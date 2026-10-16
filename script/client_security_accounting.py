#!/usr/bin/env python3
"""Client SPARK/hiding-WHIR interactive ledger from exported guest constants.

The output is conditional arithmetic, not a knowledge-soundness certification.
See SECURITY_ACCOUNTING.md for the theorem correspondence still required.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
from decimal import Decimal, ROUND_CEILING, localcontext
import hashlib
import json
import math
from pathlib import Path

from security_accounting import Event, FIELD_BITS, bits, rs_mca_bits


def query_error(length: int, dimension: int, queries: int, m: int) -> float:
    """Uniform sampling without replacement; round agreement upwards safely."""
    if not 1 < dimension < length or not 0 <= queries <= length or m < 3:
        raise ValueError("invalid code or distinct-query count")
    with localcontext() as context:
        context.prec = 80
        agreement = (Decimal(dimension) / length).sqrt() * (1 + Decimal(1) / (2 * m))
        good = int((agreement * length).to_integral_value(rounding=ROUND_CEILING))
    if good >= length:
        raise ValueError("analysis distance must be positive")
    if queries > good:
        return 0.0
    return math.prod((good - i) / (length - i) for i in range(queries)) * (1 + 1e-12)


def phase_shape(round_config: dict, randomness: int = 0) -> dict:
    fold = round_config["folding_factor"]
    length = round_config["domain_size"] >> fold
    dimension = (1 << round_config["num_variables"]) + randomness
    queries = min(round_config["num_queries"], length)
    if round_config.get("query_positions", queries) != queries:
        raise ValueError("exported query count disagrees with distinct-query sampler")
    # m is a proof-analysis choice, not a transcript parameter. Every selected
    # value gives a valid radius; optimizing this subtotal makes no protocol edit.
    m = min(range(3, 101), key=lambda value:
            query_error(length, dimension, queries, value)
            + fold * 2**-rs_mca_bits(length, dimension, value, 1 << fold))
    return dict(length=length, dimension=dimension, queries=queries, fold=fold,
                message_variables=round_config["num_variables"],
                m=m, list_bound=m * length / dimension,
                agreement=math.sqrt(dimension / length) * (1 + 1 / (2 * m)),
                query_error=query_error(length, dimension, queries, m),
                mca_bits=rs_mca_bits(length, dimension, m, 1 << fold))


def algebraic(layer: str, name: str, numerator: float, source: str, count=1):
    return Event(layer, name, count, FIELD_BITS - math.log2(numerator), source)


def append_query(events, layer, label, phase, source):
    if phase["query_error"]:
        events.append(Event(layer, label, 1, bits(phase["query_error"]), source))


def plain_events(name: str, config: dict):
    # Version entry added by the corrected plain commitment separator.
    if config["domain_separator"][:2] != [17104896, 1]:
        raise ValueError("plain WHIR constants lack the continuation version")
    rounds = config["rounds"] + [config["final_round"]]
    phases = [phase_shape(item) for item in rounds]
    events = []
    source = "Plonky3 repository: whir/src/pcs/{verifier,prover}/mod.rs"
    for index, phase in enumerate(phases):
        label = f"phase{index}"
        events.append(Event(name, label + ".mca", phase["fold"], phase["mca_bits"],
                            "BCSS25 Theorem 4.6; CFW26 Lemma 3.15"))
        events.append(algebraic(name, label + ".sumcheck", 2 * phase["list_bound"],
                                source, phase["fold"]))
        append_query(events, name, label + ".queries", phase, source)
        ood = config["commitment_ood_samples"] if index == 0 else rounds[index-1]["ood_samples"]
        variables = config["num_variables"] if index == 0 else rounds[index-1]["num_variables"]
        if ood <= 0:
            raise ValueError("plain ledger requires OOD list separation")
        events.append(Event(name, label + ".ood", 1,
                            ood * (FIELD_BITS - variables) + 1 - 2 * math.log2(phase["list_bound"]),
                            source))
        # Includes the initial evaluation claims, whose exact batch size is
        # bounded by this explicit cap for the exported SPARK layouts.
        terms = 1024 if index == 0 else phases[index-1]["queries"] + ood + 1
        events.append(algebraic(name, label + ".constraint_batching",
                                2 * terms * phase["list_bound"], source))
    events.append(algebraic(name, "final_sumcheck", 2, source,
                            config["final_sumcheck_rounds"]))
    return events, phases


def mask_shape(group: dict) -> dict:
    shape = group["shape"]
    length = shape["domain_size"]
    dimension = shape["message_len"] + shape["randomness_len"]
    m = 3
    return dict(length=length, dimension=dimension, m=m, width=group["width"],
                list_bound=m * length / dimension,
                mca_bits=rs_mca_bits(length, dimension, m, group["width"]),
                query_error=query_error(length, dimension, shape["randomness_len"], m))


def hiding_events(common: dict):
    rounds = common["rounds"] + [common["final_round"]]
    randomness = common["oracle_randomness"]
    if len(rounds) != len(randomness) or len(rounds) != len(common["folding_schedule"]):
        raise ValueError("inconsistent hiding schedule")
    phases = [phase_shape(item, r) for item, r in zip(rounds, randomness)]
    groups = common["base_case_mask_groups"]
    # This ledger maps the exported all-free-basis application/sumcheck packing.
    # Other layouts require a separate mapping of logical masks to codewords.
    if common["mask_packing"] != "all_free_basis" or any(g["width"] != 1 for g in groups):
        raise ValueError("only the selected packed mask layout is accounted")
    if len(groups) != 2 * len(rounds) + 1 or groups[:2] != common["external_mask_groups"]:
        raise ValueError("unexpected mask commitment order")
    masks = [mask_shape(group) for group in groups]
    events = []
    mask_product = math.prod(mask["list_bound"] for mask in masks[:2])
    external_list = phases[0]["list_bound"] * mask_product
    for index, phase in enumerate(phases):
        label = f"phase{index}"
        mask_index = 2 + 2 * index
        expected = common["ell_zk"] * phase["fold"]
        if groups[mask_index]["shape"]["message_len"] != expected:
            raise ValueError("sumcheck mask packing disagrees with folding count")
        mask_product *= masks[mask_index]["list_bound"]
        joint_list = phase["list_bound"] * mask_product
        events.append(algebraic("hiding", label + ".initial_combination", joint_list,
                                "CFW26 Lemma 6.5"))
        events.append(algebraic("hiding", label + ".masked_sumcheck",
                                common["ell_zk"] * joint_list, "CFW26 Lemma 6.5", phase["fold"]))
        events.append(Event("hiding", label + ".mca", phase["fold"], phase["mca_bits"],
                            "BCSS25 Theorem 4.6; CFW26 Lemma 3.15"))
        append_query(events, "hiding", label + ".source_queries", phase,
                     "CFW26 Theorems 9.6 and 7.1; pcs/utils.rs")
        if index + 1 < len(phases):
            switch_index = mask_index + 1
            switch_group = groups[switch_index]
            if switch_group["shape"] != common["switch_masks"][index]:
                raise ValueError("switch mask order differs from transcript")
            samples = rounds[index]["ood_samples"]
            if samples != 1:
                raise ValueError("private OOD accounting currently requires one sample")
            message_len = 1 << phase["message_variables"]
            if switch_group["shape"]["message_len"] != randomness[index] + samples:
                raise ValueError("private OOD mask has unexpected geometry")
            next_list = phases[index+1]["list_bound"]
            switch_list = masks[switch_index]["list_bound"]
            # The private OOD polynomial spans the message and switch-mask
            # message; its last coefficient includes the fresh pad.
            degree = message_len + switch_group["shape"]["message_len"] - 1
            events.append(algebraic("hiding", label + ".private_ood",
                                    (next_list * switch_list)**2 * degree / 2,
                                    "CFW26 Theorem 9.6; pcs/zk/code_switch.rs"))
            mask_product *= switch_list
            events.append(algebraic("hiding", label + ".switch_combination",
                                    next_list * mask_product * (phase["queries"] + samples),
                                    "CFW26 Theorem 9.6; pcs/zk/verifier/mod.rs"))
    final = phases[-1]
    source_code = common["source_code"]
    if (source_code["message_len"] + source_code["randomness_len"], source_code["domain_size"]) != (
            final["dimension"], final["length"]):
        raise ValueError("base-case code differs from final folded oracle")
    events.append(Event("hiding", "base_case.source_mca", 1,
                        rs_mca_bits(final["length"], final["dimension"], final["m"]),
                        "CFW26 Theorem 7.1"))
    events.append(algebraic("hiding", "base_case.combine", final["list_bound"] * mask_product,
                            "CFW26 Theorem 7.1"))
    for index, mask in enumerate(masks):
        events.append(Event("hiding", f"base_case.mask{index}.mca", 1, mask["mca_bits"],
                            "CFW26 Theorem 7.1; heterogeneous masks union bound"))
        append_query(events, "hiding", f"base_case.mask{index}.queries", mask,
                     "CFW26 Theorem 7.1; pcs/zk/base_case/verifier.rs")
    return events, phases, masks, external_list


def account_client(constants: dict):
    events, hiding, masks, external_list = hiding_events(constants["common"])
    plain = {}
    metadata = constants["table_metadata"]
    configs = [("fixed_value", constants["fixed_value_whir"])]
    embedded = 2 * max(metadata["row_memory_size"], metadata["col_memory_size"]) <= metadata["value_domain_size"]
    if not embedded:
        configs.append(("fixed_audit", constants["fixed_audit_whir"]))
    configs.extend((f"read{index}", config) for index, config in enumerate(constants["read_whir"]))
    for name, config in configs:
        local, phases = plain_events(name, config)
        events.extend(local)
        plain[name] = phases
    common = constants["common"]
    local_spartan = 15 * common["num_outer_rounds"] + max(2, common["ell_zk"] - 1) * common["num_inner_rounds"] + 4
    ops = metadata["value_domain_size"].bit_length() - 1
    memory = max(metadata["row_memory_size"], metadata["col_memory_size"]).bit_length() - 1
    tuple_terms = 2 * (2 * metadata["value_domain_size"] + metadata["row_memory_size"] + metadata["col_memory_size"])
    product_rounds = ops * (ops - 1) // 2 + memory * (memory - 1) // 2
    spark_terms = tuple_terms + 3 * product_rounds + 2 * (ops + memory) + 6 * 5 + 8
    # Both application masks are fixed when the client IOP challenges use them.
    # OOD separation fixes the plain SPARK candidates before product challenges.
    events.append(algebraic("spartan_spark", "iop", external_list * (local_spartan + spark_terms),
                            "spartan-whir/src/security.rs; local committed-list union"))
    totals = {name: bits(sum(e.error for e in events if e.layer == name))
              for name in sorted({e.layer for e in events})}
    return dict(schema="spartan-client-security-accounting-v1", field_bits=FIELD_BITS,
                client_interactive_ledger_bits=bits(sum(e.error for e in events)),
                whole_client_guarantee_established=False, grinding_amplification_credited=0,
                classical_work_bits=None, fixed_audit_embedded=embedded,
                component_bits=totals, hiding_phases=hiding, mask_codes=masks,
                plain_phases=plain,
                proof_obligations=[
                    "CFW26 relaxed relation/extractor correspondence for packed heterogeneous mask codes",
                    "client Spartan/SPARK committed-list state and extraction correspondence",
                    "BCS/Fiat-Shamir compilation and cryptographic assumptions",
                    "exact generated guest and final verifier authenticate this corrected protocol",
                ], events=[dict(**asdict(event), total_error=event.error) for event in events])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("constants", type=Path)
    args = parser.parse_args()
    raw = args.constants.read_bytes()
    result = account_client(json.loads(raw))
    result["constants_sha256"] = hashlib.sha256(raw).hexdigest()
    print(json.dumps(result, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
