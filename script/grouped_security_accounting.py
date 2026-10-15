#!/usr/bin/env python3
"""Conditional classical error accounting for the selected grouped chain.

The output is a coefficient for a conditional knowledge-soundness reduction,
not a demonstrated attack cost or a whole-chain security certification.
See SECURITY_ACCOUNTING.md for the hypotheses and transcript correspondence.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, ROUND_CEILING, localcontext
import hashlib
import json
import math
from pathlib import Path

import client_security_accounting as client
import security_accounting as sa


ROOT = Path(__file__).resolve().parents[1]
RUN = ROOT / "benchmark-results/2026-10-15-poseidon-grinding-fresh"
P = sa.MODULUS
Q = P**5
RADIUS_GRID = [x / 4 for x in range(5, 12)] + list(range(3, 1001))
SOURCES = [
    "script/security_accounting.py",
    "script/client_security_accounting.py",
    "script/grouped_security_accounting.py",
    "crates/whir/src/config.rs",
    "crates/whir/src/verify.rs",
    "crates/backend/fiat-shamir/src/challenger.rs",
    "crates/backend/fiat-shamir/src/prover.rs",
    "crates/backend/fiat-shamir/src/verifier.rs",
    "crates/rec_aggregation/zkdsl_implem/fiat_shamir.py",
    "crates/lean_prover/python-verifier/verifier.py",
    "crates/lean_prover/src/grouped_execution.rs",
    "crates/sub_protocols/src/grouped_logup.rs",
    "crates/sub_protocols/src/grouped_logup/air.rs",
    "crates/sub_protocols/src/grouped_logup/pcs.rs",
    "crates/rec_aggregation/src/binary_recursion.rs",
    "crates/rec_aggregation/src/bytecode_claims.rs",
    "crates/rec_aggregation/src/compilation.rs",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def query_joint_bound(p: int, domain: int, good: int, queries: int, work: int) -> float:
    """Maximum over fixed agreement sets; includes Poseidon's work check.

    A fresh duplex separates the checked word from every query. For
    p=K*domain+1, residue zero has K+1 preimages and every other residue
    has K preimages. The work check retains its canonical-field bias.
    """
    if (domain < 2 or domain & (domain - 1) or p % domain != 1
            or not 1 <= good <= domain or queries < 1 or work < 0):
        raise ValueError("unsupported query distribution")
    k = p // domain
    mass = (good * k + 1) / p
    passing = ((p - 1) // (1 << work) + 1) / p
    return passing * mass**queries


def query_event(b: int, queries: int, work: int, m: float,
                rate: int, hash_profile: str) -> dict:
    domain = 1 << b
    with localcontext() as context:
        context.prec = 80
        agreement = (Decimal(2) ** (-Decimal(rate) / 2)
                     * (1 + Decimal(1) / (2 * Decimal(str(m)))))
        good = int((agreement * domain).to_integral_value(rounding=ROUND_CEILING))
    if not 1 <= good < domain:
        raise ValueError("analysis radius must give a positive distance")
    if hash_profile == "keccak":
        passing = 2.0**-work
        mass = good / domain
        joint = passing * mass**queries
        support = domain
    elif hash_profile == "poseidon":
        passing = ((P - 1) // (1 << work) + 1) / P
        mass = (good * (P // domain) + 1) / P
        joint = query_joint_bound(P, domain, good, queries, work)
        support = domain
    else:
        raise ValueError("unknown transcript")
    return dict(agreement_positions=good, domain=domain,
                first_query_support=support, ordinary_agreement_mass=mass,
                pow_pass_probability=passing, pow_work_bits=sa.bits(passing),
                query_joint_error=joint, query_joint_bits=sa.bits(joint),
                conditional_query_bits=sa.bits(joint / passing))


def mca_error(length: int, dimension: int, m: float, width: int) -> float:
    """BCSS25 Thm4.6 and CFW26 Lemma3.15, allowing analysis-only radii."""
    if not 1 < dimension < length or m <= 0 or width < 1:
        raise ValueError("invalid code geometry")
    with localcontext() as context:
        context.prec = 80
        rho = Decimal(dimension - 1) / length
        agreement = ((Decimal(dimension) / length).sqrt()
                     * (1 + Decimal(1) / (2 * Decimal(str(m)))))
        if agreement >= 1:
            raise ValueError("analysis radius must give a positive distance")
        parameter = max(3, int((rho.sqrt() / (agreement - rho.sqrt()))
                               .to_integral_value(rounding=ROUND_CEILING)))
        a = Decimal(parameter) + Decimal("0.5")
        numerator = ((2 * a**5 + 3 * a * (1 - agreement) * rho) * length
                     / (3 * rho * rho.sqrt()) + a / rho.sqrt()) * width
        return float(numerator / Decimal(Q)) * (1 + 1e-12)


def native_schedule(profile: sa.Profile, phases: list[dict], final: int) -> dict:
    """Mirror the native integer-155 selection, independently of analysis m."""
    query_pows, folding_pows = [], []
    for index, phase in enumerate(phases):
        n, rate, m = phase["variables"], phase["log_inv_rate"], phase["m"]
        prox = sa.proximity_bits(n, rate, m, field_bits=sa.NATIVE_FIELD_BITS,
                                 list_agreement=False)
        folding = sa.NATIVE_FIELD_BITS - math.log2(sa.list_size(rate, m)) - 1
        folding_pows.append(math.ceil(max(0, profile.security_bits - min(prox, folding))))
        query_bits = phase["queries"] * (rate / 2 - math.log2(1 + 1 / (2 * m)))
        if index + 1 < len(phases):
            nxt = phases[index + 1]
            combination_bits = sa.NATIVE_FIELD_BITS - math.log2(
                2 * (phase["queries"] + nxt["ood_samples"])
                * sa.list_size(nxt["log_inv_rate"], nxt["m"]))
            query_bits = min(query_bits, combination_bits)
        query_pows.append(math.ceil(max(0, profile.security_bits - query_bits)))
    return dict(queries=[p["queries"] for p in phases], query_pows=query_pows,
                folding_pows=folding_pows, ood=[p["ood_samples"] for p in phases],
                final_variables=final)


def phase_events(phase: dict, schedule: dict, index: int,
                 m: float, hash_profile: str) -> dict:
    n, rate, fold = phase["variables"], phase["log_inv_rate"], phase["folding_factor"]
    work = schedule["query_pows"][index]
    folding_work = schedule["folding_pows"][index]
    candidates = sa.list_size(rate, m)
    query = query_event(phase["query_domain_bits"], phase["queries"], work,
                        m, rate, hash_profile)
    # Positive Poseidon checks duplex before the folding challenge. Keccak
    # consumes a separate checked word. Zero work contributes factor one.
    scale = (2.0**-folding_work if hash_profile == "keccak"
             else ((P - 1) // (1 << folding_work) + 1) / P)
    mca = mca_error(1 << phase["query_domain_bits"], 1 << (n - fold), m, 1 << fold)
    folding = scale * (mca + 2 * candidates / Q)
    ood = candidates**2 * (2**n / Q)**phase["ood_samples"] / 2
    return dict(phase=index, variables=n, log_inv_rate=rate, fold=fold,
                native_m=phase["m"], analysis_m=m, list_bound=candidates,
                queries=phase["queries"], query_pow=work, folding_pow=folding_work,
                query_domain_bits=phase["query_domain_bits"], **query,
                folding_mca_joint_error=scale * mca,
                folding_sumcheck_joint_error=scale * 2 * candidates / Q,
                folding_transition_error=folding, ood_error=ood,
                continuation_combination_error=0.0,
                transition_error=max(folding, query["query_joint_error"], ood))


def grouped_events(m: float, n: int = 23, rate: int = 6, fold: int = 5) -> dict:
    """Degree-two three-polynomial lifting plus conservative grouped algebra.

    One joint list applies after helper commitment. The fixed codeword adds
    no list factor. Before lookup challenges, use the execution-only list.
    Capacity bounds cover every table layout fitting this root dimension.
    """
    candidates = sa.list_size(rate, m)
    lifting = 2 * mca_error(1 << (n + rate - fold), 1 << (n - fold), m, 1 << fold)
    degrees = {
        "lookup_rational_identity": 4 * ((1 << n) - 1),
        "constraint_batch_zerocheck_balance": n + 148 + 1,
        "air_sumcheck_union": 11 * n,
        "public_input_and_memory": 3 + 8,
        "initial_group_claim_batch": 201,
        "three_polynomial_cross_consistency": 2,
        "ood_and_three_groups_batch": 3,
    }
    algebra = {name: candidates * degree / Q for name, degree in degrees.items()}
    # Include all other algebra conservatively as one subtotal. Four work bits
    # protect lambda's curve lifting; they are not applied to unrelated terms.
    total = lifting / 16 + sum(algebra.values())
    return dict(list_bound=candidates, curve_degree=2, batching_pow=4,
                curve_lifting_interactive_error=lifting,
                curve_lifting_joint_error=lifting / 16,
                algebra_degrees=degrees, algebra_errors=algebra,
                algebra_union_bits=sa.bits(sum(algebra.values())),
                transition_upper_bound=total, transition_upper_bound_bits=sa.bits(total))


def layer_account(name: str, profile: sa.Profile, n: int) -> dict:
    hash_profile = "keccak" if name == "node" else "poseidon"
    _, phases, _, final = sa.whir_events(name, profile, n, hash_profile)
    schedule = native_schedule(profile, phases, final)
    cases = {}
    for case in ["native_radius", "optimized_radius"]:
        rows = []
        for index, phase in enumerate(phases):
            grid = [phase["m"]] if case == "native_radius" else RADIUS_GRID
            choices = [phase_events(phase, schedule, index, m, hash_profile) for m in grid]
            # A finite per-phase search; the tiny cross-phase combination is
            # evaluated afterwards and included in the reported coefficient.
            rows.append(min(choices, key=lambda row: row["transition_error"]))
        for index, row in enumerate(rows):
            if index + 1 < len(rows):
                nxt = rows[index + 1]
                degree = row["queries"] + schedule["ood"][index + 1]
                row["continuation_combination_error"] = (
                    row["pow_pass_probability"] * 2 * degree * nxt["list_bound"] / Q)
            shift = row["query_joint_error"] + row["continuation_combination_error"]
            row["shift_transition_error"] = shift
            row["transition_error"] = max(row["folding_transition_error"], shift, row["ood_error"])
            row["transition_bits"] = sa.bits(row["transition_error"])
            row["folding_transition_bits"] = sa.bits(row["folding_transition_error"])
            row["shift_transition_bits"] = sa.bits(shift)
        initial_list = rows[0]["list_bound"]
        if name == "node":
            extra = grouped_events(rows[0]["analysis_m"], n)
            algebra = extra["transition_upper_bound"]
        else:
            events = sa.algebraic_events(name, n, initial_list, False, 8)
            algebra = sum(event.error for event in events)
            extra = dict(algebra_errors={event.event: event.error for event in events},
                         algebra_union_bits=sa.bits(algebra))
        coefficient = max(algebra, 2 * final / Q, *(r["transition_error"] for r in rows))
        event_sum = algebra + 2 * final / Q + sum(
            r["fold"] * r["folding_transition_error"]
            + r["shift_transition_error"] + r["ood_error"] for r in rows)
        cases[case] = dict(phases=rows, reductions=extra,
                           conditional_coefficient=coefficient,
                           conditional_coefficient_bits=sa.bits(coefficient),
                           event_union_diagnostic_bits=sa.bits(event_sum))
    return dict(profile=profile.__dict__, dimension=n, transcript=hash_profile,
                native_schedule=schedule, **cases)


def account(report_path: Path, constants_paths: list[Path]) -> dict:
    report = json.loads(report_path.read_text())
    profiles = report["profiles"]
    if not (report["complete"] and report["node_arity"] == 2
            and profiles["terminal_grouped_logup"] and profiles["terminal_keccak"]):
        raise ValueError("requires a complete two-client grouped terminal report")
    if len(report["layers"]) != 5:
        raise ValueError("requires exactly two direct proofs, two lifts and one root")
    dimensions = {}
    for name, labels in [("direct", ["direct_left", "direct_right"]),
                         ("lift", ["lift_left", "lift_right"]),
                         ("node", ["binary_root_grouped_logup"])]:
        matching = [row for row in report["layers"] if row["layer"] in labels]
        values = [row["stacked_num_variables"] for row in matching]
        if sorted(row["layer"] for row in matching) != sorted(labels) or len(set(values)) != 1:
            raise ValueError("missing or unequal proof dimensions")
        program_log = 18 if name == "direct" else 17
        if any(row["bytecode_padded_instructions"] != 1 << program_log for row in matching):
            raise ValueError("bytecode reductions require program dimensions 22/21/21")
        dimensions[name] = values[0]
    if dimensions != dict(direct=29, lift=23, node=23):
        raise ValueError("grouped geometry correspondence covers dimensions 29/23/23")
    if (profiles["lift_child_num_variables"] != dimensions["direct"]
            or profiles["node_child_num_variables"] != dimensions["lift"]):
        raise ValueError("compiled child dimensions disagree with the proof report")
    layers = {name: layer_account(name, sa.Profile(**profiles[name]), dimensions[name])
              for name in dimensions}
    if layers["node"]["profile"] != sa.Profile(100, 28, 6, 5, 4, 1, 6).__dict__:
        raise ValueError("grouped argument requires the selected terminal profile")
    if len(constants_paths) != 2:
        raise ValueError("two client constants files are required")
    clients = []
    for path in constants_paths:
        result = client.account_client(json.loads(path.read_text()))
        clients.append(dict(constants_sha256=digest(path),
                            coefficient=2.0**-result["client_interactive_ledger_bits"],
                            coefficient_bits=result["client_interactive_ledger_bits"],
                            component_bits=result["component_bits"],
                            grinding_credit=0))
    bytecode = sum((claims - 1 + 2 * n) / Q for claims, n in [(1, 22), (1, 22), (2, 22), (2, 21)])
    tree = {}
    for case in ["native_radius", "optimized_radius"]:
        error = (sum(row["coefficient"] for row in clients) + bytecode
                 + sum((1 if name == "node" else 2) * row[case]["conditional_coefficient"]
                       for name, row in layers.items()))
        tree[case] = dict(coefficient=error, coefficient_bits=sa.bits(error))
    return dict(
        schema="leanvm-grouped-classical-accounting-v1", date="2026-10-15",
        scope="Two client proofs, two direct proofs, two lifts, one grouped root; terminal Merkle collision term excluded",
        field_cardinality=str(Q), field_bits=sa.FIELD_BITS,
        analysis_grid=RADIUS_GRID,
        optimizer_claim="finite per-phase search; no claim of global optimum or tightest available theorem",
        interpretation="Conditional coefficient in Pr[false statement accepted] <= Qstar*coefficient + HashOther(Qstar); not an attack cost",
        whole_chain_guarantee_established=False,
        terminal_merkle_collision_term="excluded by request; commitment binding assumed",
        classical_security_bits_certified=None,
        conditional_hypotheses=[
            "Ideal transcript output after the fresh post-grinding Poseidon duplex, with canonical field/index distributions",
            "Each accepted work prefix fixes one continuation gamma or lambda input; fresh retries require another passing prefix",
            "WHIR mutual correlated agreement and constrained candidate/extractor correspondence",
            "Grouped same-set lifting, adaptive-helper trace reconstruction, and authenticated fixed program",
            "Client packed-mask/code-switch and Spartan/SPARK round-by-round knowledge correspondence",
            "Compatible same-oracle straight-line recursive extraction; all extraction queries counted in Qstar",
            "Other transcript, commitment, relation and application hash assumptions, represented by HashOther",
        ],
        report_sha256=digest(report_path),
        source_sha256={name: digest(ROOT / name) for name in SOURCES},
        clients=clients, layers=layers, bytecode_reduction_error=bytecode,
        tree_composition=tree)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=RUN / "terminal/report.json")
    parser.add_argument("--client-constants", type=Path, nargs=2,
                        default=[RUN / f"client/fixture-{i}/full_zk_spark_guest_constants.json" for i in range(2)])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = account(args.report, args.client_constants)
    raw = json.dumps(result, indent=2, allow_nan=False) + "\n"
    if args.output:
        args.output.write_text(raw)
    else:
        print(raw, end="")


if __name__ == "__main__":
    main()
