#!/usr/bin/env python3
"""Reproduce the C1 interactive error ledger; see SECURITY_ACCOUNTING.md.

This program performs parameter arithmetic, not a security certification. Hash
security, Fiat-Shamir knowledge extraction, and client-proof security are
separate obligations. In particular, PoW is never added to an error exponent.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
import math
from pathlib import Path
from decimal import Decimal, ROUND_CEILING, localcontext
import hashlib


MODULUS = 2**31 - 2**24 + 1
EXTENSION_DEGREE = 5
FIELD_BITS = EXTENSION_DEGREE * math.log2(MODULUS)
NATIVE_FIELD_BITS = 155


@dataclass(frozen=True)
class Profile:
    security_bits: int
    grinding_bits: int
    log_inv_rate: int
    first_folding_factor: int
    subsequent_folding_factor: int
    rs_domain_initial_reduction_factor: int
    max_num_variables_to_send_coeffs: int


@dataclass(frozen=True)
class Event:
    layer: str
    event: str
    count: int
    single_event_bits: float
    source: str

    @property
    def error(self) -> float:
        return self.count * 2.0 ** -self.single_event_bits


def bits(error: float) -> float:
    return -math.log2(error) if error > 0 else math.inf


def list_size(rate: int, m: int) -> float:
    return m * 2.0**rate


def proximity_bits(n: int, rate: int, m: int, *, field_bits=FIELD_BITS,
                   list_agreement=True) -> float:
    """BCSS25 Theorem 4.6, or the native Theorem 1.5 selection formula.

    eta follows the native f64 computation. The list-agreement theorem uses
    ceil(sqrt(rho)/eta); ordinary correlated agreement uses half that ratio.
    """
    rho = 2.0 ** -rate
    eta = 2.0 ** (-(rate / 2 + math.log2(2 * m)))
    gamma = 1 - math.sqrt(rho) - eta
    divisor = eta if list_agreement else 2 * eta
    theorem_m = max(3, math.ceil(math.sqrt(rho) / divisor))
    a = theorem_m + 0.5
    bound = ((2 * a**5 + 3 * a * gamma * rho) * 2.0 ** (n + rate)
             / (3 * rho**1.5) + a / math.sqrt(rho))
    return field_bits - math.log2(bound)


def query_count(profile: Profile, rate: int, m: int) -> int:
    per_query = rate / 2 - math.log2(1 + 1 / (2 * m))
    return math.ceil(max(0, profile.security_bits - profile.grinding_bits) / per_query)


def select_m(profile: Profile, n: int, rate: int) -> int:
    """Mirror WhirConfig::compute_optimal_log_c_for_rate (integer-bit policy)."""
    feasible = []
    for m in range(3, 101):
        prox = proximity_bits(n, rate, m, field_bits=NATIVE_FIELD_BITS,
                              list_agreement=False)
        folding = NATIVE_FIELD_BITS - math.log2(list_size(rate, m)) - 1
        required_pow = math.ceil(max(0, profile.security_bits - min(prox, folding)))
        if required_pow > profile.grinding_bits:
            break
        feasible.append(m)
    if not feasible:
        raise ValueError(f"native profile has no feasible m at n={n}, rate={rate}")
    return min(feasible, key=lambda m: (query_count(profile, rate, m), m))


def query_density(bits_in_index: int, hash_profile: str) -> float:
    if not 0 <= bits_in_index <= 24:
        raise ValueError("queried RS domain exceeds KoalaBear two-adicity")
    if hash_profile == "keccak":
        return 1.0
    if hash_profile != "poseidon":
        raise ValueError("unknown query hash profile")
    size = 1 << bits_in_index
    return ((MODULUS + size - 1) // size) * size / MODULUS


def rs_mca_bits(length: int, dimension: int, m: int, interleaving=1) -> float:
    """BCSS25 Theorem 4.6 and CFW26 Lemma 3.15, with exact RS dimension.

    The analysis agreement is sqrt(dimension/length)*(1+1/(2m)). BCSS25
    uses the slightly reduced rate (dimension-1)/length. The interleaved
    error is at most its width times the scalar-code error.
    """
    if not 1 < dimension < length or interleaving < 1 or m < 3:
        raise ValueError("unsupported Reed-Solomon code geometry")
    with localcontext() as context:
        context.prec = 80
        rho = Decimal(dimension - 1) / length
        agreement = (Decimal(dimension) / length).sqrt() * (1 + Decimal(1) / (2 * m))
        if agreement >= 1:
            raise ValueError("analysis agreement must be below one")
        parameter = max(3, int((rho.sqrt() / (agreement - rho.sqrt()))
                               .to_integral_value(rounding=ROUND_CEILING)))
        a = Decimal(parameter) + Decimal("0.5")
        bound = ((2 * a**5 + 3 * a * (1 - agreement) * rho) * length
                 / (3 * rho * rho.sqrt()) + a / rho.sqrt()) * interleaving
        error = bound / Decimal(MODULUS**EXTENSION_DEGREE)
    # Cover floating-point conversion in the displayed accounting arithmetic.
    return bits(float(error) * (1 + 1e-12))


def whir_events(name: str, profile: Profile, n: int, hash_profile: str):
    f0 = profile.first_folding_factor
    sub = profile.subsequent_folding_factor
    threshold = profile.max_num_variables_to_send_coeffs
    reduction = profile.rs_domain_initial_reduction_factor
    if not 3 <= f0 <= 9 or not 3 <= sub <= 9 or reduction <= 0 or reduction > f0 or f0 > n:
        raise ValueError("invalid folding/reduction profile")
    rounds = math.ceil(max(0, n - f0 - threshold) / sub)
    final_variables = n - f0 - rounds * sub
    if rounds == 0 or final_variables < 0:
        raise ValueError("C1 accounting requires at least one continuation round")
    rate = profile.log_inv_rate
    domain = n + rate
    events = []
    phases = []
    previous_queries = None
    config_source = "crates/whir/src/config.rs"
    initial_list = None
    for phase in range(rounds + 1):
        fold = f0 if phase == 0 else sub
        m = select_m(profile, n, rate)
        candidates = list_size(rate, m)
        if initial_list is None:
            initial_list = candidates
        queries = query_count(profile, rate, m)
        if queries >= 400:
            raise ValueError("recursive query parser requires fewer than 400 queries per phase")
        ood = next(s for s in range(1, 64)
                   if s * NATIVE_FIELD_BITS + 1 - 2 * math.log2(candidates) - n * s
                   >= profile.security_bits)
        density = query_density(domain - fold, hash_profile)
        query_bits = queries * (rate / 2 - math.log2(1 + 1 / (2 * m)) - math.log2(density))
        prefix = f"whir.phase{phase}"
        events.extend([
            Event(name, prefix + ".list_agreement", fold,
                  rs_mca_bits(1 << (domain-fold), 1 << (n-fold), m, 1 << fold),
                  config_source + "; BCSS25 Theorem 4.6; CFW26 Lemma 3.15"),
            Event(name, prefix + ".fold_sumcheck", fold,
                  FIELD_BITS - math.log2(2 * candidates), config_source),
            Event(name, prefix + ".queries", 1, query_bits,
                  config_source + "; crates/backend/fiat-shamir/src/challenger.rs"),
            Event(name, prefix + ".ood", 1,
                  ood * FIELD_BITS + 1 - 2 * math.log2(candidates) - n * ood, config_source),
        ])
        if previous_queries is not None:
            events.append(Event(name, prefix + ".query_ood_batch", 1,
                                FIELD_BITS - math.log2(2 * (previous_queries + ood) * candidates),
                                config_source))
        phases.append(dict(variables=n, log_inv_rate=rate, folding_factor=fold, m=m,
                           queries=queries, ood_samples=ood, query_domain_bits=domain-fold,
                           query_density=density))
        previous_queries = queries
        n -= fold
        rs_reduction = reduction if phase == 0 else 1
        rate += fold - rs_reduction
        domain -= rs_reduction
    events.append(Event(name, "whir.final_coefficient_sumcheck", final_variables,
                        FIELD_BITS - 1, "crates/whir/src/verify.rs"))
    return events, phases, initial_list, final_variables


def algebraic_events(name: str, stack_variables: int, candidates: float,
                     root: bool, public_memory_variables: int):
    """Conservative dimension bounds; list-union every algebraic component.

    Each table has at most 2**stack_variables rows, and its bus count is at
    most its committed width. Therefore LogUp active slots <=2**stack_variables.
    See the document for the rational-polynomial identity and no-wrap condition.
    """
    def degree_event(label, degree, source):
        return Event(name, label, 1, FIELD_BITS - math.log2(candidates * degree), source)

    # These deliberately exceed the current table metadata, making the bound
    # insensitive to small AIR rewrites. Tests pin the intended inequalities.
    max_constraints = 1024
    max_statement_values = 1024
    max_air_degree_with_eq = 11
    bus_fingerprint_degree = 4  # ceil(log2(12 instruction columns + PC + domain))
    slots = 1 << stack_variables
    gkr_layers = max(0, stack_variables - 5)
    gkr_sumcheck_rounds = sum(range(5, stack_variables))
    result = [
        degree_event("logup.rational_identity", bus_fingerprint_degree * (slots - 1),
                     "crates/sub_protocols/src/logup.rs; rational identity derivation"),
        degree_event("logup.denominator_zero", bus_fingerprint_degree * slots,
                     "crates/sub_protocols/src/quotient_gkr/mod.rs"),
        degree_event("gkr.initial_evaluation", 2 * 5,
                     "crates/sub_protocols/src/quotient_gkr/mod.rs"),
        degree_event("gkr.layer_batching_and_line", 3 * gkr_layers,
                     "crates/sub_protocols/src/quotient_gkr/mod.rs"),
        degree_event("gkr.cubic_sumchecks", 3 * gkr_sumcheck_rounds,
                     "crates/sub_protocols/src/quotient_gkr/mod.rs"),
        degree_event("air.constraint_batching", max_constraints - 1,
                     "crates/lean_prover/src/verify_execution.rs"),
        degree_event("air.zerocheck", max_air_degree_with_eq * stack_variables,
                     "crates/lean_prover/src/verify_execution.rs"),
        degree_event("air.sumcheck", max_air_degree_with_eq * stack_variables,
                     "crates/lean_prover/src/verify_execution.rs"),
        degree_event("public_input_mle", 3,
                     "crates/lean_prover/src/verify_execution.rs"),
        degree_event("whir.statement_batching", max_statement_values - 1,
                     "crates/whir/src/verify.rs"),
    ]
    if root:
        result.extend([
            degree_event("public_memory_mle", public_memory_variables,
                         "crates/lean_prover/src/verify_execution.rs"),
            degree_event("c1.gamma_secondary_group", 2,
                         "crates/whir/src/verify.rs::verify_two_commitments"),
            degree_event("c1.lambda_cross_claims", 2,
                         "crates/whir/src/verify.rs::verify_two_commitments"),
            # Up to 63 OOD samples are supported by the native configuration.
            degree_event("c1.theta_groups", 64,
                         "crates/whir/src/verify.rs::verify_two_commitments"),
        ])
    return result


def candidate_profiles(name: str):
    if name == "no-grinding-113-111-115":
        return dict(direct=Profile(113, 0, 1, 6, 3, 6, 8),
                    lift=Profile(111, 0, 4, 5, 3, 5, 8),
                    node=Profile(115, 0, 2, 5, 3, 5, 8))
    if name == "no-grinding-113-115":
        return dict(direct=Profile(113, 0, 1, 6, 3, 6, 8),
                    lift=Profile(115, 0, 2, 5, 3, 5, 8),
                    node=Profile(115, 0, 2, 5, 3, 5, 8))
    if name == "no-grinding-112":
        return dict(direct=Profile(112, 0, 1, 6, 3, 6, 8),
                    lift=Profile(112, 0, 3, 5, 3, 5, 5),
                    node=Profile(112, 0, 3, 5, 3, 5, 5))
    raise ValueError("unknown candidate")


def account(profiles: dict[str, Profile], direct_variables: int, recursive_variables: int,
            client_bits: float, program_variables: tuple[int, int, int],
            public_memory_variables=8, *, root_variables: int | None = None):
    if not math.isfinite(client_bits) or client_bits <= 0:
        raise ValueError("client bound must be a positive finite exponent")
    if root_variables is None:
        root_variables = recursive_variables
    original_n, lift_n, node_n = program_variables
    if original_n != lift_n + 1 or lift_n != node_n:
        raise ValueError("C1 requires program dimensions [n+1, n, n]")
    if max(program_variables) > root_variables:
        raise ValueError("fixed programs do not fit the terminal polynomial")
    if sum(1 << n for n in program_variables) > 1 << root_variables:
        raise ValueError("fixed programs exceed terminal polynomial capacity")
    events = []
    layers = {}
    for name, profile, n, multiplicity, hash_profile in [
        ("direct", profiles["direct"], direct_variables, 2, "poseidon"),
        ("lift", profiles["lift"], recursive_variables, 2, "poseidon"),
        ("node", profiles["node"], root_variables, 1, "keccak"),
    ]:
        local, phases, candidates, final_variables = whir_events(name, profile, n, hash_profile)
        local += algebraic_events(name, n, candidates, name == "node", public_memory_variables)
        layers[name] = dict(profile=asdict(profile), count=multiplicity,
                            stack_variables=n, phases=phases,
                            final_coefficients=1 << final_variables,
                            interactive_accounting_bits=bits(sum(e.error for e in local)))
        events.extend(Event(e.layer, e.event, e.count * multiplicity,
                            e.single_event_bits, e.source) for e in local)
    # Two single-claim lift reductions, then two two-claim node reductions.
    for name, count, n, claims in [("lift_original", 2, original_n, 1),
                                  ("node_original", 1, original_n, 2),
                                  ("node_lift", 1, lift_n, 2)]:
        events.append(Event("bytecode", name, count,
                            FIELD_BITS - math.log2((claims - 1) + 2 * n),
                            "crates/rec_aggregation/src/bytecode_claims.rs"))
    backend_error = sum(e.error for e in events)
    events.append(Event("client", "external_security_obligation", 2, client_bits,
                        "caller-supplied client bound; requires separate justification"))
    total = sum(e.error for e in events)
    return dict(schema="leanvm-c1-security-accounting-v1", field_modulus=MODULUS,
                extension_degree=EXTENSION_DEGREE, field_bits=FIELD_BITS,
                native_field_bits=NATIVE_FIELD_BITS,
                proximity_bound="BCSS25 Theorem 4.6 (list correlated agreement)",
                proof_counts=dict(client=2, direct=2, lift=2, node=1),
                backend_interactive_accounting_bits=bits(backend_error),
                composed_interactive_accounting_bits=bits(total),
                classical_work_bits=None, quantum_work_bits=None,
                whole_chain_guarantee_established=False,
                excluded_obligations=[
                    "client bound requires its own protocol/extractor correspondence, not a configuration label",
                    "constrained WHIR state/extractor correspondence for this implementation",
                    "Fiat-Shamir/BCS reduction and recursive knowledge-extractor composition",
                    "Poseidon1/Poseidon2, Keccak and SHA-256 computational assumptions",
                    "source, generated guest, Solidity and deployed-artifact semantic equivalence",
                    "fresh WHIR constraints must have gamma powers disjoint from the carried claim",
                ],
                grinding_treatment="no amplification credited; interactive errors remain unscaled",
                generic_hash_work_bits=dict(poseidon_digest=4 * math.log2(MODULUS),
                                            keccak_240=120, sha256=128),
                layers=layers, events=[dict(**asdict(e), total_error=e.error) for e in events])


def report_dimensions(data: dict, direct: int | None, lift: int | None,
                      root: int | None) -> tuple[int, int, int]:
    """Read each proof's own stack dimension, never its child's dimension.

    An incomplete report can be screened with an explicit missing dimension;
    it cannot establish that the missing proof actually fits that dimension.
    """
    result = []
    for name, labels, supplied in (
        ("direct", {"direct_left", "direct_right"}, direct),
        ("lift", {"lift_left", "lift_right"}, lift),
        ("root", {"binary_root_c1"}, root),
    ):
        entries = [entry for entry in data.get("layers", []) if entry.get("layer") in labels]
        dimensions = {entry["stacked_num_variables"] for entry in entries}
        if len(dimensions) > 1:
            raise ValueError(f"{name} proof dimensions differ")
        if entries and ({entry["layer"] for entry in entries} != labels or len(entries) != len(labels)):
            raise ValueError(f"{name} report requires exactly the expected proof layers")
        measured = next(iter(dimensions), None)
        if supplied is not None and measured is not None and supplied != measured:
            raise ValueError(f"supplied {name} dimension differs from the report")
        value = measured if measured is not None else supplied
        if value is None:
            raise ValueError(f"report has no {name} proof dimension; supply --{name}-variables for a conditional screen")
        result.append(value)
    return tuple(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--candidate", choices=["no-grinding-112", "no-grinding-113-115",
                                               "no-grinding-113-111-115"])
    source.add_argument("--report", type=Path, help="runner report containing direct/lift/node profiles")
    client = parser.add_mutually_exclusive_group(required=True)
    client.add_argument("--client-bits", type=float,
                        help="separately justified per-client error exponent (configuration alone is insufficient)")
    client.add_argument("--client-constants", type=Path, nargs=2,
                        help="the two corrected client guest constants files; uses their conditional ledgers")
    parser.add_argument("--direct-variables", type=int,
                        help="direct stack dimension; defaults to 29 for candidates, inferred for reports")
    parser.add_argument("--lift-variables", "--recursive-variables", dest="lift_variables", type=int,
                        help="lift stack dimension; defaults to 23 for candidates, inferred for reports")
    parser.add_argument("--root-variables", type=int,
                        help="root stack dimension; defaults to lift for candidates, inferred independently for reports")
    parser.add_argument("--program-variables", type=int, nargs=3, default=[22, 21, 21])
    args = parser.parse_args()
    if args.report:
        data = json.loads(args.report.read_text())
        profiles = {key: Profile(**data["profiles"][key]) for key in ("direct", "lift", "node")}
        direct_variables, lift_variables, root_variables = report_dimensions(
            data, args.direct_variables, args.lift_variables, args.root_variables)
    else:
        profiles = candidate_profiles(args.candidate)
        direct_variables = args.direct_variables if args.direct_variables is not None else 29
        lift_variables = args.lift_variables if args.lift_variables is not None else 23
        root_variables = args.root_variables if args.root_variables is not None else lift_variables
    evidence = []
    client_bits = args.client_bits
    if args.client_constants:
        from client_security_accounting import account_client
        for path in args.client_constants:
            raw = path.read_bytes()
            item = account_client(json.loads(raw))
            evidence.append(dict(constants_sha256=hashlib.sha256(raw).hexdigest(),
                                 interactive_ledger_bits=item["client_interactive_ledger_bits"],
                                 component_bits=item["component_bits"],
                                 proof_obligations=item["proof_obligations"]))
        # account() counts two equal terms; their mean reproduces this exact sum.
        client_bits = bits(sum(2**-item["interactive_ledger_bits"] for item in evidence) / 2)
    result = account(profiles, direct_variables, lift_variables,
                     client_bits, tuple(args.program_variables), root_variables=root_variables)
    if evidence:
        result["client_evidence"] = evidence
    print(json.dumps(result, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
