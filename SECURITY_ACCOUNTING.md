# Recursive verification security accounting

Current analysis: October 15, 2026. The selected backend uses the 100-bit security parameter with grinding budgets of 22 bits for direct proofs, 24 bits for lifts, and 28 bits for the terminal proof. The client keeps its separate 116-bit configuration. The analysis below retains those parameters and the measured 10,666,368 gas transaction. It excludes the terminal Solidity Merkle collision term, assuming binding for that commitment.

`script/grouped_security_accounting.py` calculates a conservative classical error coefficient for two client proofs, two direct execution proofs, two lifts, and one grouped root. With analysis radii chosen from a finite grid, the coefficient is **9.8639371e-30 = 2^-96.355679**. This calculation does not certify a 100-bit chain or demonstrate a forgery at approximately 96 bits of work. It is conditional on the knowledge-extraction and oracle assumptions stated below; its output keeps `whole_chain_guarantee_established: false` and `classical_security_bits_certified: null`.

The calculation includes the actual grinding schedules and fresh query distributions, grouped helper constraints, three-polynomial batching, fixed-program reductions, and proof multiplicities. The [grouped derivation](GROUPED_SECURITY_DERIVATION.md) supplies the joint-list argument and statement/challenge tables. The composed bound includes material contributions from direct, lift and root proofs. Stronger constrained-code arguments may improve the bound; the finite radius search and conservative list correlated agreement constants are not claimed optimal.

## Reproduction

Run from the LeanVM repository root. The default inputs are the freshly verified selected chain and its two client constants files:

```sh
python3 script/grouped_security_accounting.py
python3 script/client_security_accounting.py benchmark-results/2026-10-15-poseidon-grinding-fresh/client/fixture-0/full_zk_spark_guest_constants.json
python3 -m unittest discover -s script -p 'test*security_accounting.py'
```

`--report`, `--client-constants LEFT RIGHT`, and `--output PATH` allow explicit input and output locations. The JSON records source/input hashes, per-phase native schedules, selected analysis radii, individual events, grouped additions, and tree composition. The [current chain report](benchmark-results/2026-10-15-poseidon-grinding-fresh/terminal/report.json) records all five LeanVM verifications at dimensions 29/23/23. The analysis rejects other dimensions, missing/duplicated children, and a different fixed-program geometry. The generated recursive verifiers enforce their configured child dimensions before commitment parsing; the selected final verifier fixes the root geometry.

`script/security_accounting.py` remains an ordinary two-commitment C1 interactive diagnostic. Its unscaled event union deliberately omits grinding amplification and does not represent the selected grouped chain. A client configuration requesting 116 bits likewise supplies no independent proof of a 116-bit composed bound; the current client contribution is calculated from its actual exported constants.

The calculator uses `q = 2130706433^5`, so `log2(q) = 154.943423437...`. Native WHIR parameter selection uses the integer 155. The calculator reproduces that selection policy, including its floating-point rounding, then evaluates error terms using the actual field cardinality.

## Selected parameters

The selected profile is [terminal_grouped.json](crates/spartan_whir_guest/profiles/terminal_grouped.json). It uses the original backend parameters below and the grouped terminal. [terminal_c1.json](crates/spartan_whir_guest/profiles/terminal_c1.json) retains the ordinary-C1 fallback with the same 100-bit parameters. The archived ordinary-C1 parameters are recorded in `benchmark-results/terminal-c1-b-threshold6-pow28/report.json` and `benchmark-results/2026-10-14-recursion-soundness/terminal-control/report.json`.

| Layer | Security parameter | Grinding budget | Inverse-rate logarithm | First/subsequent fold | Initial RS reduction | Final-variable threshold |
| --- | ---: | ---: | ---: | --- | ---: | ---: |
| Direct | 100 | 22 | 1 | 6 / 4 | 2 | 5 |
| Lift | 100 | 24 | 4 | 5 / 4 | 1 | 3 |
| Terminal | 100 | 28 | 6 | 5 / 4 | 1 | 6 |

`WhirConfig::new` uses the grinding budget when choosing query counts and derives the actual query and folding work requirements for each phase. The budget is not a uniform extra exponent for every proof component. Ordinary C1 also has a separate two-bit polynomial batching check; the grouped terminal uses `GROUPED_BATCHING_POW_BITS = 4` for its three-commitment batch.

### Calculated coefficients and composition

Each exponent below is the negative base-two logarithm of a conditional error coefficient. Errors that occur at the same challenge are added. For each LeanVM proof, the calculator then takes the maximum across transitions, conservatively using an algebraic subtotal where finer separation is unnecessary. The client retains its larger existing event-union coefficient and receives no grinding credit.

| Component | Multiplicity | Conditional coefficient exponent |
| --- | ---: | ---: |
| Client Spartan/SPARK and hiding/plain WHIR | 2 | 104.647 |
| Direct execution | 2 | 98.662 |
| Lift | 2 | 99.063 |
| Grouped terminal, including its extra reductions | 1 | 98.177 |
| Complete tree coefficient | — | **96.356** |

The grouped additions alone give 103.567 bits, including the separate four-bit lambda work check. Their algebraic subtotal is 121.621 bits using the root's capacity bounds. The shared WHIR component dominates the root.

Let the component coefficients be `eC,eD,eL,eG`, and let `eBC` be the four fixed-program reduction errors. The conservative tree coefficient is `E=2eC+2eD+2eL+eG+eBC`. Under the explicit extraction hypotheses below, the classical formula is `Pr[false acceptance] <= Qstar*E + HashOther(Qstar)`. `Qstar` includes adversarial and additional extraction/verification oracle queries. `HashOther` contains the computational terms other than the specifically excluded terminal Merkle term. The exponent 96.356 describes `1/E`; the formula does not construct an attack.

[WHIR Theorems 5.2 and 5.6](https://eprint.iacr.org/2024/1586) add mutual-correlated-agreement and algebraic terms within transitions. [SWIRL Theorem 4.2.5 and Corollary 4.2.6](https://openvm.dev/swirl.pdf) explain the maximum over transitions and its classical oracle-query scaling. Neither justifies dropping proof multiplicities from this recursive tree. Doing so would require a joint extractor that partitions a single query budget across every recovered proof.

### Actual work schedules

| Layer | Queries by phase | Query work bits | Folding work bits |
| --- | --- | --- | --- |
| Direct | 159, 32, 20, 15, 12, 10 | 22, 22, 22, 21, 19, 18 | 8, 0, 0, 0, 0, 3 |
| Lift | 39, 20, 14, 11, 9 | 24, 24, 24, 24, 24 | 0, 0, 3, 5, 12 |
| Root | 25, 15, 12, 10 | 28, 28, 25, 23 | 0, 0, 0, 4 |

These schedules were independently checked against `WhirConfig::new`. The analysis changes only its proximity radii: direct uses `m=[47,8,5,2.5,2,2]`, lift `[11,4,5,4,189]`, and root `[5,2.5,1.75,1.5]`. The grid contains quarter steps from 1.25 through 2.75 and integers from 3 through 1000. The theorem's integer parameter is recomputed from the actual scalar-code dimension and is always at least three. Every chosen radius supplies a valid arithmetic bound; this finite per-phase search is not a proof of global optimality.

### Exact grinding contribution

For Poseidon, write `Cw=floor((p-1)/2^w)+1` and `aw=Cw/p`. Each successful positive work check performs a fresh duplex before subsequent sampling. In the ideal-transcript model, the work event and the new query or folding samples are independent. For a query domain `H=2^b`, write `p=KH+1`, let `A` bound the agreement-set size, and put `v=(KA+1)/p`. The maximum joint probability over a fixed agreement set is `aw*v^t`. Every query, including the first, has full domain support. Keccak consumes its checked word and retains `2^-w*(A/H)^t`.

The calculator rounds `A=ceil(H*sqrt(rho)*(1+1/(2m)))` upward with high-precision arithmetic and includes canonical-field sampling bias. For a Poseidon folding challenge, a fixed exceptional set `B` has joint probability at most `aw*|B|/q` under the same fresh-output hypothesis. The calculator applies that work factor to both mutual correlated agreement and the scalar sumcheck term. A zero-bit check has `aw=1` and leaves the transcript unchanged.

Continuation gamma and initial lambda follow an explicit duplex. Their work credit also requires the argument from transcript order: every passing work prefix fixes one subsequent challenge input; fresh retries require another passing work prefix. Merkle-derived answers are fixed by previously binding roots and indices. Independent output words alone would not justify a work factor if the prover could insert arbitrary fresh transcript messages after a passing nonce. The selected ordering supplies no such free message. Transcript/capacity collisions remain part of `HashOther`.

The finite-radius calculation still falls below 100 bits after composing the seven proofs. Its remaining loss comes from conservative correlated-agreement bounds, analysis radii, and proof multiplicities. Establishing a stronger coefficient requires a tighter justified reduction or different parameters; this transcript correction keeps all runtime parameters unchanged.

## Error events

### WHIR

For each phase, let `n` be its polynomial-variable count, `r` its inverse-rate logarithm, `rho = 2^-r`, and `eta = sqrt(rho)/(2m)`. The Johnson list bound is `L = m*2^r`. Source anchors are `crates/whir/src/config.rs`, `crates/whir/src/verify.rs`, and `crates/backend/fiat-shamir/src/challenger.rs`. The table lists the interactive ingredients before grinding; the selected classical calculation substitutes the exact query distribution above and applies each work check only to its protected events.

| Event | Count | Bound |
| --- | --- | --- |
| List correlated agreement | Each folding challenge | Exceptional-set bound / `q` |
| Folding sumcheck | Each folding challenge | `2L/q` |
| Query consistency | Each phase | `[sqrt(rho)+eta]^t * beta^t` |
| OOD list separation | Initial commitment and each continuation phase | `L^2 * (2^n/q)^s / 2` |
| Query/OOD constraint combination | Each continuation | `2(t_previous+s)L/q` |
| Final coefficient sumcheck | Each remaining variable | `2/q` |

The exceptional-set calculation uses list correlated agreement in [BCSS25, Theorem 4.6](https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf), with theorem parameter `ceil(sqrt(rho)/eta)`. The native parameter selector cites ordinary correlated agreement in Theorem 1.5, whose parameter is `ceil(sqrt(rho)/(2eta))`. Applying the stronger list statement throughout the ledger is conservative; establishing the precise constrained-WHIR reduction remains necessary.

For the actual event bound, a scalar Reed–Solomon code with dimension `D` and block length `H` uses the theorem's reduced rate `(D-1)/H`. The chosen agreement remains `sqrt(D/H)*(1+1/(2m))`; the theorem parameter is recomputed from those values. An interleaved code of width `K` costs at most `K` times the scalar mutual-correlated-agreement error by CFW26 Lemma 3.15. Each folding challenge is conservatively charged the whole initial width of its folding batch. The integer-bit native selector remains unchanged.

For a Poseidon query index with `b` bits, `beta = ceil(p/2^b)*2^b/p`, where `p = 2130706433`. This bounds the maximum probability density relative to a uniform index. Multiplying the query event by `beta^t` covers sampling with replacement and the implementation's low-bit bias. Keccak indices use masked uniform 32-bit samples, giving `beta = 1`. Keccak extension-field samples use rejection sampling. Poseidon extension-field uniformity is part of the ideal-transcript assumption.

### AIR, LogUp, GKR, and public memory

The ordinary-C1 calculator unions each algebraic event over the initial Johnson list. The selected direct/lift calculation reuses those conservative algebraic terms. The grouped root instead uses the helper and shared-list reductions in [GROUPED_SECURITY_DERIVATION.md](GROUPED_SECURITY_DERIVATION.md); it has no quotient-GKR term. The dimension bounds cover all traces admitted by the stated stack dimension. Each table's bus count is at most its committed width, so the number of active LogUp denominator slots is at most the stack length `N = 2^n`.

| Component | Degree numerator charged before division by `q` and multiplication by `L` | Source |
| --- | --- | --- |
| LogUp rational identity | `4(N-1)` | `crates/sub_protocols/src/logup.rs` |
| Zero denominators | `4N` | `crates/sub_protocols/src/quotient_gkr/mod.rs` |
| GKR initial evaluations | 10 | Same |
| GKR batching and two-point reduction | `3(n-5)` | Same |
| GKR cubic sumchecks | `3*sum(5..n-1)` | Same |
| AIR constraint batching | 1023 | `crates/lean_prover/src/verify_execution.rs` |
| AIR random evaluation and AIR sumcheck | `11n` each | Same |
| Public input evaluation | 3 | Same |
| Terminal public region evaluation | 8 | Same |
| Initial WHIR statement batching | 1023 | `crates/whir/src/verify.rs` |

The batching ceilings deliberately exceed the current 145 AIR constraints and 253 ordinary WHIR statement values. The ordinary-C1 table metadata is execution `(degree 5, width 20, buses 5)`, extension operations `(degree 6, width 29, buses 16)`, and Poseidon16 `(degree 10, width 110, buses 33)`. The extra equality polynomial makes the maximum AIR sumcheck degree eleven. Changes exceeding these ceilings require an accounting update.

#### LogUp rational identity

The fingerprint is a multilinear evaluation in four challenge variables: twelve instruction columns, the program counter, and the domain separator fit in sixteen coordinates. Distinct padded tuples define distinct fingerprint polynomials. Over the rational-function field in those challenges, a nonzero multiset imbalance gives a nonzero rational sum `sum_i m_i/(c-f_i)`: its residue at a distinct pole is the nonzero multiplicity. Multiplying by the distinct denominator factors gives a nonzero polynomial of total degree at most `4(N-1)`. Schwartz–Zippel gives the charged bound without requiring a union over every pair of tuples. The additional `4N/q` term conservatively covers undefined denominators.

This argument establishes equality of multiplicities in the base field. Recovering integer memory and bytecode semantics also requires the enforced table limits to keep total lookup counts below the base-field characteristic. `crates/lean_vm/src/core/constants.rs::ensure_no_overflow_in_logup` checks that invariant. A native or recursive verifier must reject zero final GKR denominators before relying on the rational identity.

### Bytecode reductions

There are four reductions: two single-claim reductions over the original guest, one two-claim reduction over the original guest, and one two-claim reduction over the lift program. A reduction of `k` claims for an `n`-variable fixed program costs at most `[(k-1)+2n]/q`: powers-of-alpha batching followed by `n` quadratic sumcheck rounds. The endpoint is authenticated through the fixed program. See `crates/rec_aggregation/src/bytecode_claims.rs` and `crates/rec_aggregation/src/binary_recursion.rs`.

### C1 with an authenticated fixed program

Let `f` be the execution oracle and `g` the authenticated fixed-program codeword. For every `lambda`, adding `lambda*g` translates the Reed–Solomon code, so `List(f+lambda*g) = List(f)+lambda*g`. The candidate list for `f` is fixed before the grouping challenge, cross evaluations, and `lambda`. This identity requires the secondary commitment to authenticate the known, correctly encoded polynomial.

The three program dimensions must have the supported layout `[n+1,n,n]`. Their concatenation occupies `2^(n+2)` entries. A larger root polynomial may contain that concatenation followed by zeros. In multilinear coordinates, its evaluation is `g_padded(z,x) = product_i(1-z_i)*g(x)`, where `z` contains the added leading coordinates. The authenticated program statements fix those coordinates to zero, preserving their original evaluations. Deterministic zero padding adds no probabilistic error. The WHIR and execution terms use the full padded root dimension; the four bytecode reductions retain their original program dimensions. The calculator checks that the concatenation fits the root, while native and final verifiers must authenticate the same padding, selector prefixes, commitment, and root dimension.

Write the primary and secondary grouped functionals as `A` and `B`, their claims as `a` and `b`, and the prover's cross claims as `u` and `v`. For a candidate `h` in the primary list, the two combined residuals are `A(h)-a + lambda*(A(g)-u)` and `B(h)-v + lambda*(B(g)-b)`. If either original grouped claim is false, at least one residual is a nonzero affine polynomial. Since the cross claims precede `lambda`, the ledger charges `2L/q` for this step. It separately charges gamma batching of the primary claims, two secondary-group powers, and theta batching of OOD answers and both groups. The implementation anchor is `WhirConfig::verify_two_commitments` in `crates/whir/src/verify.rs`.

## Client proof accounting

`script/client_security_accounting.py` reads the exported client constants, checks the corrected plain-WHIR version entry, and inventories the actual hiding and plain code dimensions. The corrected withdrawal fixture gives a conditional interactive ledger of approximately 104.647 bits per client. Its components are hiding WHIR 105.597, fixed-value WHIR 106.916, first read WHIR 106.916, second read WHIR 108.539, and the Spartan/SPARK algebraic checks 118.114 bits. These figures describe the unscaled interactive client ledger and retain the proof obligations below. The client configuration remains 116 with its existing grinding schedule.

### Code dimensions and queries

An interleaved hiding oracle has scalar-code dimension `D = message_length + randomness_length`. For this fixture the three scalar codes have `(H,D)` equal to `(8192,4364)`, `(2048,636)`, and `(1024,188)`. Their query counts are 268, 124, and 124. Nominal message-only rates would omit the random coefficients and overstate the query bound.

The client sampler in pinned `whir/src/pcs/utils.rs` rejects biased base-field samples and duplicate indices, so it samples a uniform subset. If `A` bounds the number of agreeing positions, the probability that all `t` distinct queries agree is `choose(A,t)/choose(H,t)`, with zero error when `t>A`. The calculator rounds the real agreement count upward and computes this hypergeometric probability. It selects an analysis radius by searching `m=3..100`; this choice changes the proof analysis and leaves the protocol and proof unchanged.

For each mask code and each source code, the Johnson argument bounds its list by `L = m*H/D`. The same bound covers a jointly interleaved list: different codewords agree in at most `(D-1)/H` of their positions regardless of alphabet width. For masks with different dimensions or query domains, the calculator multiplies their individual list bounds and sums their consistency errors. It does not assume that same-height commitment batching reduces those lists.

### Hiding reductions and client IOP

The hiding rows instantiate the reductions in [CFW26, Sections 6, 7, and 9](https://eprint.iacr.org/2026/391). Write `L_source` for the current source list, `L_masks` for the product of all masks committed at that point, `L_next` for the new source list, and `L_switch` for the new switch mask list.

| Reduction | Charged terms |
| --- | --- |
| Masked sumcheck, Lemma 6.5 | `L_source*L_masks/q` for the first combination; per fold, MCA plus `ell_zk*L_source*L_masks/q` |
| Code switch, Theorem 9.6 | `(L_next*L_switch)^2*d_ood/(2q)`; previous-source query error; `L_next*L_masks*(t+s)/q` after adding the switch mask |
| Base case, Theorem 7.1 | Source MCA, the sum of mask MCAs, `L_source*L_masks/q`, and source/mask query errors |

The OOD degree `d_ood` includes the current folded message and the switch-mask message containing old encoding randomness and the fresh pad. The committed mask list grows in transcript order: two external groups, the first sumcheck mask, then alternating switch and sumcheck masks. The calculator checks that order and the packed message lengths. The selected configuration uses one private OOD sample and width-one packed mask groups; other layouts are rejected until their mapping is supplied.

The local Spartan algebraic numerator is `15*n_outer + max(2,ell_zk-1)*n_inner + 4`. The SPARK numerator includes tuple/grand-product identities, cubic product sumchecks, layer batching, and opening batching as counted in `spartan-whir/src/security.rs`. The calculator unions these terms over the witness and two external-mask lists. Plain SPARK OOD separation fixes the read-polynomial candidates before the product challenges; its failure events are charged separately. Establishing the exact round-by-round state and extractor for this combination of packed masks and Spartan remains a proof obligation, so the script reports `whole_client_guarantee_established: false`.

## Computational and composition obligations

### Continuation batching across verifiers

Every continuation keeps the carried claim at coefficient one and assigns the fresh OOD and query constraints `gamma, gamma^2, ...`. Initial batching starts with coefficient one. The source checks cover both the scalar claimed sum and the final polynomial weight, since they must use identical powers.

| Verifier | Continuation source | Final weight source |
| --- | --- | --- |
| Native LeanVM | `crates/whir/src/verify.rs`, `crates/whir/src/open.rs` | Same verifier |
| Recursive LeanVM | `crates/rec_aggregation/zkdsl_implem/whir.py` | Saved continuation coefficients |
| Client plain WHIR | `../spartan-whir/vendor/p3-whir/src/pcs/{prover,verifier}/mod.rs` uses `Constraint::new_continuation` | `../spartan-whir/vendor/p3-sumcheck/src/constraints/mod.rs::challenge_powers` |
| Client plain WHIR guest | `crates/spartan_whir_guest/zkdsl_implem/plain_whir_poseidon1.py::plain_combine_continuation` | `accumulate_plain_round_weight` |
| Client hiding WHIR | Pinned `whir/src/pcs/zk/verifier/mod.rs` uses `shifted_powers(combination)` | The same saved coefficient vector |

The plain client domain separator includes a continuation version before its configuration and first commitment. Exported guest constants contain this separator verbatim. Client proofs and generated guests must therefore be regenerated together. The regression uses a carried error `e` and a first fresh error `-e`: the continuation residual is `e(1-gamma)`, which only vanishes at `gamma = 1` for nonzero `e`.

### Exact scope of the conditional claim

The source and algebra review establishes the corrected continuation invariant, nonzero GKR division, the grouped helper relation, and the three-polynomial reduction using a shared candidate list. The quantitative calculation is complete for the stated formulas and dimensions. Applying its coefficient as an end-to-end knowledge-security theorem still requires these concrete correspondence conditions:

1. The constrained-WHIR state must track the particular nearby codeword satisfying the carried linear functional through every fold, OOD/query code switch and final-coefficient step. The universal grouped lifting lemma preserves that particular candidate. Ordinary correlated agreement alone only gives an existential nearby preimage, so substituting its smaller constants requires an additional preservation argument.
2. The client's packed mask and code-switch states must extract the same witness that satisfies its Spartan/SPARK closing constraints. The numerical client ledger supplies event bounds; it does not construct this extractor.
3. Recursive knowledge extraction must recover root execution, child lift proofs, direct proofs and client proofs under the same random oracle. Compatible straight-line extraction, or a quantified alternative, must count every additional oracle query in `Qstar`. A generic rewinding extractor cannot silently reuse the adversary's original budget.
4. Fresh transcript outputs must follow the modeled distribution, and the ordering between the work check and its challenge must prevent independent retries after a passing work prefix. Expected programs, relations, profiles, fixed commitments and application outputs must be authenticated by the caller and the generated programs.

These conditions explain the JSON's explicit conditional status. They are specific proof correspondence requirements, not a requirement for machine formalization. The [classical BCS theorem](https://eprint.iacr.org/2023/1071) requires round-by-round knowledge soundness; an interactive event union alone does not establish it. A valid extracted root trace yields the two accepting lift verifications; extracted lift traces yield accepting direct verifications; extracted direct traces yield accepting client verifications. Unioning the seven local extraction failures gives the displayed tree formula when those hypotheses hold.

The mutual correlated agreement constants are sufficient rather than optimal. [BCGM's powers-generator analysis](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2026.24) and sharper constrained-subspace bounds may improve them. Concrete Poseidon security, sponge behavior, native Merkle binding, application-digest binding and relation binding remain computational assumptions. The terminal Solidity Merkle collision term is excluded throughout this requested calculation.

### Grinding and classical attack work

For a fixed transcript prefix, a classical prover searches for a nonce satisfying the verifier's work check. If one attempt passes with probability `a`, finding a passing nonce takes `1/a` attempts on average in the ideal-hash model. If the subsequent challenge independently causes a particular bad transition with probability `epsilon`, finding both takes approximately `1/(a*epsilon)` attempts. With a uniform `w`-bit check, this contributes `w` bits to that transition's classical work exponent. This is the usual purpose of grinding: a prover performs extra hashing so the protocol can use fewer queries. [Rivain's grinding formulation](https://eprint.iacr.org/2026/1625) describes this work-versus-proof-size tradeoff.

The exact joint probability is `a * Pr[bad transition | passing nonce]`. Applying the independent-product expression requires a justified conditional challenge distribution. Different work checks protect different transitions, and their costs do not automatically multiply across a multiround proof. The grouped calculator applies the actual distributions above. The older ordinary-C1 calculator retains its unscaled diagnostic role. Neither calculation changes the selected grinding checks or backend security parameter.

#### Check placement and distributions

`crates/whir/src/verify.rs` checks query work immediately before STIR indices and folding work after receiving a sumcheck polynomial and before its challenge. Polynomial batching checks precede `lambda`. `crates/whir/src/config.rs` selects queries using `security_level - pow_bits` and derives the per-phase work deficit from its query/combination or folding error formulas. That is the implementation's intended contribution of grinding to the classical target.

Poseidon checks the low `w` bits of a canonical base-field word. For `p = 2130706433`, a uniform word passes with probability `a = (floor((p-1)/2^w)+1)/p`; the exact work exponent is `-log2(a)`. Keccak checks a masked raw 32-bit word, giving exactly `a = 2^-w` in the random-oracle model. These distinctions matter when a bound is close to its target.

The Poseidon prover, native verifier, recursive verifier and Python reference all duplex once after a successful positive work check. The checked output is discarded before the first extension-field coefficient or STIR query is sampled. Invalid nonces reject before that refresh, and zero-bit checks remain no-ops. Keccak consumes the checked raw word before subsequent sampling. The polynomial batching branch retains its explicit duplex before `lambda`. Protocol version fields and WHIR profiles remain unchanged; affected unpublished proofs and compiled recursive programs are regenerated together.

The grouped calculator multiplies the full query/folding event by the exact independent work probability. Exhaustive small-field tests verify the maximum query probability over every agreement set, and polynomial-root tests distinguish fresh sampling from checked-coordinate reuse. Native, compiled recursive and Python regressions check the exact refreshed state, sample parity, zero-bit behavior and invalid nonces. These checks establish the implemented transition and arithmetic; the extraction hypotheses remain explicit.

### Scoped transcript audit

The scope is the selected native/recursive LeanVM proof family and its grouped terminal adapter. The full grouped statement-authority and challenge-order tables appear in [GROUPED_SECURITY_DERIVATION.md](GROUPED_SECURITY_DERIVATION.md). The shared grinding sites have the following authority and prefix requirements:

| Statement component | Authority and binding | First use |
| --- | --- | --- |
| Program/profile and child dimensions | Application configuration; profile capacity and generated dimension checks | Lookup and WHIR challenges |
| Public input and terminal memory region | Caller values observed before roots; evaluation claims authenticated by PCS | Lookup and memory evaluations |
| Fixed program root, prefixes and carried claims | Authenticated preprocessing; expected-root check and ordered statement observation | Lookup and grouped PCS |
| Execution/helper roots and proof claims | Prover-controlled; roots/messages observed before dependent challenges | The corresponding algebra/PCS transition |
| Work witness | Prover-controlled; canonical low-bit check on observed nonce output | Query or folding sample |

| Challenge | Newly fixed transcript prefix | Check and distribution |
| --- | --- | --- |
| Folding scalar | Complete degree-two round polynomial, then work nonce | Positive Poseidon work is followed by a fresh duplex; Keccak consumes a separate word |
| STIR query indices | Next root and observed OOD answer, or explicit final coefficients, then work nonce | Positive Poseidon work is followed by a fresh duplex; every index has ordinary canonical sampling |
| Continuation gamma | Same work/query sequence and root-authenticated values, then explicit duplex | Fresh output; carried coefficient one and fresh coefficients gamma, gamma squared, etc. |
| Grouped lambda | Group gamma, all six cross claims, four-bit work nonce, explicit duplex | Fresh output; three committed polynomials combined with coefficients one, lambda, lambda squared |
| OOD point | Corresponding commitment or virtual-oracle lambda | Earlier than its answer and later work checks; no retroactive work credit |

Native anchors are `crates/whir/src/verify.rs`, `crates/backend/fiat-shamir/src/{challenger,verifier,utils}.rs`, and `crates/lean_prover/src/{profile,verify_execution,grouped_execution}.rs`. Recursive parity anchors are `crates/rec_aggregation/zkdsl_implem/{fiat_shamir,whir}.py`. The current native prover's one-field nonce and raw recursive format's eight-field nonce admit different search spaces but have the same per-fresh-output probability in the stated model. The audit assumes hash binding and authorized expected public inputs; it does not turn a prover-supplied commitment into application authorization.
