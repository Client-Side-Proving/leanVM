# Current grouped terminal: conditional quantitative derivation

Date: 2026-10-15. Derivation for the selected artifact with fresh Poseidon output after grinding; profiles remain unchanged.

The selected artifact is `leanVM/benchmark-results/2026-10-15-poseidon-grinding-fresh/terminal/native/root-fixture.json`, proof SHA-256 `fdaa43cd34298cbcb40a9c5b4fa1618cbac8cdfb04f7afa61b19d17d1249eb68`. Its root has 23 variables, rate 1/64, first fold 5, subsequent folds 4, initial domain reduction 1, threshold 6, and nominal security/grinding settings 100/28. It uses three initial commitments and grouped mode observation `[0x474c5531,1,8,3,5,11,4,0]`. This derivation excludes hash collisions, random-oracle conversion, client/direct/lift errors, and recursive composition unless stated explicitly.

Run `python3 script/grouped_security_accounting.py` from the LeanVM repository root. The calculator uses the same initial analysis radius for the grouped additions and the shared WHIR proof. Its `grouped_events(m)` function evaluates the extra grouped terms. The selected analysis radius is `m=5`, giving a grouped subtotal of 103.5668 bits and an algebra subtotal using capacity bounds of 121.6215 bits. The shared WHIR coefficient is 98.1766 bits; it dominates the root. Full-chain composition and the exact grinding distributions are recorded in [SECURITY_ACCOUNTING.md](SECURITY_ACCOUNTING.md).

## Main result

A single joint list suffices for the grouped AIR and initial batching when the universal same-agreement-set property of list correlated agreement is used. An independent execution-list times helper-list product is unnecessary. The lookup challenges occur earlier, so their bound uses the execution list alone, fixed before those challenges. The fixed program polynomial contributes no list factor.

For the native analysis choice m=6, the sufficient initial agreement is a=13/96, and every relevant initial list has at most L=384 elements. The degree-two, width-32 initial combination has error at most 2^-98.3090955365 under uniform interactive lambda. Its explicit separate 4-bit work check gives a joint event of 2^-102.3090955365 per independent attempt in an ideal random-oracle work analysis. This credit applies at this transition only. The grouped AIR/lookup/claim algebra has union error at most 2^-123.0319538203 for the measured shape, or 2^-121.3584335056 using the loose capacity bounds S<=2^23 and h<=23. These values do not establish 100 bits for the complete chain.

## Code and polynomial geometry

Let p=2130706433, q=p^5, log2(q)=154.9434234372. Let C be the RS code over the extension field with base-field evaluation domain H of size 2^24 and scalar dimension D=2^18. Each initial Merkle leaf contains K=32 base-field values. The committed oracles f, g, h are elements of (F_q^32)^H, with g the exact trusted fixed-program codeword. The underlying full message has 23 variables and 2^23 coefficients. The virtual initial oracle is v_lambda=f+lambda*g+lambda^2*h, assembled from openings at the same row indices. It has no additional Merkle root.

The source maps this equation directly: `crates/whir/src/open.rs:233` observes all six cross values; lines 235–239 check work, duplex, sample lambda and use `[1,lambda,lambda^2]`. The verifier mirrors it at `crates/whir/src/verify.rs:325`–342. `verify_stir_challenges_linear_combination` opens the same query positions against all three roots. Subsequent rounds use the shared ordinary WHIR state machine, with fresh continuation coefficients starting at gamma at `verify.rs:417`–427 and `open.rs:386`–401.

Base-field input words do not add an alphabet-conversion assumption here: a scalar RS polynomial of degree<D agreeing with a base-field word at more than D points of a base-field domain has base-field coefficients, by unique interpolation. Thus the decoded execution and five-coordinate helper messages are base-field messages.

## Joint list and lifting lemma

For any analysis m>=3, set rho0=D/H=2^-6, a=sqrt(rho0)*(1+1/(2m)), and define

- Lambda_f = {F in C^32 : agreement(F,f)>=a};
- J(f,h) = {(F,Hh) in C^32 x C^32 : agreement((F,Hh),(f,h))>=a}.

Agreement in J means simultaneous agreement of every coordinate of both words on the same rows. The vector code C^64 has relative pairwise agreement at most rho=(D-1)/H, because distinct vector codewords differ in at least one scalar RS column. Applying the usual Johnson counting argument directly to this alphabet gives

`|J| <= (1-rho)/(a^2-rho) <= 1/(a^2-rho0) < m/rho0 = 64m`.

The same bound holds for Lambda_f and for the list of v_lambda in C^32. For clarity, the elementary counting proof uses the candidate agreement sets: sum over row multiplicities, apply Cauchy–Schwarz, and bound each pairwise intersection by (D-1). It does not multiply scalar-column list sizes. In particular |J|<=384 at m=6. Projection of every element of J to its first component belongs to Lambda_f.

For the needed universal statement, use [Ben-Sasson–Carmon–Haboeck–Kopparty–Saraf, Theorem 4.6](https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf), with curve degree two. Write rho=(D-1)/H, gamma=1-a, t=max(ceil(sqrt(rho)/(a-sqrt(rho))),3), A=t+1/2, and

`B(H,D,a) = H*(2*A^5 + 3*A*gamma*rho)/(3*rho^(3/2)) + A/sqrt(rho)`.

For each of the 32 scalar columns, the number of exceptional lambda values is at most 2B. A union over columns costs 32, giving `epsilon_lift <= 2*32*B/q`. There is no candidate-list multiplier in this theorem: its bad event already quantifies over every sufficiently large agreement set.

Outside that event, take any c in C^32 agreeing with v_lambda on any Aset of size >=aH. On that same Aset every column of f, g, h extends to a codeword. The unique extensions give F, G, Hh. Since g is itself a known codeword and |Aset|>D-1, G=g. Thus (F,Hh) is in J. Also c=F+lambda*g+lambda^2*Hh, since both sides are degree<D in each scalar column and agree on Aset. This proves the exact correspondence needed for the later constrained candidate, not just the existence of some unrelated nearby tuple.

This coordinatewise argument is the same elementary width union formalized for arbitrary coefficient generators by [Chiesa–Fenzi–Wang, Lemma 3.15 and Definition 3.14](https://eprint.iacr.org/2026/391). It applies to `(1,lambda,lambda^2)`, even though that paper's later constructions mainly use two-term generators.

### Why helper adaptivity does not introduce a product

Lambda_f is fixed after the execution root and before lookup gamma,beta. The helper root, and therefore J, can depend on those lookup challenges. Consequently a lookup bound using a helper-dependent list before gamma,beta would be invalid. Instead union the lookup identity failure over Lambda_f. Every later extracted F is in Lambda_f, regardless of how the helper was chosen.

Once the helper root is observed, J is fixed before all AIR and balance challenges, sumcheck challenges, public-memory points and initial PCS batching challenges. Union over J for these later equations. A prover choosing a helper after gamma,beta is legitimate: it is meant to encode inverses at those challenges. The inverse relations subsequently force those helper entries uniquely for each decoded execution candidate.

Separate L_f*L_h is a conservative fallback if one knows only separate proximity with different agreement sets. The actual shared-query construction and the universal lifting lemma above supply the stronger common-set statement, so that fallback is not required here. The known fixed g never adds a candidate-list factor.

## Grouped lookup and AIR relations

Each bus contribution is a fraction m_i/(gamma-phi_i(beta)), where phi_i is a multilinear fingerprint in four beta coordinates. For a group of at most eight fractions, the code forms `D=product d_i` and `N=sum m_i product_{j!=i} d_j`, then proves `uD=1` and contributes `uN` to the global balance. See `crates/sub_protocols/src/grouped_logup.rs:90`–134 and `grouped_logup/air.rs:168`–218. The five base coordinates of each u are authenticated by PCS at `air.rs:363`–391.

For fixed decoded F, a false lookup multiset gives a nonzero numerator polynomial after combining distinct denominator factors. Its total degree in gamma and the four beta coordinates is at most `4(S-1)`, where S is the number of bus slots. Distinct tuple fingerprints are distinct formal multilinear polynomials; domain tags are included. Thus the lookup error is at most `4(S-1)*|Lambda_f|/q`. This statement uses the field-multiplicity semantics plus the source no-wrap bounds. At the selected geometry all slot counts are below p; the accepted root-capacity bound S<=2^23 is also below p. A semantically false trace with an identically balanced formal lookup still has to violate the retained execution/AIR or fixed-public-data relations, which are checked separately.

Selected slot count:

`S = 2^19 + 2^17 + 5*2^17 + 16*2^16 + 33*2^13 = 2,629,632`.

The source bus counts are in `lean_vm/src/tables/execution/mod.rs:28`, `extension_op/mod.rs:90`, and `poseidon/mod.rs:98`. `grouped_logup/pcs.rs:191`–195 bounds occupied source length. Each table bus count is no larger than its committed width, giving the convenient capacity bound S<=2^23 for the selected root dimension.

A zero denominator does not create a grouped soundness exception after the AIR is established: `uD=1` has no solution when D=0. Charging `4S*L/q` as a bad event is optional conservatism; it is not required to make the fraction-to-inverse implication valid. The honest prover's inverse failure is a completeness abort. The ordinary recursive GKR strict-division fix remains separate and untouched by grouped execution.

There are 145 ordinary table constraints, of which six virtual-bus constraints are replaced by ten inverse-product constraints. The grouped constraint total is 149. The five sections have ten helper groups and 50 base-coordinate helper claims. The retained table constraints and degrees appear at `grouped_logup/air.rs:126`–158. Every constraint receives a distinct global alpha power, and the global lookup sum receives a separate balance challenge b at `air.rs:238`–259. For a fixed candidate pair, a false constraint array or false global balance therefore makes the combined polynomial in `(eq,alpha,b)` nonzero. With maximum selected section height h=17, a conservative total-degree bound is `h+148+1=166`; use h<=23 for the loose capacity version.

The batched AIR sumcheck has h rounds and individual degree at most 11 (`lean_prover/src/grouped_execution.rs:199`). Unioning over J gives at most `11hL/q` over all its rounds, or `11L/q` per round. Smaller sections are embedded using the leading product of sumcheck coordinates; equality weights use the corresponding suffix. This embedding is mirrored by the verifier at `grouped_logup/air.rs:342`–358. All source claims are authenticated; public row-address evaluations are reconstructed rather than supplied.

There is no quotient-GKR term in the grouped root. The helper inverse constraints replace that root argument. Quotient-GKR terms remain necessary in ordinary direct/lift proofs and are outside this root derivation.

## Opening claims and initial batching

The selected source claims are 16 memory, 16 bytecode, 174 table/shift and 50 helper values, totaling 256. Of the 206 source claims, eight bytecode fingerprints are sent to g, leaving 198 primary claims. Two PC boundary claims and two public-memory evaluations bring the primary group to 202; two carried program claims plus all eight root program claims give fixed group 10; helper group has 50. See `grouped_logup/pcs.rs:11`–16, 203–255, `sub_protocols/src/stacked_pcs.rs:55`–112, and `lean_prover/src/grouped_execution.rs:208`–250.

Each group's gamma powers restart from one. For each candidate tuple with a false opening, choose one false group before gamma. Its residual has degree at most 201, giving `201L/q` for all candidates. A more mechanical union over all three groups gives `(201+9+49)L/q` and is also safe. Public-memory matching has error `(3+8)L/q` for the selected eight-element public input and 256-element public region; their claimed values are computed from trusted public data.

After gamma fixes the three linear functionals A_i, the six off-diagonal cross claims c_ij are observed. Let P=(F,g,Hh), and define c_ii from each original group's claimed sum. For each row i, the residual under lambda is

`R_i(lambda) = sum_{j=0}^2 lambda^j * (A_i(P_j)-c_ij)`.

If one original group's residual is nonzero, its diagonal coefficient in this degree<=2 polynomial is nonzero. Choose one such row for each fixed candidate; probability that its residual vanishes is at most 2/q. Union over J gives `2L/q`. No factor for the six cross values is needed. The lifting event is separate and costs the universal `64B/q` above.

The one combined OOD point comes after lambda. For the list of v_lambda, distinct full messages have unequal univariate-expanded polynomials of degree at most 2^23-1. Pairwise separation failure is at most `choose(L,2)*(2^23-1)/q`; the existing WHIR event `L^2*2^23/(2q)` is a safe upper bound (115.7734984358 bits at m=6). This is already counted as initial OOD in the ordinary WHIR ledger and must not be added twice.

Theta then combines the OOD statement and three group functionals with weights `1,theta,theta^2,theta^3`. A false statement contributes a nonzero degree<=3 residual; `3L/q` is safe. A unique OOD-selected candidate can sharpen this factor, but the numerical report keeps L. Finally, shared WHIR authenticates the resulting constrained candidate.

## Extraction mapping and remaining hypothesis

The grouped extension has the following explicit reduction to constrained WHIR:

1. Fix the oracle roots and transcript prefix; define Lambda_f before lookup and J immediately after helper commitment.
2. Reverse an accepted shared-WHIR proof to a candidate c close to v_lambda that satisfies its final linear functional. This is the ordinary constrained-WHIR extraction obligation, with its phase-wise fold/MCA, OOD, query and continuation-batching errors.
3. Outside theta-batching failure, c satisfies the OOD and three row constraints. Outside the universal lambda lifting event, c=F+lambda*g+lambda^2*Hh for some pair in J, on the same agreement set.
4. Outside the degree-two cross-consistency event and original-group batching event, that pair authenticates every source/helper/fixed-program claim. Reverse the degree-11 AIR sumcheck, and the independent constraint/balance challenges, unioning over the fixed J. This yields the retained AIR constraints, every inverse equation, and global balance on Boolean rows.
5. Project F to Lambda_f and exclude the earlier lookup identity failure. Public-memory and fixed-program authentication then tie the decoded execution to the requested statement.

Step 2 requires an extraction result for a degree-two virtual initial oracle represented by three individually binding roots. The source makes every queried row equal to v_lambda by checking all three Merkle openings at the identical positions. Therefore the virtual-oracle adapter is deterministic and introduces no further probabilistic event once oracle binding holds; the shared WHIR reduction thereafter sees the same oracle access and linear constraint as in its ordinary proof. The initial constraints may be chosen adaptively after commitment: they are bound before the dependent group/row/folding challenges, and the list union above handles that order. Deferred OOD is accounted for explicitly, rather than assuming a unique candidate before AIR.

A complete theorem-level claim still needs the ordinary constrained-WHIR reverse-extraction/round-by-round state invariant established for this checkout's exact fold, code-switch and final-coefficient ordering, together with its compiler to Fiat–Shamir and the actual grinding distribution. This derivation supplies the grouped adapter and all its extra events; it does not independently formalize that ordinary implementation-to-theorem correspondence. CFW26's no-mask specialization explains the relevant state: a nearby codeword satisfying all carried linear functionals; OOD separates the next commitment list before query sampling; code-switch queries recover a common agreement set; shifted fresh coefficients preserve the carried functional. The source follows that order at `whir/src/verify.rs:387`–459. The earlier coefficient-one continuation defect is fixed by `combine_constraints(...,true)` at line419; substituting the old equation would break this state invariant.

The universal list-CA constants used here are sufficient, not claimed optimal. A tighter weighted constrained-agreement theorem may reduce the MCA constants. Its application must handle constraints coupling all 32 interleaved coordinates. Merely replacing Theorem4.6's parameter with ordinary correlated-agreement's parameter does not prove the universal lifting lemma above. A different round-by-round proof using constrained subspaces could be valid; it needs its own interleaving/constraint theorem mapping. Failure of this conservative bound to reach 100 bits is not a demonstrated attack.

## Statement authority

Scope: `verify_execution_inner` in grouped mode, `verify_grouped_tail`, `verify_three_commitments`/`verify_linear_combination` and the selected binary-root caller. All paths below assume that the application supplies the intended bytecode, profile, fixed root, and public statement; native API type checks alone do not authorize them.

| Component | Supplier and control | Binding or validation | First dependent challenge | Result |
|---|---|---|---|---|
| Root bytecode, protocol profile, dimensions, selectors/prefixes, batching work | Trusted application configuration; proof cannot override | Static profile/C1 descriptor in FS cap; parsed primary dimension equals configured secondary dimension (`verify_execution.rs:180`–196,258–285) | Lookup gamma | Bound under caller authorization |
| Grouped mode identity | Verifier mode selection | Eight fields observed before public statement and roots (`verify_execution.rs:199`–200; `grouped_execution.rs:14`) | Lookup gamma | Bound |
| Fixed polynomial g | Trusted preprocessing/application root | Exact expected secondary Merkle root comparison (`verify_execution.rs:281`–284); dynamic fixed-program prefixes are part of descriptor | Lookup gamma | Known exact codeword under preprocessing and binding assumptions |
| Application root and public memory | Caller supplies public fields; native validation checks region bounds | Public input, region header and values observed before dimensions/roots (`verify_execution.rs:202`–208); public evaluations PCS-bound | Lookup gamma, later memory points | Bound; semantic application authorization is external |
| Carried program statements | Caller supplies decoded root public memory and fixed layout | Ordered full statement observation before dimensions/roots; PCS includes them with all eight root program openings | Lookup gamma, group gamma | Bound and authenticated |
| Execution oracle f | Prover | Merkle root observed before lookup (`verify_execution.rs:270`–286) | Lookup gamma,beta | Lambda_f fixed |
| Helper oracle h | Prover, adaptive to lookup | Root read before duplex and AIR challenges (`grouped_execution.rs:193`–198) | eq,alpha,balance | J fixed; cannot justify earlier lookup challenges |
| AIR final claims | Prover | Read/observed before public-memory points and PCS group challenge (`grouped_execution.rs:199`–229) | Public memory points, group gamma | All256 claims authenticated by their respective groups |
| Cross claims | Prover, adaptive to group gamma | Six values observed before work/duplex/lambda (`verify.rs:325`–341) | lambda | Bound |
| Combined OOD answer | Prover, adaptive to OOD point | Answer read before duplex/theta (`verify.rs:343`–357) | theta | Bound |
| Continuation roots, OOD answers, query answers | Prover | Each observed before corresponding fresh batch/fold challenge (`verify.rs:387`–427) | Continuation gamma and folds | Correct shifted coefficients retained |

## Challenge order

Prover and verifier agree at the listed sites. “Prefix” includes all earlier rows in this table and the static cap/mode/public statement.

| Challenge | Newly fixed prefix | Used for | Candidate set permitted at that point | Source anchors |
|---|---|---|---|---|
| Lookup gamma, then four beta coordinates after duplex | Dimensions and execution/fixed roots | Bus denominators and tuple fingerprints | Lambda_f only; helper absent | `verify_execution.rs:270`–302; `grouped_execution.rs:90`–103 |
| eq vector, alpha, balance b after duplex | Helper root | Row equality,149 constraint weights, global lookup balance | J(f,h) | `grouped_execution.rs:193`–199; `air.rs:238`–259 |
| h AIR sumcheck challenges | Each degree11 round polynomial | Reduce combined relation to final column claims | J(f,h) | `grouped_execution.rs:199`–205 |
| Public-input/region points | All256 final claims | Bind trusted public memory to execution | J, projected execution | `grouped_execution.rs:200`–229 |
| Initial group gamma after duplex | All opening points/values, including derived public evaluations and carried fixed claims | Independently batch groups202/10/50 | J | `verify.rs:320`–324; `open.rs:215`–219 |
| lambda after4-bit work and explicit duplex | Six cross values and work witness | f+lambda*g+lambda²*h and three row claims | J fixed; universal curve lifting | `verify.rs:325`–342; `open.rs:233`–239 |
| Combined OOD point after duplex | lambda | Separate virtual-oracle candidate list | Lambda(v_lambda), at most L | `verify.rs:343`–345; `open.rs:241`–255 |
| theta after duplex | OOD answer | OOD plus three grouped functionals | Same virtual list | `verify.rs:345`–369; `open.rs:256`–267 |
| Initial folds | Each quadratic sumcheck message | Fold constrained virtual oracle | Shared WHIR phase list | `verify.rs:379`–385 |
| Next OOD/query/fresh batch/folds | Next root, OOD answer, work, openings, then duplex | Code switch, continuity and carried functional | Appropriate next-phase list | `verify.rs:387`–427; `open.rs:320`–401 |
| Final queries and final sumchecks | Explicit64 final coefficients; work before queries | Authenticate final codeword and close functional | Explicit final polynomial | `verify.rs:432`–459 |

## Numerical grouped additions at m=6

| Event | Conservative error | Bits |
|---|---|---:|
| Lookup rational identity | 4(S-1)L/q | 123.0320320 |
| Constraint batching, equality and balance | (17+148+1)L/q | 138.9834215 |
| AIR sumcheck, all17 rounds | 11*17*L/q | 138.8115665 |
| Public memory evaluation | 11L/q | 142.8990293 |
| Original group claims | 201L/q | 138.7074092 |
| Cross consistency | 2L/q | 145.3584609 |
| OOD plus3group combination | 3L/q | 144.7734984 |
| Algebra union | Sum of preceding7 rows | 123.0319538 |
| Universal lambda lifting | 2*32*B/q | 98.3090955 |
| Lambda lifting with its independent4-bit work, ideal RO | 2^-4 * 2*32*B/q | 102.3090955 |

Initial OOD separation and all remaining WHIR errors are already provided by the shared ledger and must be included once. The generated JSON includes the native-m phase events to make double counting visible. For a round-by-round composition, use the appropriate maximum transition error and the explicit work/RO theorem; retain list unions inside each transition.
