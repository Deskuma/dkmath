# Findings 014

## Source checkpoint

The requested instruction014 is the implementation contract; its conjectural singleton classification is a proof target, not an assumption. The live tree was clean. Existing Instruction013 code/reports were inspected. No AGENTS.md was found in the workspace.

Reusable source declarations recorded before new helpers:

- `rough_empty_eq_uncovered`, `sqrtCutoff_support_card_le_three`, `sqrtCutoff_power_four_gt`.
- `roughWave_sum_eq_support_sum`, `sqrt_rough_moment_balance`, `sqrt_covered_moment_balance`.
- `sqrt_rough_prime_divisor_gt`, `prime_dvd_candidate_mem_active`, `sqrt_two_support_repeated_prime`.
- `sqrt_roughTriple_product_offset_mem`, `sqrt_roughTripleMoment_eq_product_count`.
- `mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue`, `activePrime_reducedResidue_packet`.
- Mathlib `Finset.card_eq_one`, `Finset.card_eq_two`, `Finset.card_eq_three`, `Finset.card_bij`, `Finset.card_eq_sum_card_fiberwise`, `Finset.card_image_of_injOn`.
- Mathlib `Nat.minFac_prime`, `Nat.minFac_sq_le_self`, `Nat.minFac_dvd`, `Nat.Prime.dvd_of_dvd_pow`, `Nat.prime_dvd_prime_iff_eq`, `Nat.factorization_pow_self`, `Nat.Prime.factorization_pow`.

The intended elementary singleton argument uses minFac and the fourth-power threshold; numerical factorization will only be diagnostic.

## Support strata partition and singleton label packet

`ParitySafeSqrtRoughStrata` builds. Four pairwise-disjoint existing-carrier filters partition R; N0 identifies with existing U. Weighted cardinal algebra gives R, roughI, M2, M3 and the exact singleton/moment criterion. `roughSingleton_label_packet` extracts the unique actual active prime by `Finset.card_eq_one`.

## Singleton cofactor classification

The proposed classification is true. `sqrt_singleton_point_cube_or_cross` is kernel checked for every natural anchor and actual singleton rough seat. A composite cofactor has minFac at most n; singleton support forces it to p. The new generalized `sqrt_rough_square_quotient_one_or_prime` forces the remaining quotient to p (the unit case falls below the open shell). No additional type or mathematical counterexample arose. Initial compiler failures in carrier proofs were elaboration issues, corrected without changing statements.

## Cube converse/bijection and cross converse/bijection

`ParitySafeSqrtRoughSingleton` builds. `sqrt_cube_offset_packet` and `sqrt_cross_offset_packet` construct actual rough seats with support exactly {p}. Both offset maps are injective; their images are disjoint. The singleton stratum equals their union and its cardinality is exactly cube keys plus cross keys. `sqrtRoughCubeKeys_card_le_one` holds uniformly, by spacing of cubes and n<p².

## Per-p CrossFiber regrouping

CrossFiber uses the finite integer quotient interval with prime q>n. Exact shell membership and `sqrt_cross_count_eq_fiber_sum` are proved. No external cofactor is inserted into the active-label universe.

## Repeated-product converse/bijection

`sqrtRoughRepeatedKeys` uses a sorted pair and Bool side (false repeats p, true repeats q). `sqrt_repeated_offset_packet`, `sqrt_repeated_keys_offset_injective`, `rough_double_eq_repeated_seats`, and `rough_double_card_eq_repeated` build. Exact active support identifies the sorted pair; positive-product cancellation identifies the side. There are no duplicate eligible keys.

## Triple-seat bijection

The existing `sqrtRoughTripleProductsInShell` carrier is retained. `sqrt_triple_offset_packet`, `sqrt_triple_keys_offset_injective`, `rough_triple_eq_product_seats`, and `rough_triple_card_eq_products` build. Injectivity follows by applying `upperTriples` to equal supports and its singleton formula for an increasing triple.

## Complete cardinal census theorem

`ParitySafeSqrtRoughCensus` builds through `sqrt_rough_factorization_census`, product moment/covered formulas, the exact positivity equivalence, and `prime_squareCell_of_cross_fiber_budget`. No alternate coverage/moment ledger was introduced. The exhaustive point disjunction and structural fiber bounds are being added next.

## Bounded singleton diagnostics

All 429 prime anchors 3≤n≤3000 were scanned, with every row and every nonzero owner fiber preserved in `logs/discovery-014.json`; the compact complete row stream is `logs/discovery-014.txt`. Classification assertions found no counterexample. Maximum fiber occupancy is 13, maximum repeated count 7 and triple count 54. These are finite observations, not uniform bounds or asymptotics. Six calibration anchors, including 1021, were selected for independent kernel verification.

## Exhaustive point classification and structural fiber bounds

The exhaustive `sqrt_rough_point_factorization` disjunction and pointwise `sqrt_zero_point_prime` build. The zero case reuses existing uncovered/support-escape primality. `sqrt_cross_fiber_eq_reduced_quotient_filter` proves an exact identity with the prime-above-n filter of the existing reduced quotient interval. It justifies the old wave-capacity comparison. `sqrt_cross_fiber_card_le_div_add_one` and `sqrt_cross_fiber_parity_spacing` build. The geometric bound is only a per-owner bound; no summed strict inequality follows from it here.

## Calibration evaluation engineering

The CrossFiber finite range was tightened to `Ioc (max n (n²/p)) ((n²+2n)/p)` before final validation; the same exact membership theorem is retained. For kernel calibration, Mathlib `Nat.prime_def_le_sqrt` supplies `trialPrime_iff`: the finite trial predicate is equivalent to Nat.Prime and only appears in DkMathTest. Direct default primality evaluation over the external q windows was stopped as too expensive; no mathematical counterexample was inferred from interrupted evaluation. The final calibration retains kernel reduction and never uses native_decide. Full external prime enumeration was replaced by structural recovery of Cross from checked N1 and cube counts, followed by the proved exact fiber regrouping. Three selected fibers are independently kernel evaluated with the bounded primality test. This checks every reported production count without enumerating all external cofactors.

The hand-entered 1013 singleton count was corrected from 161 to 154 using both the preserved diagnostic and 013 moment arithmetic (181−2·3−3·7). It is a transcription correction, not a failed classification. The final checked table is required to agree with both production identities and discovery rows.


## Verification process recovery

After interrupted tool calls, six obsolete Lake/Lean calibration processes remained alive. Read-only host process inspection identified the exact PIDs belonging to this task; those obsolete processes were terminated, preserving the current build. The temporary repository-local trial-predicate probe passed: profiler output showed 181s in import under memory pressure and about 0.09s in tactic execution, confirming that its proof was not the bottleneck. Its reusable predicate/equivalence remains in CensusCounts; the duplicate probe source was removed and its log is preserved. Both final facade and root builds passed (9086 and 10389 jobs respectively). Existing five out-of-scope placeholder warnings are recorded separately from this change's trust audit.

## Final calibration repairs

A completed failed calibration attempt is preserved in `logs/calibration-attempt-014.txt`: the numerical rough moments and cube checks succeeded, while the test-only predicate needed an explicit `Decidable` instance. Added `instDecidableTrialPrime` with the finite sqrt-divisor decision procedure. A profiling run after process cleanup measured about 10s import and about 9.5s kernel checking for the new rough moments; interrupted heavy copies had distorted earlier runtime.

The 1021 inventory proof now reuses the checked 1019 inventory and proves the exact boundary update by prime divisibility and the nonprime integer 1020. Only primality certificates for 1019/1021 and the sqrt boundary are needed. Compiler repairs used `decide +kernel` for sqrt reduction and an explicit `if_neg` for the filtered insert. No production mathematical statements were weakened.

## Six complete census calibrations

Final CensusCounts builds (17s) and CensusCalibration builds (14s), with no new warnings. `full_census_checked` proves all reported production cards at 211,503,1009,1013,1019,1021. `census_cross_fiber_sum_checked` proves the six exact owner sums. Selected independent fibers have cards 3,7,7. `census_endpoints` and `shell1021_prime_from_census` consume product-count strict inequalities, not whole E/I evaluation.

The closed 2042-offset carrier caused recursion/heartbeat expansion when rewriting directly. Added reusable symbolic inventory adapters in the test module and specialized them only after proving their generic statements; this resolved the compiler limit without widening proof assumptions. Production census statements remain unchanged.

## Final mathematical judgment

All required support strata, singleton forward/converse uniqueness, cube bound, repeated/triple bijections, exact point/set/cardinality census, moment normal forms, fiber regrouping and elementary bounds are proved. Optional reduced-quotient connection is also proved. Uniform strict fiber budget remains an explicit unproved provider obligation. No classification counterexample was found or asserted; all compiler failures and finite-data transcription corrections are distinguished above.

Final axiom audit builds (9094 jobs): 119 public/source-API entries, including all 69 new production declarations, are checked. The full-set parser confirms only the three standard logical axioms and no sorryAx. Header/forbidden-token/whitespace/artifact checks pass. Final facade/root builds remain PASS; pre-existing root placeholder warnings are out of scope and absent from these dependencies.

Outcome A — COMPLETE SQRT-ROUGH FACTORIZATION CENSUS
