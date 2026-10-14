# Instruction 038 report

Outcome C. The universal aggregate compensation inequality is neither proved nor refuted. Exact central carry coordinates, common-mass cancellation and positive product encoding are formalized. A structural obstruction to both same-base compensation and one-coordinate weight domination is identified and kernel-checked. These exact bridges are not reported as a new independent weighted upper bound. The strongest proved correction budget remains Instruction 037.

## Exact central coordinates

The new production module [GnomonCentralCarryCompensation.lean](../../../DkMath/NumberTheory/Legendre/GnomonCentralCarryCompensation.lean) defines the central carrier

    C(n) = {d in [1,2*n] : IsPrimePow d and d <= n%d+n%d}.

For d=p^a, its weight is vonMangoldt(d)=log(p), counted once for each active exponent coordinate. A thin specialization of Mathlib factorization_choose' proves that the number of active exponent coordinates in a cutoff Ico(1,b), with log_p(2*n)<b, equals the p-adic factorization exponent of choose(2*n,n). This reuses the existing Kummer currency without a new arbitrary-binomial framework.

The full weighted bridge is proved independently by the existing factorial/floor incidence theorem. Factorial cancellation gives log choose(2*n,n) = log((2*n)!)-2*log(n!). For each positive d, the exact floor identity is

    floor(2*n/d) = 2*floor(n/d) + centralCarry(n,d).

Nonprime-power weights vanish. Hence Lean proves, for every n including empty boundary cases,

    log choose(2*n,n) = sum over C(n) of vonMangoldt(d).

No diagnostics or compensation assumption enter this identity. DivisorIncidence, GnomonDivisorCarry, Mathlib Choose.Factorization and the DkMath BinomialPrimePower Kummer receivers were audited before choosing this thin bridge.

## Common cancellation and product encoding

Let S(n) be the existing small-carry carrier. The production API names

    common = S intersect C,
    small-only = S minus C,
    central-only = C minus S.

The exact split theorem expresses both full masses as their common mass plus their respective residual mass. Subtracting gives

    smallCarry - log centralBinomial
      = smallOnlyMass - centralOnlyMass.

Consequently the candidate is equivalent to smallOnlyMass <= centralOnlyMass. Since all remaining coordinates are prime powers, the same comparison is equivalent to

    product over small-only of minFac(d)
      <= product over central-only of minFac(d).

Both products are positive; empty products are one. Distinct powers of the same prime contribute repeated base factors, so multiplicity is retained. Divisibility is not assumed. The equivalences delimit the open target; they do not establish its sign and are not counted as compensation progress.

## Formal structural obstruction

At n=4, common is empty, small-only is {3}, and central-only is {5,7,8}. The left product is 3; the right product is 5*7*2=70. Thus the missing log(3) is compensated in total by log(70), while 3 does not divide 70. Same-base exponent-chain domination fails: there is a small residual at base 3 and no central residual at base 3. The retained pointwise n=4,d=3 counterexample remains kernel-checked.

At n=27, the exact residual carriers are

    small-only = {5,11,19,23},
    central-only = {2,4,7,16,47,49,53}.

Their contributed bases are respectively {5,11,19,23} and {2,2,7,2,47,7,53}. The products are 24035 and 976472. The compensation inequality is formally derived from the retained 037 finite central-binomial proof at this anchor.

A stronger obstruction is also proved: no injective map from small-only labels into central-only labels can weakly increase each contributed prime base. The three left bases 11,19,23 exceed 7, whereas only two right bases, 47 and 53, exceed 7. The Lean proof restricts any proposed map to those high-base labels and contradicts the finite cardinal inequality 3<=2. Since log is increasing on these positive bases, a one-coordinate weight-dominating injection cannot prove the universal candidate either.

The successful finite inequality at 27 therefore requires pooled cross-base compensation. For example, 11 can be paid by the two base-7 coordinates, 5 by the three base-2 coordinates, and 19 and 23 by 47 and 53. The existing Kummer receivers identify valuations of each coefficient separately; they supply no uniform rule allocating such disjoint groups across the two different carry systems.

Complementary residue pairing was also tested. The calibration preserves d=11 with residue 3 (n=14), which is small-only locally, and its complementary residue 8 (n=8), which activates both carry systems. Thus complementing a residue can land in common mass, not central-only mass; it is not an automatic compensation involution. Moreover it changes n rather than defining a map on the fixed-n label carrier.

Label-size matching is insufficient for the weights: a larger coordinate such as 49 contributes only log(7), less than the weight log(11) at the smaller coordinate 11. The bounded search finds label matchings, but that does not upgrade them to weight matchings. No independent uniform pooled-product inequality, corrected compensation error bound, or fixed-n weighted involution was obtained. This is the precise limitation of the available carry APIs, not a claim that the original conjecture is false or impossible to prove by other methods.

## Bounds and correction budget status

No new unconditional central-binomial bound is exported. No B_central provider is added with an unproved universal compensation assumption hidden inside it. The strongest proved phase-aware small bound remains

    smallCarry <= psi(2*n)-E_037,

and the strongest implemented independent combined envelope remains

    C_ns <= B_phase_037 <= B_036.

The repeated-large band and finite reciprocal higher correction remain available and unchanged. The existing 037 conditional consumer remains the applicable proved provider. No exclusion radius was widened and the closed singleton factor-depth branch was not reopened.

For interpretation only, diagnostics compute the hypothetical envelope

    B_central = log choose(2*n,n) + repeatedBand + reciprocalBudget.

Its use as a universal independent bound is conditional on the unresolved weighted compensation theorem. It need not uniformly improve B_phase: at n=4, the existing phase small bound is smaller than the central logarithm. At the larger retained anchors it is numerically sharper, but no general ordering against 037 is asserted.

## Exact bounded search and retained anchors

The search checks the positive residual-product comparison using exact Python integers for n=3..10000. It finds no counterexample. This is an exact bounded computation, not a kernel-checked universal theorem. Logs and budget margins are floating diagnostics only. The diagnostic verifies the central carrier product equals choose(2*n,n) at recorded samples, records exact products and both difference carriers at the required anchors, and stores the SHA-256 of its retained 037 source.

The recorded budget samples are n=3..300 plus 1031 and 5000 (300 values). Same-base domination first fails at 4, and one-coordinate base domination first fails at 27 in this bounded search. The formal regressions certify those obstructions independently of the search. No unsampled global-first-failure claim is made.

| n | small-only mass approx | central-only mass approx | compensation margin approx | proved phase margin diagnostic | hypothetical central margin diagnostic |
|---|---|---|---|---|---|
| 4 | 1.098612 | 4.248495 | 3.149883 | 7.160648 | 4.010765 |
| 27 | 10.087266 | 13.791701 | 3.704435 | 22.477546 | 22.623259 |
| 32 | 10.017932 | 19.392880 | 9.374949 | 22.189462 | 24.973217 |
| 69 | 19.116154 | 66.423487 | 47.307333 | -11.231783 | -3.808373 |
| 210 | 44.634558 | 141.348648 | 96.714091 | 64.626574 | 107.540259 |
| 297 | 62.686982 | 254.243388 | 191.556406 | -52.888370 | 10.213420 |
| 1031 | 277.066849 | 819.427151 | 542.360302 | 254.171238 | 639.553776 |
| 5000 | 1355.899106 | 3995.372252 | 2639.473145 | 186.132458 | 2667.302497 |

Even if universal central compensation were proved, the hypothetical criterion still misses at n=69 by about 3.808373. It would remove the retained n=297 failure numerically, giving about +10.213420, and enlarge the positive n=5000 margin from about +186.132458 to +2667.302497. These signs are diagnostic interpretations, not new certified prime-existence results. Correction slack remains decisive at 69, so the evidence does not isolate Q as the sole remaining obstacle. Since the aggregate theorem is unresolved, there is no stronger proved correction envelope in this checkpoint.

## Validation

Focused production/calibration, complete Legendre facade, root DkMath, and all-new-production axiom audit builds pass using LEAN_NUM_THREADS=2. The audit covers all ten public production declarations (four definitions and six theorems); the private log-product helper is covered transitively. Only propext, Classical.choice and Quot.sound occur. New sources contain no forbidden proof constructs, retain unified headers and immediate file markers, and pass the scoped artifact audit and git diff --check.

| Build | Exit | Seconds | Peak RSS KiB | Swaps |
|---|---|---|---|---|
| focused | 0 | 26.541 | 7031200 | 0 |
| axiom-audit | 0 | 13.315 | 6735196 | 0 |
| facade | 0 | 13.438 | 6752232 | 0 |
| root | 0 | 14.037 | 7116392 | 0 |

Focused, facade and axiom-audit logs contain no warnings. The root reports five pre-existing sorry warnings in TriominoFLT:1919, ZsigmondyCyclotomicResearch:147, TriominoCosmicBranchA:4187, GcdNextResearch:850 and CyclotomicPrincipalization:5389, outside this new-declaration audit. No whole-repository sorry-free claim is made. No memory failure occurred. Timings are incremental measurements rather than clean-build benchmarks.

Artifacts: [source inventory](source-inventory-038.md), [coverage](evidence/MANIFEST.md#log-edee162589f0ac16), [diagnostics](evidence/MANIFEST.md#log-ea95521a7d39fe39), [focused](evidence/MANIFEST.md#log-16625325f8612fc2), [axiom audit](evidence/MANIFEST.md#log-44850286cee7b614), [facade](evidence/MANIFEST.md#log-c3f21ed6eb21def9), [root](evidence/MANIFEST.md#log-e494b4d6fae97e68), and [artifact check](evidence/MANIFEST.md#log-15ca80b9fe794485). Reproduce with checks/build-038.py (focused axiom-audit facade root), checks/diagnostics-038.py and checks/check-038.py.

## Next natural frontier and implementation proposal

The open object is now an exact weighted product comparison between explicit difference sets. A useful implementation proposal is to investigate a single disjoint pooled-block assignment whose block products dominate the left base products, using the n=27 grouping as a calibration and the formal no-injection theorem as a regression. Such a construction must have a new arithmetic allocation rule independent of the desired inequality; an existence receiver that simply assumes the product comparison would be circular repackaging. No such uniform rule is presently proved.

If pooled allocation cannot be justified from fixed-n residue structure, the remaining issue is a genuinely weighted prime-power comparison beyond the current per-base Kummer identities. The hypothetical n=69 deficit also shows that settling central compensation would not itself settle all correction-envelope failures. Preserve the exact compensation defect and the separate repeated-band/higher slacks when judging further estimates. No arbitrary carry framework, local exclusion heuristic, analytic conjecture, or design for Instruction 039 is introduced.
