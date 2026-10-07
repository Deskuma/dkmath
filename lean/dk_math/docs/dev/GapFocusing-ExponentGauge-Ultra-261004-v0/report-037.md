# Instruction 037 report

Outcome B, via a proved alternative phase exclusion. A genuine phase-aware small-carry bound and a stronger independent correction envelope are formalized. The universal central-binomial candidate is unresolved: it is neither proved nor refuted here. No universal strict budget result or new unconditional prime-existence range is claimed.

## Central-binomial investigation

The candidate smallCarry(n) <= log(choose(2*n,n)) is not used as a premise, production definition or consumer hypothesis. Diagnostics test n=3..10000 and find no counterexample. The largest sampled ratio is 0.8947754213634967 at n=27. The calibration additionally proves the inequality at n=27 in Lean, by a kernel-checked natural product inequality followed by the exact von Mangoldt/log-product identity and monotonicity of log. This finite result is not extrapolated to all n.

The audit inspected GnomonDivisorCarry's remainder/floor identities, its prime-power carry receiver, Mathlib's factorization_choose, DkMath's BinomialPrimePower Kummer/valuation receivers and PascalPrebirthBoundary. The central coefficient counts the coordinates d <= n%d+n%d; the small square-shell carry instead uses d <= n^2%d+(2*n)%d. These coordinates are not pointwise included. The calibration preserves n=4,d=3: small carry is one, central carry is zero, and choose(8,4) has zero factorization at 3. This refutes a direct coordinate inclusion, not the proposed aggregate inequality. The existing row-height and factorization results do not supply weighted compensation across different labels. That missing aggregate comparison is the precise proof obstruction retained here.

Rather than assert that the central candidate is false, this checkpoint proves one useful weaker replacement from the same carry geometry.

## Proved phase-aware replacement

For d in [1,2*n], put r = n%d. Define the exclusion set Eset by either

    r <= 4*sqrt(d) and r^2%d + (2*r)%d < d,

or

    r = d-1.

Let E(n) be the sum of von Mangoldt weights over this set. The fixed radius 4 selects one bounded quadratic-residue zone; it was calibrated for a useful retained-anchor saving, not asserted to be optimal. The minus-one class is also included because its exclusion is algebraically uniform. No arbitrary carry-comparison hierarchy or variable-radius campaign is introduced.

The definition uses a width residue and a sufficient zero-phase condition. It does not query Q, shell primes, old-budget strictness, or the exact small-carry event carrier. It deliberately covers only part of the full zero-carry complement: the kernel-checked example n=32,d=53 has zero carry but is outside Eset. Thus the new budget is not an exact small-carry sum disguised as an upper bound.

The production theorem computes n^2%d = (n%d)^2%d and (2*n)%d = (2*(n%d))%d. The quadratic-zone branch immediately has zero carry. For the minus-one branch, d>=2 gives square remainder 1 and width remainder d-2, whose sum is d-1; d=1 is handled separately. Therefore every excluded label has carry zero, including nonprime powers. Nonnegativity and disjointness with actual small events give

    smallCarry(n) <= psi(2*n) - E(n).

This is the strongest phase-aware small-carry bound proved in this checkpoint. It is generally weaker than the unproved central-binomial candidate, but it is proved for every n and removes certified positive mass from the previous prefix estimate.

## Repeated band and combined correction

Repeated large carry is bounded by the independent nonprime von Mangoldt mass

    Rband(n) = sum over nonprime d in (2*n,n^2] of vonMangoldt(d).

This excludes the low higher powers previously present in the separate global repeated-prefix estimate. For n>=3 the finite prefix split proves exactly

    psi(2*n) + Rband(n)
      = theta(2*n) + psi(n^2)-theta(n^2).

That identity is a private assembly lemma, not claimed as a new analytic estimate. It also prevents double counting an improvement already built into the combined 036 budget.

Reuse the 027 finite reciprocal higher-correction bound. The new production envelope is

    B_phase(n) = B_036(n) - E(n),
    C_ns(n) <= B_phase(n) <= B_036(n)    (n>=3).

Equivalently B_phase = psi(2*n)-E + Rband + reciprocalBudget. The formal comparison with 036 follows from nonnegativity of E. It is independent of Q and shell-prime existence. The production consumer proves

    Q + B_phase < log(cell) -> exists a prime in SquareCell n.

This is a sufficient provider, not an equivalence. The singleton factor-depth branch remains unchanged and closed.

## Retained-anchor diagnostics

The diagnostic independently enumerates prime-power labels and computes the exclusion predicate, exact small carry, nonprime band and hypothetical central budget. Excluded labels are explicitly checked to have zero carry. Q and previous coordinates are reused from the retained 036 diagnostic, with its SHA-256 recorded. Phase comparisons cover n=3..300 plus 1031 and 5000 (300 samples); the separate central conjecture test covers n=3..10000. All floating weights, signs and ratios are diagnostics, not proof premises.

| n | exact small approx | phase small upper approx | central log approx | exclusion E approx | B_phase approx | phase margin approx |
|---|---|---|---|---|---|---|
| 27 | 31.500600 | 35.350748 | 35.205035 | 18.104925 | 65.705845 | 22.477546 |
| 32 | 32.677332 | 44.836035 | 42.052281 | 17.501196 | 82.251409 | 22.189462 |
| 69 | 45.655748 | 100.386491 | 92.963081 | 36.340080 | 176.262186 | -11.231783 |
| 210 | 191.161211 | 330.788987 | 287.875302 | 85.087406 | 557.808660 | 64.626574 |
| 297 | 216.753367 | 471.411564 | 408.309773 | 116.100608 | 801.089736 | -52.888370 |
| 1031 | 882.867556 | 1810.610396 | 1425.227858 | 237.829369 | 2913.394288 | 254.171238 |
| 5000 | 4287.167674 | 9407.810858 | 6926.640819 | 605.585835 | 14622.451127 | 186.132458 |

At n=5000, the old 036 reduced margin was -419.453377. The proved exclusion removes about 605.585835 weighted units, giving a new diagnostic margin +186.132458. Thus the previous numerical correction deficit is removed at this anchor. B_phase still exceeds the exact correction substantially, so its entire slack is not removed. This positive floating sign is not presented as a kernel-checked strict criterion or new prime-existence range.

At n=210 the diagnostic margin becomes positive as well. At 69 and 297 it remains negative, despite positive exact old-ledger margins. These are failures of a sufficient envelope, not counterexamples to prime existence or to the proved correction bound. No unsampled global sign claim is made.

Q is more cleanly separated from the correction envelope at 5000, but it is not the sole outstanding issue globally: phase-envelope slack still matters at 69 and 297. The unproved central-binomial comparison would improve the small term further; it is kept visibly separate from the implemented alternative.

## Validation

The production module is [GnomonSmallCarryPhase.lean](../../../DkMath/NumberTheory/Legendre/GnomonSmallCarryPhase.lean), exported by the Legendre facade. Calibration proves the pointwise obstruction, proper partial exclusion, finite central bound at 27, and correction/comparison instances for all retained anchors. All ten public production declarations (four definitions and six theorems) are audited, with private helpers covered transitively. Only propext, Classical.choice and Quot.sound occur; no sorryAx, new axiom or forbidden proof construct is introduced.

All builds use LEAN_NUM_THREADS=2. Unified headers and immediate file markers are retained. The bounded artifact audit and git diff --check pass. Timings are incremental measurements; they do not imply clean-build performance gains.

| Build | Exit | Seconds | Peak RSS KiB | Swaps |
|---|---|---|---|---|
| focused | 0 | 16.569 | 7030356 | 0 |
| axiom-audit | 0 | 12.692 | 6730664 | 0 |
| facade | 0 | 12.805 | 6752176 | 0 |
| root | 0 | 13.536 | 7115124 | 0 |

The imported PacketCross:285 unused-variable warning remains. The root also reports pre-existing sorry declarations in ZsigmondyCyclotomicResearch:147, TriominoFLT:1919, TriominoCosmicBranchA:4187, GcdNextResearch:850 and CyclotomicPrincipalization:5389. These are outside the new public declaration audit. No repository-wide absence of sorry is claimed, and no memory failure occurred.

Artifacts: [source inventory](source-inventory-037.md), [coverage](logs/coverage-037.json), [diagnostics](logs/diagnostics-037.json), [focused](logs/focused-037.txt), [axiom audit](logs/axiom-audit-037.txt), [facade](logs/facade-037.txt), [root](logs/root-037.txt), and [artifact check](logs/artifact-check-037.txt). Reproduce the builds using checks/build-037.py with focused axiom-audit facade root, the numerical experiment using checks/diagnostics-037.py, and the artifact audit using checks/check-037.py.

## Next natural frontier and implementation proposal

Keep the singleton factor-depth campaign closed. The natural unresolved theorem is an aggregate weighted comparison with the central binomial coefficient, rather than a pointwise carry inclusion. A useful implementation proposal is a single finite weighted comparison receiver separating central-missing small coordinates from compensating central coordinates. Such a receiver must prove the compensation inequality independently; prime-power factorization alone does not establish it. The n=4,d=3 obstruction should remain a regression for any proposed comparison.

If that comparison remains inaccessible, seek a justified estimate for the remaining correction slack or for Q, with an explicit sum of the two slacks in the provider. The current fixed quadratic exclusion demonstrates a useful finite gain but proves no uniform saving sufficient for all n. Merely widening the residue zone or repeating finite sign checks would not resolve the global criterion. No design for Instruction 038, unproved analytic estimate or universal Legendre conclusion is introduced.
