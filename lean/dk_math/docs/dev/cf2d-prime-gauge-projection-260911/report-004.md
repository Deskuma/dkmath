# CPG-V1-004 — paired Goldbach phase refinement

Date: 2026-09-12  
Status: complete

## Implemented API

Added the production module
[GoldbachRefinement.lean](../../../DkMath/NumberTheory/PrimeGauge/GoldbachRefinement.lean):

```lean
DkMath.NumberTheory.PrimeGauge.goldbachLeftReservedChildIndices
DkMath.NumberTheory.PrimeGauge.goldbachRightReservedChildIndices
DkMath.NumberTheory.PrimeGauge.pairedReservedChildIndices
DkMath.NumberTheory.PrimeGauge.pairedSurvivingChildIndices
DkMath.NumberTheory.PrimeGauge.existsUnique_leftReservedChild
DkMath.NumberTheory.PrimeGauge.existsUnique_rightReservedChild
DkMath.NumberTheory.PrimeGauge.leftReservedChild_ne_rightReservedChild_of_not_dvd_two_center
DkMath.NumberTheory.PrimeGauge.pairedReservedChildIndices_card_eq_two
DkMath.NumberTheory.PrimeGauge.pairedSurvivingChildIndices_card_eq_q_sub_two
```

The left and right reserved sets are the bounded child indices whose `ZMod q`
coordinates equal `+n` and `-n`, respectively. Their existence and
uniqueness factor through CPG-V1-004a's arbitrary-target child theorem.
When `¬ q ∣ 2 * n`, the two target classes are distinct by the existing
Goldbach residue theorem, so the two reserved indices are distinct. The
reserved union therefore has cardinality `2`, and its complement in the `q`
bounded child indices has cardinality `q - 2`.

Added the focused regression
[PrimeGaugeGoldbachRefinement.lean](../../../DkMathTest/NumberTheory/PrimeGaugeGoldbachRefinement.lean).
It checks the two targets and both cardinality results for the concrete world
`{2, 3, 5}`, fresh `q = 7`, parent `r = 1`, and center `n = 10`.

## Scope boundary

- The surviving set is the complement of the two raw `ZMod q` phase targets on
  a bounded child fiber.
- It is not an interval-level Goldbach survivor theorem: left natural
  subtraction requires a separate `child ≤ n` hypothesis, and proper endpoint
  exceptions remain outside this module.
- No child is asserted to be prime, and no short-interval, universal escape,
  Strong Goldbach, or continuum claim is made.
- The `q - 2` cardinality is a finite phase refinement and is not counted as
  strict information gain before the CPG-V1-007 audit.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.NumberTheory.PrimeGauge.GoldbachRefinement \
  DkMathTest.NumberTheory.PrimeGaugeGoldbachRefinement
```

Result: exit 0, `Build completed successfully (8705 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-004-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the new production/test files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for the two cardinality theorems: only `propext`,
  `Classical.choice`, and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-004` is complete. The next checkpoint is `CPG-V1-005`, the
parent-independent relative shape theorem. It must use the phase-level child
targets without silently converting them into interval-level proper Goldbach
obstructions.

