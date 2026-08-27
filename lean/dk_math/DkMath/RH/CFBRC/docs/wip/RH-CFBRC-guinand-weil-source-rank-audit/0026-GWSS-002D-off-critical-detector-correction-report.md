# GWSS-002D off-critical detector correction report

Global objective:
zero configuration -> independent source -> off-critical detector -> arithmetic control -> centered-coordinate uniqueness -> `RiemannHypothesis`

Correction scope:
This report corrects the semantic gap in the initial 0024 implementation.  The
original theorem established `(z ^ 2).im ≠ 0` and a nonzero witness moment as
parallel conclusions.  The latter used occupied-orbit mass only, so it was an
occupancy witness rather than an off-critical detector.

## Corrected load-bearing bridge

For a target index `j0`, write

```text
q0 := pascalCenteredXiSquaredOrbitCoordinate R j0
m0 := pascalCenteredXiSquaredOrbitMassVec R j0.
```

`pascalCenteredXiOffCriticalOrbitScalarDetector_ne_zero` proves that

```text
((q0.im : ℂ) * m0) ≠ 0
```

using both the off-critical hypothesis `q0.im ≠ 0` and the occupied-mass
hypothesis `m0 ≠ 0`.

`exists_pascalCenteredXiMellin_offCritical_detector_coefficients` scales the
finite inverse-matrix extractor coefficients by `(q0.im : ℂ)` and proves the
exact moment identity

```text
∑ i, c i * momentVec i = (q0.im : ℂ) * m0.
```

`exists_pascalCenteredXiMellinOffCriticalWitness_of_full_rank_target` packages
these coefficients as an admissible finite Mellin weight and returns both the
exact detector identity and its nonzero consequence.

The repaired global theorem
`exists_pascalCenteredXiMellinOffCriticalWitness` transfers the identity to a
selected actual zero `z`:

```text
zeroMoment = ((z ^ 2).im : ℂ) *
  pascalCenteredXiSquaredOrbitMass R (z ^ 2).
```

Thus removing `z.re ≠ 0` removes the only route to the nonzero detector
factor.  The sanity theorem
`pascalCenteredXiCriticalOrbitScalarDetector_eq_zero` confirms that the
detector vanishes when an actual centered zero has `z.re = 0`.

## Classification and boundary

`OFF-CRITICAL-MELLIN-WITNESS-FOUND`

GWSS-002: CLOSED  
Next unresolved Gap: `MELLIN-WITNESS-ARITHMETIC-CONTROL-GAP`  
GWSS-003: authorized next but not started  
GWSS-004: not authorized

No prime-side estimate, top-horizontal removal, infinite-height limit, Weil
positivity, Li criterion, functional-equation source promotion, or RH
deduction is introduced.  The coefficient vector remains target-dependent and
finite inside the existing canonical Mellin family.

## Verification

- `lake build DkMath.RH.CFBRC.PascalCenteredXiMellinOffCriticalWitnessAudit`
  succeeds under `leanprover/lean4:v4.32.2`.
- `git diff --check` succeeds.
- The scalar detector, scaled extractor, local witness, and global witness
  theorem use only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `native_decide`, or new axiom is used.
