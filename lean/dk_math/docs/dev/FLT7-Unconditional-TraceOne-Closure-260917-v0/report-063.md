# FLT7TC-005R57 — Thomas `F5` internal `SevenRealCubic` bridge

## Initial scope and boundary

This report records the implementation of `instruction-063.md`.  The
production target is a new focused module,
`DkMath/FLT/Seven/SevenRealCubicThomasUnit.lean`; the existing real-root
approximation module is not imported by that production module.

The exact internal candidate is

```text
thomasLambda = alpha^2 + alpha - 1 = (-1, 1, 1)
```

and the intended route is the finite, kernel-checked bridge

```text
F5(R,S) = norm (R - thomasLambda*S)
deep S -> ThetaNilpotentDepth 8 -> inverse-depth seventh-root extraction.
```

No closure claim is made at this stage.  In particular, the Thomas finite
denominator bound from R56 remains external to this module.

## Existing APIs inspected

- `SevenRealCubicInt.norm` is multiplicative and the cyclic conjugate product
  theorem `mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm` is public.
- `SevenRealCubicInt` has explicit coordinate multiplication and the relation
  `alpha_cube`.
- `ofThetaCoordinates`, `thetaConstInt`, `thetaLinearInt`, and
  `thetaSquareInt` are public exact coordinate APIs.
- `projectiveLog`, `projectiveLog_apply`, and
  `unit_isSeventhPower_iff_projectiveLog_eq_zero` are available from the unit
  class module.
- `ThetaNilpotentDepth`, `thetaNilpotentDepth_mono`, and
  `unit_is_pow_seven_pow_of_inverse_depth` are available from the finite-depth
  module.
- `F5`, `Q5`, `T5`, `sigma5`, and their invariance theorems are available from
  `SevenRealCubicHighDepthFive`.
- The generic norm-one inverse proof is currently private in
  `SevenRealCubicSourcePlaneNormSeven`; R57 will use the smallest neutral local
  version if no public theorem is suitable.

## Incremental ledger

| stage | result |
|---|---|
| source/API inspection | complete |
| production module | complete |
| scratch coordinate and axiom checks | complete |
| focused Lean build | complete |
| report and warning audit | complete |

## Implemented exact bridge

The new production module implements Parts A--D of the instruction as exact
integer identities:

- `thomasLambda` is definitionally based on `alpha^2 + alpha - 1`, with
  coordinates `(-1, 1, 1)`.
- Its cubic equation, norm-one identity, explicit unit lift, theta-coordinate
  form `11 + 7*theta + theta^2`, and unit relation
  `thomasLambda^2 * (1 + alpha) = alpha^6` are proved.
- The projective logarithm is computed exactly as `(0, 2)`.
- `thomasPlaneElement R S = R - thomasLambda*S` satisfies
  `norm (thomasPlaneElement R S) = F5 R S` and the theta-plane relation
  `thetaLinearInt = 7 * thetaSquareInt`.
- `F5 R S = 1` produces a norm-one unit lift without importing the real-root
  approximation module.

Part E is implemented by exposing the theta-linear and theta-square product
 formulas.  Together with the unit constant-coordinate coprimality, these
 formulas prove that `ThetaNilpotentDepth n` is preserved by unit inversion.

Part F normalizes a deep `S` input through the three `sigma5` branches while
 preserving `F5`, `Q5`, and `T5`, and returns the branch with `7^8 ∣ S'` and
 `7 ∤ R'`.  Part G then proves the normalized Thomas unit has depth eight,
 its inverse has the same depth, it is a `7^8`-th power in the unit group, and
 its projective logarithm is zero.

Part H adds the exact seventh-root return equation.  For a unit `t` whose
 seventh power lies on the Thomas plane, the equation reduces to
 `seventhThetaLinearQuotient = 7 * seventhThetaSquareQuotient`; the coprime
 factor theorem then proves `7 ∣ thetaLinearInt t`.

## Verification

The focused command

```text
lake build DkMath.FLT.Seven.SevenRealCubicThomasUnit
```

completed successfully with 9210 jobs.  The new production module emits no
local tactic or declaration warnings after the warning cleanup; warnings
replayed from unrelated existing dependencies remain outside this target.

The scratch audit
`scratch-063-thomas-unit-audit.lean` also completed successfully.  Its
`#print axioms` checks report only the ordinary kernel/library axioms
`propext`, `Classical.choice`, and `Quot.sound` for the checked declarations;
no external theorem axiom is introduced by this module.

## R45/R56 comparison and boundary

R45 supplies the earlier real-cubic structural route.  R57 isolates the
Thomas `F5` plane and supplies the missing finite unit-coordinate bridge:
deep-S normalization, inverse-depth preservation, and the exact first
seventh-root divisibility condition.  It does not construct the exact
successor needed for a strict descent.

The R56 external statement
`FixedThomasSixBound: F5 = 1 -> |S| < 5764801` is retained as a documented
frontier and is not assumed as an internal theorem here.  Consequently this
checkpoint records a finite unconditional bridge only; it does not claim a
Thomas descent, a real-sector elimination, or FLT closure.

## Current mathematical endpoint

The intended endpoint is the exact theorem that a normalized deep-S Thomas
plane unit has an inverse-depth-eight representation as a `7^8`-th power and
has trivial projective logarithm.  A strict successor/descent or an FLT
closure theorem is outside the checkpoint unless an exact integer successor is
constructed and kernel-checked.
