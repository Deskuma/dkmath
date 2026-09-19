# FLT7TC-005R26 — Implementation report

## Scope

This report records the implementation and verification work for
`instruction-032.md`.  The checkpoint refines the current
`DirectOrbitPowerSplitPacket` at the element level.  It does not restart the
R25 ordinary homogeneous-gap route and does not claim a successor state,
descent, or an FLT7 contradiction.

## Scratch verification

- The first scratch theorem checked that core coprimality can be transported
  through the displayed unit factors and then recovered from the seventh
  powers with `isCoprime_mul_units_left` and `IsCoprime.pow_iff`.
- The production proof isolates
  `delta = orbitUnit01Unit * (gapUnit * quotientUnit)⁻¹`.  The R24 classes
  reduce its projective logarithm to `(0,0)` in `(ZMod 7)^2`, and the existing
  unit-class theorem supplies `delta = w^7`.
- Seventh powers are not cancelled by an unqualified domain tactic.  The
  equality is transported through the existing real embedding; odd seventh
  powers are injective in `ℝ`, and the model-to-ring-of-integers map and
  coefficient embedding are used to return to `SevenRealCubicInt`.
- The exponent-2 extraction reuses
  `exists_associated_pow_of_associated_pow_mul`; no new factorization engine
  was added.
- The norm layer uses `natAbs(norm unit)=1`, the existing complement identity
  `G*Q=a^6`, and natural-number power injectivity to obtain `R*S=a^3`.
  The strict R21 bound is transported as `0<R` and `R^2<a`.

## Sequential validation

The following validations are run one at a time:

```text
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareRefinementScratch
lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquareRefinement.lean
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareRefinement
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareRefinementApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareRefinementAxiom
```

The scratch theorem and production module both elaborate successfully.
The facade, API surface, and axiom-audit modules also build successfully; the
new declarations use only `[propext, Classical.choice, Quot.sound]`.

## Checkpoint answers

1. Part A: proved on every current power-split packet; no norm coprimality is
   used.
2. Part B: proved unconditionally from the R24 projective classes.
3. Part C: proved as a literal root-product equation, with the seventh-power
   cancellation checked through the real embedding.
4. Part D: proved with the existing generic associated-power splitter at
   exponent two.
5. Part E: packaged as `DirectOrbitSquareRefinementPacket` with explicit
   units and unit-times-square equations.
6. Part F: proved `G=R^2`, `Q=S^2`, `R*S=a^3`, `0<R`, and `R^2<a`.
7. Part G: no successor or descent construction was introduced; the square
   refinement is recorded as a current-packet algebraic refinement only.
8. Part H: no norm-gcd inference is made from element coprimality.
9. Part I: no historical packet or weighted quotient is imported.
10. Part J: the new data does not close FLT7; the remaining successor bridge
    is deliberately left open.

## Outcome

**Outcome A — COPRIME SQUARE REFINEMENT GREEN; SUCCESSOR BRIDGE OPEN.**

The current smaller-norm packet admits the requested element-level square
refinement and clean norm consequences.  R25 remains frozen, and no
unconditional FLT7 closure is claimed.
