# FLT7TC-005R27 — Square-refined twisted signature audit

## Scope

This report records the implementation of `instruction-033.md`. The
construction stays at the current `DirectOrbitSquareRefinementPacket` level.
It does not introduce a global unit-group modulo-squares classification and
does not turn the result into an FLT7 contradiction.

## Production implementation

Added:

- `DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean`
- facade export in `DkMath/FLT/Seven.lean`
- API audit:
  `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionApi.lean`
- axiom audit:
  `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionAxiom.lean`
- reusable scratch examples:
  `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionScratch.lean`

The production API defines the three square-refined unit coefficients
`directOrbitSquareTwistCoeff0/1/2`. It proves:

1. The exact identity
   `c0 * (r0^7)^2 + c1 * (r1^7)^2 + c2 * (r2^7)^2 = 0`, with all unit
   factors retained.
2. The exponent `32 + 42*k` is even, its half is explicit, and the pair-axis
   factor at that exponent is a square.
3. The coefficient transports `c1 = P^e * rotate(c0)` and
   `c2 = P^e * rotate(c1)`.
4. The projective classes remain `(2,4)`, `(2,2)`, `(2,5)`.
5. The three square-root variables are nonzero, using real embedding
   injectivity and square-refinement norm positivity.
6. `c0` cannot be a square unit: square transport makes all three terms in
   the exact identity strictly positive under the real embedding.
7. The signed norm is fixed exactly:
   `norm (c0 : SevenRealCubicInt) = 1`.
8. The cyclic real signature cannot be totally positive or totally negative.
   The positive case contradicts the square-weighted identity after
   transport; the negative case contradicts `realEval_cyclic_norm` together
   with `norm c0 = 1`.

## Validation

Sequential Lean checks completed successfully:

- `lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean`
- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareTwistObstruction`
- `lake build DkMath.FLT.Seven`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionApi`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionAxiom`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionScratch`

The axiom audit for the new declarations reports only the ordinary
`propext`, `Classical.choice`, and `Quot.sound` dependencies inherited from
the existing algebraic infrastructure. No `sorry`, `admit`, `unsafe`, or
new axiom declaration was added.

## Mathematical status

The checked result is a structural square-refined twisted obstruction and a
mixed-sign audit at the current direct-orbit level. It does not supply a
theorem forcing `c0` to be square or totally positive, and therefore does not
close the remaining FLT7 successor/descent route.

## Outcome

**Outcome B — SQUARE-WEIGHTED STATE GREEN; `c0` PROVED NON-SQUARE WITH MIXED
REAL SIGNATURE; POWER-REFINEMENT ROUTE FROZEN.**

The seventh-power gauge normalization is obstructed by R24/R25, ordinary
homogeneous restart is obstructed by R25, and the square-gauge normalization
is obstructed here. No FLT7 contradiction is claimed.
