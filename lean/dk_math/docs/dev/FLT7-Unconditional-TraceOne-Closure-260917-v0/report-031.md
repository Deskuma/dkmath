# FLT7TC-005R25 — Implementation report

## Scope

This report records the implementation and verification work for
`instruction-031.md`.  The checkpoint tests the ordinary homogeneous
seventh-power restart on the R22/R23 transported twisted state.  It is a
negative structural result; it does not assert a contradiction of FLT7.

## Scratch verification

- `directOrbitPairAxisUnitOne` has scalar theta residue `4`, obtained from
  `pairAxisUnit_thetaResidue_eq_pairPhase` and `pairPhase_one_val`.
- The exponent calculation uses the multiplicative period six:
  `32 + 42*k = 2 + 6*(5 + 7*k)`, hence
  `(4 : ZMod 7)^(32 + 42*k) = 2`.  This is deliberately separate from the
  projective-log reduction modulo seven, which gives exponent class `4`.
- For every `DirectOrbitPowerSplitPacket s`, direct residue calculation gives
  `thetaResidue (coeff1 * coeff0⁻¹) = 2`.  The proof uses the rotation residue
  identity and unit inverse cancellation, not projectiveLog.
- Therefore `coeff1 - coeff0` has nonzero theta residue and is not divisible by
  `eisensteinAxis`.
- The rotated root gap has zero theta residue, so
  `eisensteinAxis ∣ rotateEquiv s.gapRoot - s.gapRoot`.  The packet's
  `¬eisensteinAxis ∣ s.gapRoot` and primality of `eisensteinAxis` imply
  `¬eisensteinAxis ∣ s.gapRoot^7`.
- The weighted remainder
  `(coeff1 - coeff0) * s.gapRoot^7` is therefore not theta-divisible.
- Applying the exact weighted difference identity and the ordinary
  seventh-power factorization to the first summand shows that divisibility of
  the full weighted difference by the root gap would force theta-divisibility
  of the remainder.  This proves
  `directOrbit_weighted_difference_not_gap_dvd`.
- The explicit restart corollary
  `directOrbit_no_ordinary_homogeneous_restart` rules out a quotient `q` with
  the weighted difference equal to `(rotateEquiv gapRoot - gapRoot) * q`.
- The existing R24 projective class theorem also exposes the optional unit
  gauge obstruction `directOrbit_twistedCoeff1_not_unit_gauge`.

Sequential validation completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicWeightedGapObstruction
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicWeightedGapObstructionApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicWeightedGapObstructionAxiom
```

The axiom audit for the new declarations reports only
`[propext, Classical.choice, Quot.sound]`.  The new production file contains
no `sorry`, `admit`, `unsafe`, or project `axiom` declaration.

## Checkpoint answers

1. Part A: proved, `thetaResidue P = 4`.
2. Part B: proved using multiplicative period six; kept distinct from the
   projective-log modulus-seven calculation.
3. Part C: proved for every current packet, with scalar ratio residue `2`.
4. Part D: proved; the coefficient difference is a theta-unit.
5. Part E: proved; the successor root gap is theta-divisible while the root
   seventh power is not.
6. Part F: proved; the weighted remainder is not theta-divisible.
7. Part G: proved; the full weighted difference is not divisible by the
   ordinary root gap.
8. Part H: proved; no ordinary homogeneous quotient restart exists.
9. Part I: exposed; no seventh-power unit gauge normalizes the first pair.
10. Part J: the ordinary homogeneous-gap extraction route is not
    self-similar.  The next choices remain a genuinely weighted/twisted kernel
    or a different successor notion; neither is selected here.

## Outcome

**Outcome B — WEIGHTED GAP OBSTRUCTION GREEN; ORDINARY SELF-SIMILARITY
FROZEN.**

The failure is a structural obstruction, not an FLT7 contradiction.  No
successor recursion, iterable descent, historical receiver, or seventh-root
extension was introduced.
