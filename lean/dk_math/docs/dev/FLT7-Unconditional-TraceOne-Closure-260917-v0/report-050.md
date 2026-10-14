# FLT7TC-005R44 — Square-jet closure and 49th-power correction

## Scope and initial findings

This report records the R44 implementation work from `instruction-050.md`.
The current module is the R43 paired DeepJet module.  R43 already proves the
same-root quotient transport, the depth-32 quotient remainder, and source-root
mod-49 scalarity.

## Implementation progress

- Added the R44 coordinate and remainder layer to
  `PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean`.
- Part A is proved in the model ring by an explicit witness for
  `49 ∣ p.rho - ofInt (thetaConstInt p.rho)`.
- Part B proves scalarity of `p.rho^6` modulo `49` and transports both its
  linear and square theta coordinates.
- Part C cancels `thetaSevenUnit` from the depth-32 remainder using its unit
  inverse, yielding `theta^32 ∣ Z^7 - p.rho^6`.
- Part D weakens to theta depth six, applies the existing `axis^6 -> 49`
  helper, and proves `49 ∣ thetaSquareInt (Z^7)`.
- Part E proves `¬ 7 ∣ h.v` from the quotient-square-root axis exclusion.
- Part F proves nonzero theta constant and zero theta-linear coordinate for
  `Z`.
- Part G uses the neutral square jet modulo `49` to prove
  `thetaSquareModSeven Z = 0`.
- Parts H and I transport the square-coordinate vanishing from `Z` to
  `v⁻¹` and then to `v`.
- Part J proves `projectiveLog (Additive.ofMul v) = 0` and extracts
  `v = w^7`.
- Part K exposes the provenance-preserving wrapper with
  `W = rho * w^49` and `quotientCore = thetaSevenUnit * Z^7`.

The implementation uses no new descent or contradiction theorem.  The
endpoint is therefore Outcome B at the algebraic wrapper level; the R44
clash audit remains negative/conservative.

## Validation

- Focused module build passed:
  `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet`.
- Facade build passed:
  `lake build DkMath.FLT.Seven`.
- API check passed:
  `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetApi`.
- Axiom audit passed:
  `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetAxiom`.
  The decisive declarations report only the repository's existing
  `propext`, `Classical.choice`, and `Quot.sound` dependencies.
- R44 scratch verification passed with
  `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR44Scratch.lean`.
- Forbidden-construct scans on the R44 source/API/axiom/scratch files found no
  `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.
- `git diff --check` passed.

## Report questions

1. Yes: `49 | p.rho - ofInt(thetaConstInt p.rho)` is proved in the model ring
   with an explicit coordinate witness.
2. Yes: both linear and square coordinates of `p.rho^6` are divisible by 49.
3. Yes: `thetaSevenUnit` is cancelled from the depth-32 remainder.
4. Yes: `49 | thetaSquareInt (Z^7)` is kernel-checked.
5. Yes: `7 ∤ h.v` follows from the quotient-square-root axis exclusion.
6. Yes: the theta constant of `Z` is nonzero modulo seven and its theta-linear
   coordinate is zero.
7. Yes: the neutral square jet forces `thetaSquareModSeven Z = 0`.
8. Yes: the result is transported to `v⁻¹` and then to `v`.
9. Yes: `projectiveLog v = 0` is kernel-checked.
10. Yes: `v = w^7` is kernel-checked.
11. Yes: the wrapper exposes `W = rho0 * w^49`.
12. No independent checked theorem produced an actual contradiction.  The
    implementation therefore stops at Outcome B and does not claim FLT7
    closure.

## Part L clash audit

The existing identity
`X = directOrbitSquareTwistCoeff0 * eta^14` combined with the normalization
of `W` leaves the factor `rho * w^49` after removing the visibly square
factors `thetaSevenUnit^n` (the exponent is even) and `eta^14`.  Since `rho`
and the odd power `w^49` are not established squares by the checked API,
`directOrbit_squareTwist_coeff0_not_square` does not apply.

The existing mixed-sign lemmas rule out only the all-positive and all-negative
embedding patterns for the coefficient-zero twist.  The odd 49th power does
not fix a sign pattern, and no checked theorem in this scope identifies the
remaining signs, so no sign contradiction is available.  No new binary cubic,
Thue, or unit-equation argument was started.
