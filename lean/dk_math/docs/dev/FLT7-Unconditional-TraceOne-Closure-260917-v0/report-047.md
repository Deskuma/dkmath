# FLT7TC-005R41 — Deep-jet invariant closure and constant-coordinate elimination

## Scope

This report records the R41 implementation and its focused verification. The
target is the global invariant closure of the normalized unit `W`, the exact
seventh-power correction `W = rho * v^7`, and the first deeper restriction
`thetaLinearModSeven v = 0`. The unrestricted constant-coordinate mod-49
expansion is excluded by the R41 instruction.

## Initial investigation

- R40 already provides the weighted trace, trace plane, calibrated `rho`, and
  neutral linear/square mod-49 jets.
- Existing unit-class APIs provide `projectiveLog_apply`, seventh-power log
  vanishing, and the zero-log seventh-power criterion.
- Existing square-twist APIs provide the coefficient-zero norm and projective
  class.

The implementation and validation results will be appended below.

## Implementation

- Added the R41 Part A invariants for `directOrbitDeepJetThetaUnit`: its
  value is `thetaSevenUnit`, its norm is `-1`, and its projective log is
  `(5, 1)`.
- Added the Part B/C invariants for `directOrbitDeepJetXUnit`: norm `1` and
  projective log `(2, 4)`.
- Added the Part D invariants for the transport exponent: it is even and its
  reduction in `ZMod 7` is `3`; consequently `directOrbitDeepJetWUnit` has
  norm `1` and projective log `(1, 1)`.
- Added the Part E exact correction theorem
  `W = directOrbitDeepJetRho * v ^ 7`, using the existing projective-log
  seventh-power criterion and preserving the requested orientation.
- Added `directOrbitTracePlaneForm` and repackaged the existing trace-plane
  result.  The direct coordinate proof establishes the exact Part G identity
  `Phi (rho * Y) = -3 * thetaLinearInt Y + 14 * thetaSquareInt Y`; the
  constant coordinate cancels identically.
- Added the Part H congruence using only
  `thetaLinear_pow_seven_mod49_neutral` and
  `thetaSquare_pow_seven_mod49_neutral`:
  `49 | Phi (rho * v^7) + 21 * B * A^6`.
- Added the Part I nonvanishing and arithmetic reduction.  From the trace
  plane this gives `49 | 21 * B * A^6`, then `7 | B`, and finally the exposed
  endpoint `thetaLinearModSeven v = 0`.
- Added a provenance-preserving wrapper that combines the normalized trace,
  the exact correction, and the root restriction into one existential
  conclusion for the original canonical common-factor packet.
- Updated the public API checks, the axiom audit, the reusable R41 scratch
  check file, and the roadmap entry.

## Validation

The following checks passed sequentially:

- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet`
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetApi.lean`
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetAxiom.lean`
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetR41Scratch.lean`
- `lake build DkMath.FLT.Seven`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetApi`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetAxiom`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetR41Scratch`
- `git diff --check` and new-file `git diff --no-index --check` checks
- forbidden-construct scan over the changed Lean and verification files

The axiom audit for the R41 declarations reports only the repository's
existing `[propext, Classical.choice, Quot.sound]` dependencies.  No new
`sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom` was introduced.

The Part K audit remains a boundary audit: the checked R41 data supplies the
first root restriction but does not supply an independent clash with the
remaining second projective coordinate.  No deeper jet, quotient-scalar
identification, successor/descent claim, contradiction, or FLT7 conclusion
was added.

## Outcome

Outcome B: all requested global invariants, the exact seventh-power correction,
the constant-coordinate elimination, the focused mod-49 transport, and
`thetaLinearModSeven v = 0` are kernel-checked; the remaining root class is
one-dimensional `(0, lambda)` and is not a contradiction.
