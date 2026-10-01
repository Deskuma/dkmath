# FLT7TC-005R43 — Paired deep-jet transport and projective-root closure

## Scope and initial findings

This report records the R43 implementation work from `instruction-049.md`.
The target is the same R41 seventh-root unit `v`; no fresh seventh root is to
be introduced.  The implementation continues in the focused R42 paired
DeepJet module.

The existing DeepJet module already provides the R41 correction
`W = rho0 * v^7`, the linear mod-7 restriction on `v`, the projective-log
criterion for seventh powers, and the explicit theta-coordinate product laws.
The existing local-class module provides the canonical quotient expansion and
the source-root theta-coordinate mod-7 facts.  The new work therefore starts
with the same-v quotient transport and the exact depth-32 remainder.

## Implementation progress

- Added the same-`v` transport theorem
  `directOrbitPairedDeepJet_same_v_unit_identity`, using the R41 correction
  `W = rho0 * v^7` without introducing a fresh root.
- Added `directOrbitPairedDeepJetZ` and the exact quotient identity
  `quotientCore = thetaSevenUnit * Z^7`.
- Added the explicit depth-32 remainder theorem
  `directOrbitPairedDeepJet_quotientCore_sub_leading_axis_pow32_dvd`.
- Added the exact rotation-gap theta-coordinate formulas and the neutral
  `ofInt` scalar-to-coordinate divisibility transport.
- Added the source-root mod-49 scalarity theorem.  It weakens the existing
  depth-32 gap divisibility to `axis^9`, transports it to `343`, and derives
  `49 | thetaLinearInt rho` and `49 | thetaSquareInt rho`.
- Added the R43 API and axiom checks and a focused R43 scratch file.

The current checked frontier is Outcome C: the same-`v` quotient transport,
the depth-32 remainder, rotation formulas, and source-root mod-49 scalarity
are green.  The square-coordinate jet on `Z` and the subsequent projective
root closure remain for a later checkpoint; no contradiction or FLT7 claim is
made here.

## Validation

- `lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean` — passed.
- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet` — passed.
- `lake build DkMath.FLT.Seven` — passed.
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetApi` — passed.
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetAxiom` — passed; the audited declarations use only the existing Lean/Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR43Scratch.lean` — passed.
- `git diff --check` — passed.
- Forbidden-source scan over the R43 source/API/axiom/scratch files — no matches.
