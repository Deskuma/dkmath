# FLT7TC-005R42 — Paired-core closure and the second deep-jet coordinate

## Scope

This report records the R42 implementation of the paired quotient-core route
from the current-provenance `C = 1` packet.  The target is to reuse the exact
R41 root `v`, restore the available depth-32 quotient remainder, and derive
the second projective-coordinate restriction.  No mod-343 brute-force trace
expansion, historical terminal packet, contradiction, successor, descent, or
FLT7 conclusion is in scope.

## Initial investigation

- R41 already exposes the exact correction `W = rho * v^7` and
  `thetaLinearModSeven v = 0`.
- The quotient-side canonical packet retains `cores_product_eq`, the
  scalarizing units, and the original depth-32 gap divisibility; the older
  quotient theorem intentionally exposes only axis depth three.
- The existing local-class layer contains the depth-32 canonical expansion
  and the theta-coordinate extraction APIs needed for the quotient remainder.
- The current implementation will be placed in a focused paired deep-jet
  module so the existing DeepJet module does not absorb the new quotient
  algebra.

The implementation and validation results will be appended below.

## R42 implementation progress

- Added the focused module `DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet`.
- Added the paired quotient model `directOrbitPairedDeepJetY` with the prescribed unit expression.
- Reduced the requested fixed unit identity to the literal unit equality
  `orbitUnit01Unit = directOrbitDeepJetThetaUnit ^ 4 * directOrbitDeepJetRho`.
- Verified the underlying `SevenRealCubicInt` identity by explicit coordinate normalization and completed the unit cancellation with group-level inverse-power normalization.
- The first focused builds reached the new module and exposed only the final inverse-power cancellation proof as the active error; that proof was repaired without changing the heavy theta-seventh-power module.
- The fixed unit identity now builds.  The proof uses the literal coordinate equality for the unit values and explicit cancellation after rewriting the inverse power with `inv_pow`.
- Added exact scalarized core identities for both sides.  In particular, the quotient core is the defined `Y` times `v^14`, and the gap core is the R41 `X` unit value times `u^14`.
- Added the exact paired product theorem.  It cancels the nonzero natural scalar `((u*v : ℕ) : SevenRealCubicInt)^14` from `cores_product_eq`; it does not use projective equality.
- The focused module builds successfully with no warnings after renaming intentionally unused hypothesis binders.
- Added the depth-32 canonical witness theorem with `eisensteinAxis ^ 31 ∣ d`.
- Added the neutral scalar divisibility helpers from `7 = eisensteinAxis^3 * thetaSevenUnit`; they use explicit unit inverse witnesses and no valuation-theoretic strengthening.
- Direct elaboration of the focused module now completes successfully after replacing the high-cost generic ring normalization with explicit power and associativity rewrites.

## Validation

- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet` passed.
- The public API check passed for the paired model, fixed unit identity, core scalarizations, paired product, depth-32 canonical witness, and the two neutral divisibility helpers.
- The axiom check passed.  The reported dependencies are the existing standard dependencies `propext`, `Classical.choice`, and `Quot.sound`.
- The R42 scratch checks passed for the fixed unit identity and the neutral axis-depth implications.
- `lake build DkMath.FLT.Seven` passed after adding the focused module to the public facade.
- `git diff --check` passed, and the new Lean implementation and validation files contain no `sorry`, `admit`, `axiom`, or `sorryAx` tokens.

The implemented endpoint remains the focused algebraic/core layer recorded in
the roadmap.  The deeper mod-49/mod-343 coordinate extraction, projective-root
discharge, contradiction, successor, descent, and FLT7 conclusion remain
outside this implementation result.
