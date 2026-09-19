# FLT7TC-005R33 — Galois prime allocation and canonical common-factor normal form

## Scope

This report records the R33 implementation work under the attached
instruction.  The target is the actual ring-of-integers ideal allocation for
the square-refined packet, followed by the canonical `C = gcd R S` normal
form.  No successor, descent, or FLT7 closure is in scope.

## Initial audit

- R29 already supplies principal-ideal norm bridges, ideal coprimality, and
  distinct prime ideals above a common norm prime.
- R30 supplies `ncard = 3`, ramification index one, and inertia degree one for
  every common norm prime.
- R31 supplies the `q % 7 = 1 ∨ q % 7 = 6` support theorem.
- R32 supplies the generic `D1,D2,U,V` cube-defect normal form, but not the
  exact Galois allocation needed to identify the canonical common factor.
- The repository has the order-three `ringOfIntegersRotateEquiv` and the
  field-level `fieldRotateEquiv`; Mathlib's invariant-prime API exposes
  `Algebra.IsInvariant.orbit_eq_primesOver` and
  `Algebra.IsInvariant.exists_smul_of_under_eq`.

## Scratch / verification log

Further investigation and kernel-checking results are appended below.

### Sequential elaboration log

- The first target build showed that `Xor` is definitionally an
  `Or (a ∧ ¬ b) (b ∧ ¬ a)` in this toolchain; the implementation was changed
  to construct the two `Or` branches directly.
- The principal-ideal split was changed to an explicit `Set O` target so that
  the theorem statement does not rely on unfolding the local ideal wrappers.
- The allocation proof likewise uses `change` before applying the principal
  split, because `rw` does not unfold the wrapper definitions in that
  subgoal.
- The direct target build still reaches a deterministic `whnf` heartbeat
  limit while elaborating the principal-ideal theorem.  The local module
  heartbeat budget is currently `5_000_000`; no theorem was admitted and no
  placeholder was added.

### Completed implementation

- Added `gapSquareIdeal` and `quotientSquareIdeal` for the actual ring of
  integers `O`.
- Added a generic principal-span helper that maps the unit in
  `SevenRealCubicInt` to an `Oˣ` witness before applying the principal-ideal
  identity.
- Proved
  `span {rI} * span {sI} = span {(a : O)}` and transported the existing
  element coprimality to ideal coprimality.
- Proved `q ∣ a` from `q ∣ R` and `R*S = a^3`, then proved the exclusive
  allocation xor for every prime ideal above `(q)` using primality and ideal
  coprimality.
- Exported the production module through `DkMath.FLT.Seven` and added the
  requested API and axiom-audit test modules.

### Validation log

- `lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicPrimeAllocation.lean` — passed.
- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation` — passed.
- `lake build DkMath.FLT.Seven` — passed.
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicPrimeAllocationApi` — passed.
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicPrimeAllocationAxiom` — passed.
- The axiom audit reports only the standard `propext`, `Classical.choice`, and
  `Quot.sound` dependencies already present in the imported mathematical
  infrastructure.

## Current status

Part A and the Part B exclusive xor are kernel-checked. Parts C–M are not
claimed: the explicit Galois orbit, rotation/membership compatibility,
two-to-three forcing, cardinality, norm exponents, canonical `C,U,V` packet,
height refinement, and clash audit remain the next frontier. This is a
partial R33 checkpoint, not Outcome A or B.
