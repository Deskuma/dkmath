# FLT7TC-005R28 — Square-root scalar split and Galois prime-support audit

## Scope and initial audit

This report records the implementation of `instruction-034.md`. The target is
the current `DirectOrbitSquareRefinementPacket` from R26/R27. The checkpoint
freezes all further power refinement and treats the two R26 square roots as
the element-level factors to be audited.

The existing packet already provides:

- coprimality of `gapRoot` and `quotientRoot`;
- unit-times-square equations for both roots;
- an explicit unit-times-square equation for their product;
- the norm identity `R * S = a^3`, the positive `R` bound, and `R^2 < a`.

The first production slice therefore targets the stable square-root
coprimality theorem, the scalar associated/unit split, positivity of the
second norm, and the theta-unit statements. The ideal-factorization and
cyclic splitting parts are kept as a separate audit boundary until a neutral
Dedekind/Galois bridge is available for the current packet.

## API search findings

Mathlib exposes `Associated.pow_iff` for an integrally closed domain. The
real-cubic number-field layer also supplies the model-to-ring-of-integers
identification and the principal-ideal infrastructure. The current direct
packet, however, is expressed in the explicit `SevenRealCubicInt` model, so
the element-level support statements can be proved without introducing a
historical routing packet.

The existing R26 theorem is deliberately reused for `R * S = a^3`; no
competing norm proof surface is introduced.

## Status before implementation

The current theorem frontier is expected to be:

- A–D: current element-level square-root and theta-unit API;
- E–G: require a neutral prime-ideal norm/factorization bridge for the two
  coprime algebraic factors;
- H–J: audit/report boundary unless that bridge is established.

No claim of `Nat.Coprime R S`, `C = 1`, a successor/descent contradiction, or
unconditional FLT7 closure is in scope.

## Production result

Added `DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquarePrimeSupport.lean`
and exported it from the public `DkMath.FLT.Seven` facade. The checked API
now contains:

1. `directOrbitSquareRefinement_squareRoots_isCoprime`, obtained by removing
   the two unit factors and applying `IsCoprime.pow_iff` at exponent two.
2. `directOrbitSquareRefinement_squareRoots_associated_scalar`, obtained by
   first proving association of the two squares and applying
   `Associated.pow_iff` in the integrally closed real-cubic integer ring.
3. `directOrbitSquareRefinement_squareRoots_unit_split`, giving the explicit
   equation `r * s = unit * (a : O)`.
4. `directOrbitSquareRefinement_squareRoots_norm_product`, which re-exports
   the existing R26 `R * S = a^3` theorem, plus positivity of the second
   norm factor. The existing `0 < R` and `R^2 < a` theorems remain the
   source of those facts.
5. Element-level theta-unit theorems for both square roots. The quotient
   proof uses a small generic unit-times-power helper and does not import a
   historical routing packet.

The explicit scalar witness is constructed from the associated-square
witness using a unit inverse at the `Units` level; no real-embedding square
cancellation is used.

## Prime-support boundary

The current implementation stops at the mandatory element-level theta-unit
facts. The direct packet has no neutral theorem yet converting `7 ∣
natAbs (norm u)` into `eisensteinAxis ∣ u` for the explicit cubic model.
More importantly, Parts E–G need a current Dedekind ideal-factorization
bridge: from a rational norm prime one must construct prime ideals above it,
prove that the two ideals are distinct using element coprimality, and then
invoke the cyclic degree-three splitting theorem. No theorem is added that
would silently replace this ideal step with `q ∣ u`.

Accordingly, no `Nat.Coprime R S`, `7 ∤ R`, `7 ∤ S`, gcd support theorem,
`q ≡ ±1 (mod 7)` statement, `C = 1`, or FLT7 contradiction is claimed by
this checkpoint.

## Validation

Sequential checks completed successfully:

- `lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquarePrimeSupport.lean`
- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquarePrimeSupport`
- `lake build DkMath.FLT.Seven`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportApi`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportAxiom`
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportScratch`

The new declaration axiom audit reports only `[propext, Classical.choice,
Quot.sound]`. No `sorry`, `admit`, `unsafe`, or new axiom declaration was
added.

## Outcome

**Outcome C — ELEMENT-LEVEL SQUARE-ROOT SCALAR SPLIT GREEN; PRIME-IDEAL
SUPPORT BRIDGE REMAINS OPEN.**

The R28 implementation makes the coprime algebraic factorization explicit
and records the norm/product compatibility without making a forbidden norm
coprimality inference. The missing prime-ideal/Galois bridge is the next
honest frontier; no successor, descent, or unconditional FLT7 closure is
claimed.
