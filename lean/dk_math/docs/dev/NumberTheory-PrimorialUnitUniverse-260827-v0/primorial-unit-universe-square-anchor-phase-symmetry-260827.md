# PUU-L016 — Square-Anchor Phase Symmetry

## Scope

PUU-L015 showed that the global old-escape provider is equivalent to
Legendre's conjecture.  This checkpoint therefore moves back to the
provider-side wheel geometry and records an invariant that does not use the
Legendre application layer.

The implementation is
`DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhase.lean`, imported by
`DkMath.NumberTheory.PrimorialUniverse`.  It imports only
`DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit` and does not import
`DkMath.NumberTheory.Legendre`.

## Phase relation

The named relation

```lean
def SameSquareAnchorPhase (S : Finset ℕ) (a b : ℕ) : Prop :=
  squareAnchorWheelProjection S a =
    squareAnchorWheelProjection S b
```

is equipped with reflexivity, symmetry, and transitivity theorems.  This gives
a small public API for later phase-fiber or CRT investigations without adding
any classification of those fibers at this checkpoint.

## Period and reflection

The theorem

```lean
sameSquareAnchorPhase_add_mul_period
```

is a direct wrapper around PUU-L010's
`squareAnchorWheelProjection_add_mul_period`: translating an anchor by
`k * finitePrimeBasisProduct S` preserves its square phase.

The central new theorem is

```lean
squareAnchorPhase_reflect
```

which proves, for `n ≤ M` and `M = finitePrimeBasisProduct S`, that `n` and
`M - n` have the same square phase.  The proof handles both arithmetic cases
`2*n ≤ M` and `M ≤ 2*n`, so the endpoints `n = 0` and `n = M` are included.

## Fixed-offset and reservation invariance

For every fixed offset `r`, the theorem

```lean
squareShellProjection_eq_of_sameAnchorPhase
```

shows that same phase gives the same projected shell coordinate.  Using the
canonical projection/reservation equivalence from PUU-L010, the module then
proves:

```lean
reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase
not_reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase
```

Thus equal square-anchor phase implies identical finite-basis reservation and
non-reservation patterns for every shell offset.  The specialized theorem

```lean
reservedByPrimeBasis_square_reflect_iff
```

states the same result for the reflection `n ↔ M - n`.

This is an independent provider-side invariant: it concerns finite wheel
coordinates and reservation patterns, not the existence of an unreserved
square-shell point.

## Visible `{2, 3}`, `M = 6` regression

The theorem `squareAnchorPhase_two_three_reflection_regression` records:

```text
finitePrimeBasisProduct {2, 3} = 6
SameSquareAnchorPhase {2, 3} 1 5
SameSquareAnchorPhase {2, 3} 2 4
```

corresponding to `1^2 ≡ 5^2 ≡ 1 (mod 6)` and
`2^2 ≡ 4^2 ≡ 4 (mod 6)`.  The theorem
`reservedByPrimeBasis_two_three_reflection_regression` additionally checks
reservation-pattern preservation for offsets `r = 1` and `r = 2`.

## Boundary and next step

This checkpoint does not state or prove `escapingSquareOffsets`,
`SuccessorOldEscapeCriterion`, Legendre's conjecture, an escape-existence
theorem, a Jacobsthal/max-gap bound, a phase-fiber cardinality theorem, a CRT
sign decomposition, PowerSwap, GN/CosmicFormula, PNT, or RH.  Reflection alone
does not force an escape.

The result is independent but not yet a Legendre provider.  Its value is that
the square-anchor orbit factors through phase classes whose members have
identical reservation patterns at every fixed offset.  The next mathematically
new question is whether a phase fiber admits a prime-coordinate `±` sign
decomposition; that requires a later CRT/fiber audit.

## Verification

The focused provider-side build succeeded:

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhase
```
