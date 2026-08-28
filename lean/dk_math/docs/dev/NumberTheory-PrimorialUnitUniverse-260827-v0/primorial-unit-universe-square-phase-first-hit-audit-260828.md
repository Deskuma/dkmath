# PUU-L032 — Square-Phase First-Hit Radius Audit

## Status

L032 is implemented as a provider-side finite first-hit comparison.  It
compares arbitrary cyclic wheel labels with the labels reachable as
`n^2 mod M`, without introducing a short-square bound or an escape theorem.

## Generic profile and first hit

`DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOffsetFirstHitAudit.lean`
defines `genericUnreservedOffsetProfile S A` on `range M` by the condition

```text
IsPrimeBasisWheelSurvivor S ((A + t) % M).
```

`mem_genericUnreservedOffsetProfile_iff` exposes the bounded natural-offset
membership form.  For every nonempty finite prime basis, the theorem
`genericUnreservedOffsetProfile_nonempty` proves that every generic shift has
at least one offset, using a cyclic translate of the survivor `1`.

`genericFirstUnreservedOffset S A hS hSne` is the `Finset.min'` of the generic
profile.  The public semantics are provided by:

- `genericFirstUnreservedOffset_mem`: the first offset belongs to the profile;
- `genericFirstUnreservedOffset_lt`: it is strictly below `M`;
- `genericFirstUnreservedOffset_minimal`: every smaller offset is absent.

The square first-hit coordinate is exposed by
`squareAnchorFirstUnreservedOffset`.  The theorem
`squareAnchorFirstUnreservedOffset_eq_generic` identifies it with the generic
first hit at `squareAnchorWheelProjection S n`.  Same square phase gives equal
first-hit coordinates through
`squareAnchorFirstUnreservedOffset_eq_of_samePhase`.

## Reachable labels and radii

`squareAnchorReachablePhaseLabels S` is the image of `range M` under
`squareAnchorWheelProjection`.  Its membership theorem is
`mem_squareAnchorReachablePhaseLabels_iff`:

```text
A ∈ SquareLabels(S)
  ↔ ∃ n < M, squareAnchorWheelProjection S n = A.
```

The two finite worst-case quantities are:

```text
genericFirstHitRadius S hS hSne
  = sup over all A < M of genericFirstUnreservedOffset S A;

squareFirstHitRadius S hS hSne
  = sup over reachable square labels A of genericFirstUnreservedOffset S A.
```

The theorem `squareFirstHitRadius_le_genericFirstHitRadius` proves the basic
subset comparison.  The theorem
`squareAnchorFirstUnreservedOffset_le_squareFirstHitRadius` bounds every
square-anchor first hit by the square-restricted radius.  Both statements are
whole-old-period results.

## Exact regressions

`squarePhaseFirstHit_two_three_regression` proves, for `S = {2,3}` and `M=6`,

```text
GenericRadius = 3
SquareRadius  = 2
generic first hit at A = 2 is 3.
```

Thus the arbitrary shift `A=2` is a genuine worst case that is not reached by
the square labels in this basis.

`squarePhaseFirstHit_two_three_five_regression` proves, for `S={2,3,5}` and
`M=30`,

```text
GenericRadius = 5
SquareRadius  = 5
first hit at A = 24 is 5
squareAnchorWheelProjection S 12 = 24.
```

This gives the requested reachable generic worst case, since `12^2 mod 30=24`.
The two regressions are proved through the first-hit membership/minimality
API and finite survivor membership, rather than by asserting the radius values
without the first-hit semantics.

## Verdict

**Outcome B — QUADRATIC-RESTRICTION-REAL-BUT-NONUNIFORM.**

Square phases are a genuine restriction: `{2,3}` improves the worst first-hit
radius from `3` to `2`.  The restriction is not uniformly improving:
`{2,3,5}` has equality `5 = 5`, and a square phase reaches the generic worst
case.

Therefore square phase alone is not sufficient to justify a coverage
obstruction.  The next useful interaction must add information beyond square
phase alone, such as basis growth or another coupled coordinate, rather than
adding more first-hit identities.

## Boundary

The module remains entirely in `DkMath.NumberTheory.PrimorialUniverse`.  It
does not define or import Legendre consumers, `SquareCell`, `SquareOffset`,
`escapingSquareOffsets`, a `2*n` bound, Jacobsthal or generic wheel-gap
machinery, prime powers, asymptotic estimates, PNT/RH, PowerSwap, GN, or
CosmicFormula statements.

## Verification

The focused target

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetFirstHitAudit
```

and the facade target

```text
lake build DkMath.NumberTheory.PrimorialUniverse
```

completed successfully.  The final `./lb` full build also succeeded; the
non-`sorry` warning filter was empty.

