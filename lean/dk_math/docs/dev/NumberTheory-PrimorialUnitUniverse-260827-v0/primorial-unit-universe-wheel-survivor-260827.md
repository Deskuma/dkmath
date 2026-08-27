# PUU-L006 — Primorial wheel survivors and reflection

## Implemented surface

Added `DkMath.NumberTheory.PrimorialUniverse.WheelSurvivor` and exported it
through the public `DkMath.NumberTheory.PrimorialUniverse` facade.

- `IsPrimeBasisWheelSurvivor S r` represents a positive seat strictly inside
  the period, with no reservation by a prime in `S`.
- `primeBasisWheelSurvivors S` packages the one-period survivors as a
  `Finset`, with `mem_primeBasisWheelSurvivors_iff` as its membership theorem.
- `not_reserved_iff_coprime_finitePrimeBasisProduct` gives the reduced-residue
  interpretation without introducing any cardinality statement.

## Formal results

`reserved_reflect_iff` proves that the reservation status at `r` agrees with
that at `M - r`, where `M = finitePrimeBasisProduct S` and `0 < r < M`.
The proof uses `p ∣ M` for each basis prime and the identity
`(M - r) + r = M`.

`wheelSurvivor_reflect` lifts this to exact reflection symmetry of survivor
seats.  `wheelReflection_involutive` records the corresponding identity after
applying reflection twice under the natural side condition `r ≤ M`.

## Regression

For the basis `{2, 3}`, the period is `6` and
`primeBasisWheelSurvivors {2, 3} = {1, 5}`.  Thus the regression fixes the
expected `1 ↔ 5` reflection pattern.

## Semantic boundary

The survivor predicate is not `Nat.Prime`; composite survivors are allowed.
This checkpoint cuts one period from the L005 periodic reservation sheet and
proves its product-period reflection.  It is distinct from the PUU-L001
Euclidean escape point `M + 1`: for `{2,3}`, `5` is a survivor while `7` is
the escape point.

No Euler-phi/cardinality result, next-prime lift or unique deletion, replication,
wheel-gap propagation, square-anchor/Legendre theorem, PNT/RH statement,
PowerSwap, or GN result is introduced.
