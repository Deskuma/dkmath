# PUU-L007 — Fresh-prime lift and unique deletion

## Implemented surface

Added `DkMath.NumberTheory.PrimorialUniverse.FreshPrimeLift` and exported it
through the public `DkMath.NumberTheory.PrimorialUniverse` facade.

- `primeBasisWheelLift S r j` defines the `j`-th lift `r + j*M`.
- `finitePrimeBasisProduct_insert` gives the enlarged period
  `q * finitePrimeBasisProduct S` for a fresh `q`.
- `freshPrime_coprime_finitePrimeBasisProduct` proves coprimality of `q` and
  the old period.
- `reservedByPrimeBasis_lift_iff` and
  `not_reservedByPrimeBasis_lift` transport the old reservation status along
  every lift fiber.
- `primeBasisWheelLift_mem_enlarged_period` places every lift with `j < q`
  inside the enlarged one-period interval.

## Unique-deletion packet

`existsUnique_freshPrime_dvd_lift` proves that exactly one index `j < q`
satisfies `q ∣ primeBasisWheelLift S r j`.  Existence uses the coprime modular
inverse witness `Nat.exists_mul_mod_eq_of_coprime`; uniqueness cancels the old
period using coprimality and the bound `j < q`.

`reservedByPrimeBasis_insert_fresh_lift_iff` identifies enlarged-basis
reservation on an old-survivor fiber with divisibility by `q`, and
`existsUnique_reservedByPrimeBasis_insert_fresh_lift` packages the semantic
statement that exactly one lift is deleted.  The optional local `q - 1`
cardinality theorem was not added; the per-fiber unique-deletion theorem is
the required PUU-L007 boundary.

## `6 → 30` regression

The concrete regressions identify the deleted lift in the `{2,3}` fiber at
`r = 1` as `j = 4`, point `25`, and in the `r = 5` fiber as `j = 0`, point
`5`.  The general unique-deletion theorem supplies uniqueness for these
visible witnesses.

## Semantic boundary

`q` is fresh, not necessarily numerically next.  Each old survivor produces
`q` lifts, old-prime reservation is unchanged, and precisely one lift is newly
deleted by `q`, leaving the local factor `q - 1`.

This is not the global next-wheel decomposition or cardinality recurrence;
that belongs to PUU-L008.  Survivor still means “unreserved by the finite
basis,” not “prime.”  No lift-fiber disjointness/completeness theorem,
replication theorem, wheel-gap propagation, Legendre, PNT, RH, PowerSwap, or
GN/CosmicFormula statement is introduced.
