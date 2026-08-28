# PUU-L008 — Global wheel replication and cardinality recurrence

## Implemented surface

Added `DkMath.NumberTheory.PrimorialUniverse.WheelReplication` and exported
it through the public facade.

- `one_lt_finitePrimeBasisProduct_of_nonempty` handles the nonempty-basis
  period condition.
- `enlargedWheelSurvivor_iff_exists_oldSurvivorLift` gives the exact quotient /
  remainder decomposition of an enlarged survivor.
- `primeBasisWheelLift_injective_on_period` proves fiber disjointness.
- `freshPrimeSurvivingLiftIndices` and
  `card_freshPrimeSurvivingLiftIndices` package the local `q - 1` count.
- `primeBasisWheelSurvivorLiftSeats` and
  `primeBasisWheelSurvivor_insert_fresh_eq_liftSeats` give the global lift
  image decomposition.
- `card_primeBasisWheelSurvivors_insert_fresh` proves the global recurrence.

## Proof route

For an enlarged survivor `x`, set `r = x % M` and `j = x / M`.  The old
period bound gives `r < M`, the enlarged-period bound gives `j < q`, and
nonemptiness of `S` excludes `r = 0`.  PUU-L005/L006 then show that `r` is an
old survivor.  Conversely, PUU-L007's lift-range and fresh-prime bridge turn
every surviving old lift into an enlarged survivor.

The local index Finset is the range `q` with its unique deleted index erased,
so its cardinality is `q - 1`.  Quotient/remainder injectivity makes the
lift image disjoint across all old survivor fibers.  Summing the local counts
over the old survivor Finset yields the recurrence.

## Edge case and regression

The recurrence assumes `S.Nonempty`.  For the empty basis, the product is `1`,
there are no old survivor seats, while the one-prime wheel has positive seats;
the simple recurrence is therefore not stated for `S = ∅`.

The visible regression records the `{2,3}` wheel cardinality `2` and the
`{2,3} → {2,3,5}` recurrence `8 = (5 - 1) * 2` through the general theorem.

## Semantic boundary

The result is the exact finite self-replication law: each old survivor has
`q` lifts, one is deleted by the fresh prime, and all surviving lift fibers
form the enlarged wheel.  A survivor means only “unreserved by the finite
basis,” not “prime.”

No Euler-phi identification, closed product formula, wheel-gap transport,
nested projection, square-anchor/Legendre, PowerSwap, GN/CosmicFormula, PNT,
RH, or analytic sieve theorem is introduced.  This checkpoint stops before
PUU-L009.
