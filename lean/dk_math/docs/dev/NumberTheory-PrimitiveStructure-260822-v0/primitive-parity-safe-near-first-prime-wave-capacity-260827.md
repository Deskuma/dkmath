# PRIM-L063 — Near first-prime fiber / product-wave capacity

## Outcome

Outcome A+ — NEAR FIRST-PRIME WAVE CAPACITY COMPLETE.

The Near gate is partitioned exactly by its first prime, and the possible
square seats are retained as a finite product-wave capacity:

```text
Near
  -> first prime p with p^3 < 2*n
  -> ordered pair fiber (q,s), p*q*s <= 2*n
  -> product-wave occupancy
  -> explicit finite NearWaveBudget.
```

## Implemented module

The new module
`DkMath.NumberTheory.Legendre.ParitySafeNearFirstPrimeWaveCapacity` provides:

- `paritySafeNearFirstPrimes` and its membership/near-key consumer theorems;
- `paritySafeNearPrimePairsAtFirst` and the exact Near key characterization;
- exact first-prime fiber decomposition of the Near key cardinality;
- `paritySafeNearFirstPrimeWaveBudget`, including its equality with the Near
  key wave sum;
- the product-wave upper incidence card equality and
  `paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget`;
- the exact quotient-plus-`squareWaveCarry` arithmetic form;
- the L062 LowCost upper-control consumer.

The public facade `DkMath.NumberTheory.Legendre` imports this module.

## Proof boundary

The Near residual incidence `(r,(q,s))` is mapped to
`((canonicalPrime(n,r),(q,s)),r)`.  The retained `r` coordinate makes this
map injective, while the existing product-wave theorem supplies membership in
the finite upper ledger.  No single-seat claim is made: a Near product key
may contribute multiple seats.

The resulting LowCost control is exactly

```text
LowCostResidual <= NearWaveBudget
                 + L018 prime-square depth budget
                 + raw Fourth card.
```

## Non-goals

Near elimination, wave occupancy at most one, analytic sieve or asymptotic
estimates, new Fourth counting, fifth direction, residual recursion/descent,
global contradiction, Legendre's conjecture, and RH remain outside scope.

## Validation

- `lake build DkMath.NumberTheory.Legendre.ParitySafeNearFirstPrimeWaveCapacity`
  passed.
- `lake build DkMath.NumberTheory.Legendre` passed.
- `git diff --check` passed.
- The changed Lean source contains no `sorry`, `admit`, `axiom`, or
  `native_decide`.
