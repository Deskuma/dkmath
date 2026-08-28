# PUU-L005 — Finite prime-scale synchronization

## Implemented surface

Added `DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization` and
exported it through the existing `DkMath.NumberTheory.PrimorialUniverse`
facade.  The module defines
`IsCommonMultipleOfPrimeBasis S T`, reusing the existing finite-prime-basis,
product, and reservation vocabulary from PUU-L001.

## Formal results

- `finitePrimeBasisProduct_isCommonMultiple`: every member of `S` divides
  `finitePrimeBasisProduct S`.
- `finitePrimeBasisProduct_dvd_of_commonMultiple`: when `S` is a finite set of
  ordinary primes, its product divides every common multiple of `S`.  The
  proof is finite induction; the induction step combines the new prime with
  the old product using pairwise coprimality of distinct primes.
- `finitePrimeBasisProduct_dvd_iff_commonMultiple`: the product is the least
  common synchronization period in the divisibility order.
- `reservedByPrimeBasis_add_mul_period_iff` and
  `not_reserved_add_mul_period_iff`: adding any multiple of the product
  preserves, respectively, reservation and non-reservation.

## Regressions

The product computations are checked for `{2, 3}`, `{2, 3, 5}`, and
`{2, 3, 5, 7}`, giving `6`, `30`, and `210`.  A visible periodicity regression
identifies the `{2, 3, 5}` reservation status at `7` and `37 = 7 + 30`.

## Semantic boundary

A finite family of distinct prime-scale reservation patterns has a smallest
common period in the divisibility sense, namely the product of the primes.
For an initial prime segment this is the ordinary primorial, and the
reservation sheet repeats exactly modulo that finite product.

This checkpoint does not define prime-basis enumeration, reduced-residue or
Euler-phi counts, wheel/reflection statements, next-prime deletion, arbitrary
unit-ratio classifications, PowerSwap, GN/CosmicFormula, Legendre, PNT, or RH.
