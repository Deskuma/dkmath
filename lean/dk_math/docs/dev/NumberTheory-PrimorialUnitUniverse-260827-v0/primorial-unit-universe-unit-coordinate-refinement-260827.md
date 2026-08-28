# PUU-L002: Unit Coordinate Refinement / Prime-to-Composite Same-Point Bridge

## Result

PUU-L002 is implemented in
`DkMath.NumberTheory.PrimorialUniverse.UnitCoordinateRefinement` and exported
through the existing `DkMath.NumberTheory.PrimorialUniverse` facade.

The implementation uses positive real units and natural coordinates.  The
prime/composite label is attached only to a natural coordinate in a selected
unit presentation, never to the shared absolute real point.

## Public API

- `PositiveUnit` stores `val : ℝ` together with `0 < val`.
- `HasUnitCoordinate u n X` means `X = (n : ℝ) * u.val`.
- `HasPrimeCoordinate u X` packages a `Nat.Prime` coordinate.
- `unitCoordinate_unique` proves uniqueness at a fixed positive unit.
- `UnitRefinesBy fine coarse k` means `coarse = k * fine`.
- `unitRefinement_samePoint` proves the corresponding coordinate equality.
- `unitCoordinate_refine` transports `n` to `n * k`.

## Prime-to-nonprime packet

For a prime coarse coordinate `p` and `1 < k`,
`prime_coordinate_refinement_packet` proves all three required facts:

```text
HasUnitCoordinate fine (p * k) X
¬ Nat.Prime (p * k)
p ∣ p * k
```

The non-primality proof uses the explicit factorization theorem
`Nat.not_prime_mul`; a separate `Nat.Composite` wrapper was intentionally
avoided because the public meaning needed here is exactly “not prime” plus
the surviving old factor.

## Same-point regression

The theorem `three_at_five_eq_fifteen_at_one` fixes the motivating example:

```text
15 = 3 * 5 = 15 * 1
```

Thus `3` is prime as the coordinate in unit `5`, while `15` is not prime as
the coordinate in unit `1`.  This does not assert that the real number `15`
itself is prime or composite.

## L001 support connection

`refined_coordinate_not_supported_by_old_basis` combines coordinate
transport with L001's `newPrime_mul_not_primeSupportContainedIn`.  If
`q ∉ S` is prime, then refinement can expose `q * k` as a nonprime fine
coordinate, but the old basis still cannot contain all of its prime support:
the direct divisor `q ∣ q * k` persists.

## Boundary

This checkpoint stops at synchronized integer refinement.  It does not define
rational/irrational common-lattice classifications, arbitrary rational unit
changes, gcd/lcm lattice results, primorial wheels, reduced residues,
reflection/lift rules, PowerSwap, GN/cosmic normalization, Legendre, square
anchors, analytic prime counting, or generic lattice abstractions.

## Verification

The focused module, facade, and top-level `DkMath` target were built
successfully.  `git diff --check` and scans for `sorry`, `admit`, `axiom`, and
`native_decide` were also run for the new implementation.  No commit, push,
merge, or CI action was performed.
