# GNPC-006 report

## Outcome

Outcome A — the degree-three GN prime-shell arithmetic checkpoint is
implemented and kernel-checked.

For the dual-oriented shell

```text
GN 3 u x = u^2 + 3*u*x + 3*x^2,
```

the new API separates the ramified prime from the non-ramified sector:

```text
3 | GN 3 u x  <->  3 | u
primitive coordinates  ->  not (9 | GN 3 u x)
q | GN 3 u x, q prime, q != 3  ->  3 | q - 1
q^2 | GN 3 u x, q prime, primitive  ->  3 | q - 1
```

The positive prime-target package also supplies coprime coordinates, excludes
`3 | u`, gives `3 | p - 1`, and retains the centered-square identity.

This is a classification constraint. It does not assert that all prime
divisors are squarefree.

## Reconnaissance and owner

The preferred thin owner was added:

```text
DkMath/NumberTheory/GNThreePrimeArithmetic.lean
```

The existing degree-three explicit and centered-square APIs are reused from
`GNThreeQuadratic`:

```lean
GN_three_dual_explicit
GN_three_eq_discriminant_neg_three_form
GN_three_eq_target_iff_centered_square
GNPositiveRepresentation.bounds
GNPositiveRepresentation.degree_dvd_target_sub_one_of_target_prime
```

The existing `DkMath.NumberTheory.Gcd.GN` boundary declarations were inspected.
They were not imported into this owner because that import brings an unrelated
heavy Zsigmondy dependency and its pre-existing `sorry` warning. The required
P2 boundary exclusion is proved locally from the reused cubic expansion and
`Nat.Coprime`; no FLT or Zsigmondy module is imported.

## Final theorem surface

The mandatory layers are:

```lean
three_dvd_GN_three_iff_dvd_boundary
not_nine_dvd_GN_three_of_coprime
prime_not_dvd_boundary_of_dvd_GN_three_of_coprime_of_ne_three
three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three
three_dvd_prime_sub_one_of_square_lift_GN_three
GNPositiveRepresentation.coprime_coordinates_of_degree_three_target_prime
GNPositiveRepresentation.degree_three_prime_shell_constraints
```

The preferred derivative-side exclusion was also added:

```lean
prime_not_dvd_cubic_boundary_derivative
```

It is a finite identity consequence of the cubic shell and does not claim a
full Hensel-lifting theorem.

## Exact Mathlib route for `3 | q - 1`

For a prime divisor `q != 3`, the proof uses the following concrete route:

1. The cubic identity gives
   `(x + u)^3 = u * GN 3 u x + x^3`.
2. P2 and the corresponding second-coordinate argument show that `u`, `x`,
   and `x + u` are nonzero modulo `q`.
3. In `(ZMod q)ˣ`, define
   `r = Units.mk0 (x + u) * (Units.mk0 x)⁻¹`.
4. The identity gives `r^3 = 1`; `r != 1` follows from `q ∤ u`.
5. The exact order is obtained with
   `orderOf_eq_prime`.
6. The order divides the finite unit-group cardinality by
   `orderOf_dvd_natCard`; `Nat.card_units`, `ZMod.card`, and
   `Nat.totient_prime` reduce that cardinality to `q - 1`.

Thus the final divisibility is obtained by exact order in the finite field
unit group, rather than by an unrecorded cyclotomic theorem.

## Regression anchor and correction

The required square-lift counterexample is included and verified:

```lean
GN 3 17 1 = 343
GN 3 17 1 = 7^3
7^2 | GN 3 17 1
```

Consequently, a universal theorem of the form
`q^2 ∤ GN 3 u x` is false, even for primitive coordinates. The implemented
statement is the correct weaker one: a square-lift prime is away from `3` and
lies in the `1 mod 3` sector.

## Validation

Command:

```text
lake build DkMath.NumberTheory.GNThreePrimeArithmetic
```

Result: success (`Build completed successfully (8677 jobs).`) with no Lean
warnings. The new source contains no `sorry` or `axiom`; `git diff --check`
also passes.

## Deferred items

- no FLT3 endpoint or existing valuation route was modified;
- no universal no-square-lift theorem is claimed;
- no full Hensel lifting, prime classification, Eisenstein UFD argument, or
  cyclotomic/Zsigmondy extension was added;
- no repository-wide import or warning cleanup was attempted;
- no full repository build, commit, push, or CI run was requested or claimed.

The checkpoint stops at the verified degree-three prime-shell arithmetic and
its explicit square-lift classification boundary.
