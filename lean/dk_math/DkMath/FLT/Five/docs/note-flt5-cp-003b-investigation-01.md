# Note: FLT5 cp-003b investigation 01

## Outcome

**Outcome A:** a compiling elementary route to the fifth-power factor split
was found and promoted to `DkMath.FLT.Five.Reduction` after scratch
verification.

For every Branch-B counterexample pack, Lean now proves

```text
∃ a, z - y = a ^ 5
∃ b, GN5 (z - y) y = b ^ 5
```

The production module imports only `DkMath.FLT.Five.GN5`, whose dependency is
the Mathlib-only `Basic` layer. No research module is imported.

## Certified reduction

The compiling chain is:

```text
CounterexamplePack x y z
  -> Coprime y z
  -> Coprime (z - y) y

Coprime (z - y) y and 5 does not divide z - y
  -> Coprime (z - y) (GN5 (z - y) y)

(z - y) * GN5 (z - y) y = x^5
  -> z - y = a^5 and GN5 (z - y) y = b^5
```

The second step uses the elementary congruence

```text
GN5 g y = g * (...) + 5 * y^4.
```

Thus every common prime divisor of `g` and `GN5 g y` must divide `5*y^4`.
Coprimality excludes the `y` branch, and `5 does not divide g` excludes the
exceptional prime.

The final split is Mathlib's generic GCD-monoid theorem
`exists_eq_pow_of_mul_eq_pow`. No new unique-factorization development is
needed.

## Workspace search findings

- `DkMath.FLT.Basic` contains closely related coprimality reductions, but they
  are private and belong to the older general FLT layer.
- `DkMath.Petal.BezoutBridge` expresses the same exceptional-prime separation
  for the general `GN`; it is useful evidence but is intentionally not imported.
- `DkMath.Zsigmondy` and the Triomino Branch-B bridge provide primitive primes.
  Under a counterexample, the existing bridge drives such a prime into a
  square-divisibility lift, confirming that primitive existence alone cannot
  supply NoLift.
- `DkMath.Hackathon.FinitePrimeEscapeGN5` certifies the fixed `g=y=1` example,
  not a uniform counterexample-family theorem.
- The PowerSwap and exponent-five research layers contain structural routes,
  but no smaller factor-split lemma than the Mathlib theorem above was found.

## Contract audit

`BranchBNoLiftEscape` remains a sufficient refuter contract, but it is not the
natural next intermediate theorem. Once the factor split is known, every prime
exponent in `GN5` is forced to be a multiple of five. A NoLift prime would
therefore already be the contradiction rather than a neutral witness produced
by ordinary primitive-divisor theory.

The recommended next research kernel is consequently one of:

```text
Branch-B counterexample -> GN5 is not a fifth power
```

or a descent theorem showing that `GN5 = b^5` produces a smaller
counterexample/normal form. The new theorem
`branchB_false_of_GN5_not_fifth_power` records the exact receiver for the first
route without claiming that the missing non-fifth-power theorem is proved.

## Added declarations

```text
coprime_y_z_of_counterexamplePack
coprime_gap_y_of_counterexamplePack
dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5
coprime_gap_GN5_of_coprime_of_five_not_dvd
branchB_coprime_gap_GN5
fifth_power_factor_split
branchB_fifth_power_factor_split
branchB_false_of_GN5_not_fifth_power
```
