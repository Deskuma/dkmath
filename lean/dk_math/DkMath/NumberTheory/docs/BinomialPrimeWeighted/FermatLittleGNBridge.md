# Fermat Little Theorem Bridge to GN

## Position

This note records the route from Pascal prime-row divisibility to a
Fermat-little-theorem reading of the `GN` factor.

The goal is not to prove a new version of Fermat's little theorem.  Mathlib
already supplies the endpoint:

```lean
Nat.ModEq.pow_card_sub_one_eq_one
```

The goal here is to connect the existing DkMath Beam / `GTail` / `GN` language
to that classical theorem.

## Route

The implemented route is:

```text
Pascal prime row
  -> inner Beam is divisible by p
  -> weighted one-gap GTail inner Beam is divisible by p
  -> GN p x u = inner Beam + x^(p-1)
  -> GN p x u == x^(p-1) [MOD p]
  -> Fermat's little theorem reads x^(p-1) == 1 [MOD p]
  -> if p does not divide x, then GN p x u == 1 [MOD p]
  -> therefore p does not divide GN p x u
```

This is a useful bridge because `GN` is the vocabulary used by the primitive
prime and Zsigmondy-facing layers.

## 1. Prime Row Beam Divisibility

The coefficient-level fact is:

```text
if p is prime, every inner coefficient in row p is divisible by p.
```

Important Lean names:

```lean
theorem prime_allInnerChooseDivisible_self
theorem prime_dvd_inner_choose
theorem prime_dvd_filteredGTailOneSum_true
```

The last theorem is the weighted one-gap `GTail` form:

```lean
theorem prime_dvd_filteredGTailOneSum_true
    {p x u : Nat} (hp : p.Prime) :
    p ∣ filteredGTailOneSum p x u (fun _ => True)
```

Meaning:

```text
The inner Beam of the one-gap GTail disappears modulo p.
```

## 2. GN Splits Into Beam Plus Boundary

The bridge file is:

```lean
DkMath.NumberTheory.WeightedGNBridge
```

It connects `WeightedBinomial` to the legacy `GN` API.

The basic decomposition is:

```lean
theorem GN_eq_filteredGTailOneSum_true_add_right
    {d x u : Nat} (hd : 0 < d) :
    GN d x u =
      filteredGTailOneSum d x u (fun _ => True) + x ^ (d - 1)
```

Interpretation:

```text
GN d x u = inner Beam + right boundary
```

For row `p`, the right boundary is:

```text
x^(p-1)
```

The important point is that the coefficient sieve controls only the inner
Beam.  It does not control the right boundary, whose coefficient is `1`.

## 3. Congruence to the Boundary

Since the prime row kills the inner Beam modulo `p`, `GN` is congruent to the
right boundary:

```lean
theorem prime_GN_modEq_rightBoundary
    {p x u : Nat} (hp : p.Prime) :
    GN p x u ≡ x ^ (p - 1) [MOD p]
```

There is also a divisibility form:

```lean
theorem prime_GN_sub_rightBoundary_dvd
    {p x u : Nat} (hp : p.Prime) :
    p ∣ GN p x u - x ^ (p - 1)
```

And a quotient-witness form:

```lean
theorem prime_exists_GN_eq_mul_add_rightBoundary
    {p x u : Nat} (hp : p.Prime) :
    ∃ B, GN p x u = p * B + x ^ (p - 1)
```

This witness form is often easier to use when later arguments want an explicit
Beam quotient.

## 4. Fermat's Little Theorem Reads The Boundary

If `p` is prime and `p` does not divide `x`, Fermat's little theorem says:

```text
x^(p-1) == 1 [MOD p]
```

In Lean this is supplied by Mathlib:

```lean
Nat.ModEq.pow_card_sub_one_eq_one
```

The DkMath bridge theorem is:

```lean
theorem prime_GN_modEq_one_of_not_dvd_x
    {p x u : Nat} (hp : p.Prime) (hx : ¬ p ∣ x) :
    GN p x u ≡ 1 [MOD p]
```

This theorem is the first clean endpoint where the Beam observation and
Fermat's little theorem meet.

## 5. Non-Divisibility Of GN

The congruence `GN p x u ≡ 1 [MOD p]` immediately forbids divisibility by `p`:

```lean
theorem prime_not_dvd_GN_of_not_dvd_x
    {p x u : Nat} (hp : p.Prime) (hx : ¬ p ∣ x) :
    ¬ p ∣ GN p x u
```

Conceptually:

```text
if p does not divide x,
then p does not divide GN p x u.
```

This is exactly the kind of statement needed for later gcd control:

```text
boundary x
  and
GN p x u
```

do not automatically share the row prime `p`.

## 6. Why This Matters For Primitive / Zsigmondy Work

The primitive-prime layer often reads divisibility through:

```text
a^d - b^d = (a - b) * GN d (a - b) b
```

For prime row `p`, set:

```text
x = a - b
u = b
```

Then the new bridge gives:

```text
if p does not divide a - b,
then p does not divide GN p (a - b) b.
```

This separates two sources of divisibility:

```text
row prime p
primitive prime q
```

The row prime `p` is detected by Pascal-row Beam divisibility, but Fermat's
little theorem shows that it does not necessarily enter the full `GN` factor
when the boundary axis is a `p`-unit.

This is a useful guardrail for Zsigmondy-style arguments: primitive factors
should be tracked separately from the row-prime Beam cancellation.

## Implemented Files

Core implementation:

```text
DkMath.NumberTheory.WeightedBinomial
DkMath.NumberTheory.WeightedGNBridge
```

Public import:

```text
DkMath
```

Verified commands:

```text
lake build DkMath.NumberTheory.WeightedGNBridge
lake build DkMath
git diff --check
```
