# DkMath Collatz: one-step fixed point and unit boundary

cid: 6a6e8ee5-a85c-83ee-a2c5-4d4e0fdbd980

> **Scope summary**
>
> This document concerns only the positive solutions of
>
> $$
> 3n+1=2^h n.
> $$
>
> It proves that the accelerated odd Collatz map has no positive **one-step
> fixed point** other than the boundary state $n=1$ with $h=2$.
>
> The historical Lean declarations contain the phrase `one_cycle`, but this
> document deliberately uses **one-step fixed point** in prose.  It must not be
> read as a classification of arbitrary Collatz cycles, or as the standard
> cycle terminology used elsewhere in mathematics.

## 1. Purpose of this document

The theorem was originally introduced as a small local obstruction inside
`DkMath.Collatz.PetalBridge`.  Its implementation, review, unit-product
interpretation, and valuation-flow bridge were recorded across several
checkpoint documents.

This page collects only that theorem family in one stable place.

The goal is to make the following distinction immediately visible:

```text
proved:
  a single accelerated odd step returns to the same positive odd state
  only at n = 1, h = 2

not proved here:
  arbitrary finite Collatz cycles do not exist
  every Collatz orbit converges
```

## 2. Main Lean theorem

Source:

```text
DkMath/Collatz/PetalBridge/OneCycle.lean
```

Main declaration:

```lean
theorem collatz_scaled_one_cycle_eq_one
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2
```

The exact quantified statement is:

```text
for every natural n and h,
if n is positive and 3*n+1 = 2^h*n,
then n = 1 and h = 2.
```

The equivalent form is also available:

```lean
theorem collatz_scaled_one_cycle_iff
    {n h : ℕ}
    (hn : 0 < n) :
    3 * n + 1 = 2 ^ h * n ↔ n = 1 ∧ h = 2
```

## 3. Dynamical interpretation

For an odd state $n$, an accelerated Collatz step removes all powers of two
from $3n+1$.

If one accelerated step returns immediately to the same odd state, then for
some height $h$,

$$
\frac{3n+1}{2^h}=n.
$$

Equivalently,

$$
3n+1=2^h n.
$$

The theorem classifies exactly these positive fixed-point equations.

At the unique solution,

$$
n=1,
\qquad
h=2,
$$

and the ordinary Collatz trajectory is

```text
1 -> 4 -> 2 -> 1.
```

Thus the theorem says:

```text
the familiar boundary loop exists,
but it has no positive scaled copy that closes after one accelerated odd step.
```

## 4. Why the proof is finite and elementary

The proof classifies the possible height $h$.

### 4.1. Heights at least three are impossible

If $3\le h$, then

$$
8\le2^h.
$$

Multiplying by the positive number $n$ gives

$$
8n\le2^h n=3n+1,
$$

which contradicts $0<n$.

This is implemented by:

```lean
collatz_scaled_one_cycle_h_not_ge_three
```

### 4.2. Heights zero and one are impossible

Substituting $h=0$ or $h=1$ into

$$
3n+1=2^h n
$$

contradicts positivity.

These cases are exposed as:

```lean
collatz_scaled_one_cycle_h_ne_zero
collatz_scaled_one_cycle_h_ne_one
```

### 4.3. Height two forces the unit state

The only remaining case is $h=2$:

$$
3n+1=4n.
$$

Hence

$$
n=1.
$$

No finite search over initial values or cycle lengths is used.  The theorem is
an exact symbolic classification of one equation.

## 5. Unit-product form

Moving the linear term to the other side gives the integer identity

$$
(2^h-3)n=1.
$$

The Lean implementation first records this over `ℤ`, avoiding truncated
natural-number subtraction:

```lean
theorem collatz_scaled_one_cycle_int_unit_product
    {n h : ℕ}
    (_hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    (((2 ^ h : ℕ) : ℤ) - 3) * (n : ℤ) = 1
```

After the unique solution is known, the natural-number form is safe:

```lean
theorem collatz_scaled_one_cycle_nat_unit_product
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n * (2 ^ h - 3) = 1
```

This is the DkMath **unit-boundary** reading:

```text
closed one-step loop
  -> unit product
  -> base and scale gap both collapse to 1
```

The project-facing alias is:

```lean
collatz_scaled_one_cycle_is_unit_boundary
```

## 6. Prime-channel and support interpretation

A positive one-step fixed point leaves no nontrivial prime factor on either
factor of the unit product.

The local file proves:

```lean
collatz_scaled_one_cycle_no_prime_channel_on_base
collatz_scaled_one_cycle_no_prime_channel_on_scale_gap
collatz_scaled_one_cycle_no_prime_channel_on_unit_product
```

The thin bridge file,

```text
DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean
```

then exposes the same fact using the valuation-flow vocabulary:

```lean
oneCycle_unit_boundary_only
oneCycle_unit_product_nat
oneCycle_unit_product_int
oneCycle_no_prime_channel_on_base
oneCycle_no_prime_channel_on_scaleGap
oneCycle_no_prime_channel_on_unitProduct
oneCycle_supportMass_unitProduct_eq_one
oneCycle_rad_unitProduct_eq_one
oneCycle_no_supportMass_growth
```

The resulting chain is:

```text
3*n+1 = 2^h*n
  -> n = 1 and h = 2
  -> n * (2^h - 3) = 1
  -> no prime channel remains
  -> supportMass = 1
  -> rad = 1
```

This bridge does not turn the theorem into a general cycle theorem.  It only
records the support-theoretic meaning of the already classified one-step fixed
point.

## 7. Terminology boundary

The original checkpoint and Lean names use expressions such as:

```text
one-cycle
scaled one-cycle
1 -> 4 -> 2 -> 1 cycle
```

Inside this theorem family, these expressions mean precisely:

```text
one accelerated odd step returns to the same odd state.
```

For clear prose, use:

```text
accelerated one-step fixed point
one-step return equation
unit-boundary fixed point
```

Do not infer that the word `one_cycle` in a declaration name has the same type
or quantifier structure as a `1-cycle` or `m-cycle` defined in another
mathematical framework.

The comparison is intentionally not part of this document.  The theorem is
identified by its Lean type, not by similarity of terminology.

## 8. Exact non-claims

This theorem family does **not** establish any of the following.

```text
1. Every nontrivial Collatz cycle is impossible.
2. Every cycle with more than one accelerated odd step is impossible.
3. A theorem universally quantified over an arbitrary cycle length k.
4. A theorem universally quantified over a list of cycle states.
5. A passage from a finite observation window to all natural numbers.
6. Global boundedness of Collatz trajectories.
7. Convergence of every positive Collatz orbit to 1.
```

In particular, no hidden finite-window assumption is being promoted to a
global result.  The main theorem does not inspect a finite range at all; it
solves one universally quantified Diophantine equation.  Its limitation comes
from the equation being a one-step return equation, not from bounded
computation.

## 9. Quantifier audit

The main theorem quantifies over:

```text
n : ℕ
h : ℕ
```

and assumes:

```text
0 < n
3*n + 1 = 2^h*n
```

It does not introduce or quantify over:

```text
cycle length k
state sequence n_0, ..., n_(k-1)
multiple heights h_0, ..., h_(k-1)
return after two or more accelerated steps
```

Therefore the proven domain is exactly the fixed-point equation for one
accelerated step.

## 10. Why the multi-step problem is a different type

For one step, closure produces the unit equation

$$
(2^h-3)n=1.
$$

For several accelerated steps,

$$
n_{i+1}=\frac{3n_i+1}{2^{h_i}},
$$

repeated substitution accumulates the intermediate `+1` terms.  A return to
the initial state no longer reduces directly to the same unit product.

Schematically, the resulting equation has the different shape

$$
(2^H-3^r)n_0=S(h_0,\ldots,h_{r-1}),
$$

where the right-hand side records accumulated offsets and need not equal $1$.

Thus the present proof is not missing a final induction over cycle length.
The multi-step statement has a genuinely different algebraic type and requires
additional structure.

## 11. Theorem index

### Classification

```lean
collatz_scaled_one_cycle_h_not_ge_three
collatz_scaled_one_cycle_h_ne_zero
collatz_scaled_one_cycle_h_ne_one
collatz_scaled_one_cycle_eq_one
collatz_scaled_one_cycle_iff
collatz_scaled_one_cycle_no_wrong_height
collatz_scaled_one_cycle_no_wrong_base
```

### Concrete boundary

```lean
collatz_one_four_two_one_scaled_boundary_unique
collatz_one_four_two_one_scaled_boundary_exists
one_four_two_one_petal_scaled_cycle_unique
```

### Unit boundary

```lean
collatz_scaled_one_cycle_int_unit_product
collatz_scaled_one_cycle_nat_unit_product
collatz_scaled_one_cycle_is_unit_boundary
```

### Prime-channel exclusion

```lean
collatz_scaled_one_cycle_no_prime_channel_on_base
collatz_scaled_one_cycle_no_prime_channel_on_scale_gap
collatz_scaled_one_cycle_no_prime_channel_on_unit_product
```

### Valuation-flow bridge

```lean
oneCycle_unit_boundary_only
oneCycle_unit_product_nat
oneCycle_unit_product_int
oneCycle_no_prime_channel_on_base
oneCycle_no_prime_channel_on_scaleGap
oneCycle_no_prime_channel_on_unitProduct
oneCycle_supportMass_unitProduct_eq_one
oneCycle_rad_unitProduct_eq_one
oneCycle_no_supportMass_growth
```

## 12. Source map

Current Lean sources:

- [`../PetalBridge/OneCycle.lean`](../PetalBridge/OneCycle.lean)
- [`../PetalBridge/ValuationFlowBridge.lean`](../PetalBridge/ValuationFlowBridge.lean)

Historical implementation records:

- [`report-petal-150.md`](../../../docs/dev/das-p2l-260607/review/100_199/report-petal-150.md)
- [`review-petal-151.md`](../../../docs/dev/das-p2l-260607/review/100_199/review-petal-151.md)
- [`note-petal-ValuationFlowBridge-151.md`](../../../docs/dev/das-p2l-260607/review/100_199/note-petal-ValuationFlowBridge-151.md)
- [`review-petal-151-a.md`](../../../docs/dev/das-p2l-260607/review/100_199/review-petal-151-a.md)
- [`report-petal-151-b.md`](../../../docs/dev/das-p2l-260607/review/100_199/report-petal-151-b.md)

Package entrance:

- [`../README.md`](../README.md)

## 13. Stable summary

The stable claim of this theorem family is:

> For positive natural numbers, the equation $3n+1=2^h n$ has the unique
> solution $n=1$, $h=2$.  Therefore the accelerated odd Collatz map has only
> the familiar positive one-step fixed point, and that fixed point is a unit
> boundary with no remaining prime-support channel.

Nothing stronger should be attributed to these declarations without a new
Lean theorem whose type explicitly quantifies over the stronger cycle
structure.
