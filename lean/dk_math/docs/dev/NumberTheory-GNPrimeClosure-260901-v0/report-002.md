# GNPC-002 report

## Outcome

Outcome A — required positive-representation and finite-search theorem surface
completed.

For every fixed target `n`, a positive nondegenerate representation
`GN d x u = n` now yields the exact floor and endpoint bounds, then the coarse
strict bounds `d < n`, `x < n`, and `u < n`.  The resulting filtered
`Finset` is complete.

## Reused theory

The new module reuses the canonical DkMath GN declaration and expansion:

```lean
DkMath.CosmicFormulaBinom.GN
DkMath.CosmicFormulaBinom.GN_eq_sum
```

The `(1,1)` anchor proof uses Mathlib's:

```lean
Nat.sum_range_choose
Finset.sum_range_succ'
Nat.eq_sub_of_add_eq
```

The endpoint proof uses the existing GN tail recursion:

```lean
DkMath.CosmicFormula.GN_tail_rec
```

and Mathlib finite-sum/order lemmas:

```lean
Finset.single_le_sum
pow_le_pow_left'
le_self_pow
```

No ABC, FLT, Legendre, Primitive, Zsigmondy, cyclotomic, valuation, or
application-specific module was imported.

## Module and ownership

The new thin owner is:

```text
DkMath/NumberTheory/GNRepresentationBounds.lean
```

Its imports are limited to `Mathlib.Data.Nat.Prime.Basic` and
`DkMath.CosmicFormula.CosmicFormulaBinom`.  No public aggregator was changed.

## Final declarations

```lean
def DkMath.NumberTheory.GNPositiveRepresentation (n d x u : ℕ) : Prop :=
  2 ≤ d ∧ 0 < x ∧ 0 < u ∧
    DkMath.CosmicFormulaBinom.GN d x u = n
```

```lean
theorem DkMath.NumberTheory.GN_one_one_eq_two_pow_sub_one (d : ℕ) :
    DkMath.CosmicFormulaBinom.GN d 1 1 = 2 ^ d - 1
```

```lean
theorem DkMath.NumberTheory.two_pow_sub_one_le_GN
    {d x u : ℕ} (hx : 0 < x) (hu : 0 < u) :
    2 ^ d - 1 ≤ DkMath.CosmicFormulaBinom.GN d x u
```

```lean
theorem DkMath.NumberTheory.boundary_pow_add_head_le_GN
    {d x u : ℕ} (hd : 2 ≤ d) :
    x ^ (d - 1) + d * u ^ (d - 1) ≤
      DkMath.CosmicFormulaBinom.GN d x u
```

```lean
theorem DkMath.NumberTheory.boundary_pow_lt_GN
    {d x u : ℕ} (hd : 2 ≤ d) (_hx : 0 < x) (hu : 0 < u) :
    x ^ (d - 1) < DkMath.CosmicFormulaBinom.GN d x u
```

```lean
theorem DkMath.NumberTheory.head_lt_GN
    {d x u : ℕ} (hd : 2 ≤ d) (hx : 0 < x) (_hu : 0 < u) :
    d * u ^ (d - 1) < DkMath.CosmicFormulaBinom.GN d x u
```

```lean
theorem DkMath.NumberTheory.GNPositiveRepresentation.bounds
    {n d x u : ℕ}
    (h : GNPositiveRepresentation n d x u) :
    2 ^ d - 1 ≤ n ∧
    x ^ (d - 1) < n ∧
    d * u ^ (d - 1) < n ∧
    d < n ∧ x < n ∧ u < n
```

```lean
def DkMath.NumberTheory.GNRepresentationBox (n : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.range n).product
    ((Finset.range n).product (Finset.range n))
```

```lean
def DkMath.NumberTheory.GNPositiveRepresentations (n : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (GNRepresentationBox n).filter fun t =>
    GNPositiveRepresentation n t.1 t.2.1 t.2.2
```

```lean
theorem DkMath.NumberTheory.mem_GNPositiveRepresentations_iff
    {n d x u : ℕ} :
    (d, (x, u)) ∈ GNPositiveRepresentations n ↔
      GNPositiveRepresentation n d x u
```

The exact floor theorem required a new proof.  The combined endpoint lower
bound was achieved directly; it was not split into separate public endpoint
inequalities.  The strict endpoint theorems are exposed as ergonomic
corollaries.

## Validation

Command run from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.GNRepresentationBounds
```

Result: success (`Build completed successfully (8666 jobs).`) with no Lean
warnings.  The module was checked for newly introduced `sorry` and `axiom`;
neither occurs.  `git diff --check` passed.

## Deferred items

- `GNPrimeRepresentation` vocabulary: optional and deferred.
- `GN prime → exponent prime`.
- Composite-degree GN factorization and nested GN composition.
- Cyclotomic, residue, primitive-prime, Zsigmondy, ABC, FLT, and Legendre
  applications.
- Body primality wrapper and repository-wide GN renaming/refactor.

The checkpoint stops at the complete finite representation box and does not
classify which target values are prime or which prime values occur.
