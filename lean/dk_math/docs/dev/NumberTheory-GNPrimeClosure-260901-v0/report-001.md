# GNPC-001 report

## Outcome

Outcome A — required theorem surface completed

The symmetric factor-one closure and its GN-prime specialization are
implemented for the canonical `DkMath.CosmicFormulaBinom.GN`.  The symmetric
statement keeps the `d = 1` case, where the GN kernel may equal `1`.

## Repository reconnaissance

### Mathlib prime-product API

The exact Mathlib theorem reused is:

```lean
Nat.prime_mul_iff
```

Its current natural-number normal form is
`Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1`.
The implementation only performs conjunction/disjunction orientation cleanup
with `simp`.

### DkMath GN source and identity

The canonical GN declaration reused by the new theorem surface is:

```lean
DkMath.CosmicFormulaBinom.GN
```

The existing factorization identity was also located:

```lean
DkMath.CosmicFormulaCellDim.pow_sub_pow_eq_mul_GN
```

It is not imported or used in this checkpoint because the required P0/P1
theorems are purely about the product `x * GN d x u`; the optional Cosmic
Formula Body wrapper is deferred to avoid adding the heavier `CellDim`
dependency.

### Duplicate search

The repository search found no equivalent generic or GN-facing theorem for
the symmetric statement `Nat.Prime (a * b)` with the two factor-one branches,
nor for the requested GN-prime specialization.  The nearby
`prime_iff_large_prime_cofactor_eq_one` theorem in
`DkMath.NumberTheory.Primitive.SquareBody` is a bounded square-Body theorem
with additional hypotheses, so it is not a duplicate and is not imported.

### Ownership

The new owner is:

```text
DkMath/NumberTheory/GNPrimeClosure.lean
```

This is the appropriate thin NumberTheory closure layer.  No
`DkMath/NumberTheory.lean` aggregator exists, and the top-level `DkMath.lean`
aggregator does not enumerate every NumberTheory leaf module, so no aggregator
was changed.

## Changed files

- `DkMath/NumberTheory/GNPrimeClosure.lean`
- `docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-001.md`

## Final theorem surface

```lean
theorem DkMath.NumberTheory.prime_boundary_mul_GN_iff
    {d x u : ℕ} :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔
      (x = 1 ∧ Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) ∨
      (DkMath.CosmicFormulaBinom.GN d x u = 1 ∧ Nat.Prime x)
```

```lean
theorem DkMath.NumberTheory.prime_boundary_mul_GN_iff_boundary_eq_one_of_GN_prime
    {d x u : ℕ}
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔ x = 1
```

No optional one-way aliases were added.

## Validation

Command run from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.GNPrimeClosure
```

Result: success (`Build completed successfully (8666 jobs).`), with no Lean
warnings after the final linter cleanup.

The new module was also checked for `sorry` and `axiom`; neither occurs.
`git diff --check` passed.

## Deferred items

- Cosmic Formula Body wrapper using `pow_sub_pow_eq_mul_GN`: deferred to keep
  the required module dependency thin.
- `GN > 1` strengthening under `2 ≤ d`, `0 < x`, and `0 < u`: deferred.
- `GN prime → exponent prime`: deferred as a separate factorization problem.
- Nested GN composition identity: deferred; it is explicitly outside GNPC-001.

The forbidden application expansions (Legendre, ABC, FLT, Zsigmondy,
primitive-prime existence, and repository-wide GN renaming) were not added.
