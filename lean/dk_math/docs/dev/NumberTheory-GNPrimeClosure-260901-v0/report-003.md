# GNPC-003 report

## Outcome

Outcome A — composite degree layers are eliminated in the positive
nondegenerate natural-number region.

If `GN d x u` is prime with `2 ≤ d`, `0 < x`, and `0 < u`, then `d` is prime.
The proof is internal to the canonical GN identity and does not use
cyclotomic, residue, primitive-prime, or application-specific theory.

## Reconnaissance

The repository search was run before implementation:

```text
rg -n 'GN_mul_degree|prime_degree_of_prime_GN|not_prime_GN_of_mul_degree|GNDegreeFactorization' DkMath DkMathTest docs
```

No existing declaration or module with these GNPC-003 names was found; the
matches were confined to the instruction documents.

The exact Cosmic Formula identity reused is:

```lean
DkMath.CosmicFormulaBinom.cosmic_id_csr'
```

with type, for `R = ℕ`,

```lean
(x + u) ^ d = x * DkMath.CosmicFormulaBinom.GN d x u + u ^ d
```

For the degree decomposition, the Mathlib reconnaissance found:

```lean
Nat.not_prime_iff_exists_mul_eq
```

under `2 ≤ d`, giving `d = a * b` with `a < d` and `b < d`.  The strict
factor bounds, together with the product equation, yield `2 ≤ a` and
`2 ≤ b`.  The final primality contradiction uses:

```lean
Nat.not_prime_mul
```

## Module and declarations

The new thin owner is:

```text
DkMath/NumberTheory/GNDegreeFactorization.lean
```

The nested composition theorem is:

```lean
theorem DkMath.NumberTheory.GN_mul_degree
    {a b x u : ℕ}
    (hx : 0 < x) :
    DkMath.CosmicFormulaBinom.GN (a * b) x u =
      DkMath.CosmicFormulaBinom.GN a x u *
        DkMath.CosmicFormulaBinom.GN b
          (x * DkMath.CosmicFormulaBinom.GN a x u) (u ^ a)
```

The positive-region nontriviality package is:

```lean
theorem DkMath.NumberTheory.one_lt_factors_of_composite_degree
    {a b x u : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hx : 0 < x) (hu : 0 < u) :
    1 < DkMath.CosmicFormulaBinom.GN a x u ∧
      1 < DkMath.CosmicFormulaBinom.GN b
        (x * DkMath.CosmicFormulaBinom.GN a x u) (u ^ a)
```

The composite-degree obstruction is:

```lean
theorem DkMath.NumberTheory.not_prime_GN_of_mul_degree
    {a b x u : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hx : 0 < x) (hu : 0 < u) :
    ¬ Nat.Prime (DkMath.CosmicFormulaBinom.GN (a * b) x u)
```

The main necessary condition is:

```lean
theorem DkMath.NumberTheory.prime_degree_of_prime_GN
    {d x u : ℕ}
    (hd : 2 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) :
    Nat.Prime d
```

The GNPC-002 positive-representation wrapper is:

```lean
theorem DkMath.NumberTheory.GNPositiveRepresentation.degree_prime_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    Nat.Prime d
```

Two small composition/obstruction examples are included as regression
anchors; no numerical search campaign was added.

## Validation

Command run from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.GNDegreeFactorization
```

Result: success (`Build completed successfully (8667 jobs).`) with no Lean
warnings.

The new module was audited for `sorry` and `axiom`; neither was added.
`git diff --check` was also run for the working tree.

## Deferred items

- residue conditions such as `p ≡ 1 [MOD d]`;
- cyclotomic factorization of prime-degree GN;
- classification or uniqueness of `(x,u)` representations;
- primitive-prime / Zsigmondy theory;
- ABC, FLT, Legendre, and RH applications;
- logarithmic optimization of the finite search box;
- arbitrary semiring/polynomial generalization of `GN_mul_degree`;
- Body primality wrappers;
- the converse claim that prime degree produces a prime GN value.

The checkpoint stops at the necessary implication `prime GN → prime degree`.
