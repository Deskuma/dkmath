# Codex Instruction — PRIM-040 Finite Prime World Semantic Bridge

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

The current branch has already implemented the exact Legendre reduction without proving the unresolved provider.

The relevant completed surface is:

```text
DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
  KnownPrimeScales
  PrimeScaleGeneratedBy
  FreshPrimeDirection
  SupportDisjointFrom
  exists_freshPrimeDirection_of_supportDisjointFrom

DkMath.NumberTheory.Primitive.SquareBody
  squareBody
  unitSquare_body_eq
  squareBody_add_one_eq
  exists_prime_dvd_le_of_not_prime_of_le_squareBody
  prime_of_supportDisjointFrom_le_squareBody

DkMath.NumberTheory.Legendre
  SquareCell
  SquareOffset
  LegendreConjecture
  SquareAnchoredSupportEscape
  legendreConjecture_iff_squareAnchoredSupportEscape
```

The current mathematical boundary is correct:

```text
LegendreConjecture
  ↔ SquareAnchoredSupportEscape
```

is an exact reduction only.  There is no unconditional theorem supplying `SquareAnchoredSupportEscape`, and this instruction must not attempt to create one.

User-reported verification for the current implementation:

```text
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
no new sorry / admit / native_decide in changed files
```

Treat those build results as the accepted starting checkpoint.

---

## Review finding that motivates this checkpoint

`SupportDisjointFrom` now exists as the Primitive semantic predicate, but the square-Body closure and Legendre provider still spell the active finite prime world as a raw quantified condition:

```lean
∀ ⦃q : ℕ⦄, Nat.Prime q → q ≤ P → ¬ q ∣ m
```

Therefore the mathematics is connected, but the public Primitive API is not yet fully connected to the Legendre entry route.

The next checkpoint is to create the canonical finite world of all prime directions up to an anchor `P` and prove that its `SupportDisjointFrom` semantics is exactly the raw `q ≤ P` formulation.

This is PRIM-040 infrastructure.  It is not a PHZ periodicity theorem and not a Legendre-provider proof.

---

# Goal

Create a small reusable finite-prime-world module under `DkMath.NumberTheory.Primitive`.

Recommended new file:

```text
DkMath/NumberTheory/Primitive/FinitePrimeWorld.lean
```

The module should expose a canonical finite prime set

```lean
primeScalesUpTo (P : ℕ) : Finset ℕ
```

containing exactly the primes `q ≤ P`.

Then prove that

```text
SupportDisjointFrom (primeScalesUpTo P) m
```

is exactly the existing raw condition

```text
∀ ⦃q : ℕ⦄, Nat.Prime q → q ≤ P → ¬ q ∣ m.
```

This bridge is the missing semantic connector between the new Primitive facade and the existing square-Body / Legendre implementation.

---

# Required implementation surface

Names below are preferred unless existing repository conventions suggest a clearly better spelling.  Do not duplicate an existing equivalent declaration if reconnaissance finds one.

## 1. Canonical finite prime world

Implement conceptually:

```lean
def primeScalesUpTo (P : ℕ) : Finset ℕ :=
  (Finset.range (P + 1)).filter Nat.Prime
```

Required membership theorem:

```lean
@[simp] theorem mem_primeScalesUpTo {P q : ℕ} :
    q ∈ primeScalesUpTo P ↔ Nat.Prime q ∧ q ≤ P
```

The exact implementation may use an equivalent finite construction if Mathlib already provides a canonical prime finset, but keep the public semantics simple.

## 2. Known-prime certificate

Prove:

```lean
theorem knownPrimeScales_primeScalesUpTo (P : ℕ) :
    KnownPrimeScales (primeScalesUpTo P)
```

This makes the finite set a certified DkMath prime-scale world rather than an arbitrary `Finset ℕ`.

## 3. Exact support-disjoint bridge

Prove the central theorem:

```lean
theorem supportDisjointFrom_primeScalesUpTo_iff
    {P m : ℕ} :
    SupportDisjointFrom (primeScalesUpTo P) m ↔
      ∀ ⦃q : ℕ⦄, Nat.Prime q → q ≤ P → ¬ q ∣ m
```

Keep this theorem exact and elementary.  It should be only a semantic rewrite between finite-set membership and the existing quantified form.

## 4. Square-Body wrapper using the Primitive predicate

Update `DkMath.NumberTheory.Primitive.SquareBody` to import the finite-world module and add a thin wrapper of the already-proved closure theorem:

```lean
theorem prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
    {P m : ℕ}
    (hm : 1 < m)
    (hmUpper : m ≤ squareBody P)
    (hdisj : SupportDisjointFrom (primeScalesUpTo P) m) :
    Nat.Prime m
```

Do not re-prove the `minFac` argument.  Rewrite with `supportDisjointFrom_primeScalesUpTo_iff` and reuse `prime_of_supportDisjointFrom_le_squareBody`.

If a shorter theorem name is clearly better under the namespace, that is acceptable, but keep the existing raw theorem available.

## 5. Legendre semantic integration

Integrate the canonical finite prime world into `DkMath.NumberTheory.Legendre` without changing the mathematical frontier.

Preferred direction:

- express `SquareAnchoredSupportEscape` using
  `SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r)`;
- add a theorem exposing its exact raw quantified form, for example:

```lean
theorem squareAnchoredSupportEscape_iff_raw :
    SquareAnchoredSupportEscape ↔
      ∀ n : ℕ, 0 < n →
        ∃ r, SquareOffset n r ∧
          ∀ ⦃q : ℕ⦄, Nat.Prime q → q ≤ n → ¬ q ∣ n ^ 2 + r
```

Then keep

```lean
legendreConjecture_iff_squareAnchoredSupportEscape
```

as the public exact reduction theorem.

If changing the definition of `SquareAnchoredSupportEscape` would cause unnecessary churn, an acceptable fallback is to keep the current definition and add an exact equivalent provider phrased with `SupportDisjointFrom (primeScalesUpTo n)`.  However, do **not** create two competing provider concepts.  There should be one canonical semantic provider and one raw-form equivalence theorem.

---

# Public aggregation

Update:

```text
DkMath/NumberTheory/Primitive.lean
```

to import `FinitePrimeWorld` before `SquareBody`.

Keep application ownership unchanged:

```text
Primitive.lean
  finite-world semantics
  square-Body closure

Legendre.lean
  square-cell application
  unresolved universal provider
```

Do not move Legendre declarations into the Primitive core.

---

# Explicit non-goals

Do **not** implement any of the following in this checkpoint:

```text
proof of SquareAnchoredSupportEscape
proof of LegendreConjecture
primorial-specific definitions
PHZ residue periodicity
CRT child-seat update rules
prime-density estimates
PNT / analytic number theory
RH / CFBRC imports
von Mangoldt mass
category-theory abstractions
```

Do not introduce an axiom, theorem parameter, class field, or provider object that silently assumes the Legendre-equivalent escape statement.

Do not weaken the distinction:

```text
FreshPrimeDirection
  = at least one new prime divisor exists

SupportDisjointFrom
  = every old prime direction is absent
```

They are intentionally different notions.

---

# Mathematical invariants to preserve

The dependency direction must remain:

```text
CosmicFormula
    ↓
Primitive generic arithmetic
    ↓
FinitePrimeWorld
    ↓
SquareBody
    ↓
Legendre
```

No reverse application dependency.

The square-Body theorem remains generic in `P`; `P` is not a primorial and the theorem is not Legendre-specific.

The Legendre provider remains visibly unresolved.

---

# Verification

Run at least:

```sh
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

Check all touched Lean files for newly introduced:

```text
sorry
admit
native_decide
axiom
```

Do not spend effort on unrelated pre-existing warnings.

---

# Report back

Report:

1. files changed;
2. final declaration names;
3. whether `SquareAnchoredSupportEscape` was migrated to the semantic `SupportDisjointFrom` form or kept with an exact semantic wrapper;
4. the exact theorem connecting `primeScalesUpTo P` membership with `Nat.Prime q ∧ q ≤ P`;
5. the exact theorem connecting `SupportDisjointFrom (primeScalesUpTo P)` with the raw quantified condition;
6. build results;
7. confirmation that no Legendre-equivalent provider was assumed or proved.

Stop after this checkpoint.  The next review will decide whether to proceed to PHZ periodic reservation (`PRIM-041`) or another Primitive facade layer.