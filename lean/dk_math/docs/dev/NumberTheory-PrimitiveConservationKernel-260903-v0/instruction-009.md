# PCK-007 — Canonical {2,3,5} → 30 → 960 regression instructions

Date: 2026-09-04  
Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`  
Predecessor: `report-008.md` / PCK-006

## 0. Authorization

Implement the canonical concrete regression:

```text
{2,3,5}
  -> finitePrimeBasisProduct = 30
  -> complete closure primeScalesUpTo 30
  -> squareBody 30 = 960 = 31^2 - 1
  -> squarePrimeExpansion 30 = primeScalesUpTo 960
```

This checkpoint is concrete only. Do not introduce another abstraction.

Central firewall:

> `{2,3,5}` is the generating basis, not the complete prime support through 30.

## 1. Preferred owner

Create:

`DkMath/NumberTheory/PrimorialUniverse/ThirtySquareWorld.lean`

Namespace:

`DkMath.NumberTheory.PrimorialUniverse`

Preferred import:

`import DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge`

Do not import PHZ30 merely to name the basis. Use the literal Finset and reuse `finitePrimeBasisProduct_two_three_five`.

No public aggregator change.

## 2. Basis to complete-closure regression

Do not duplicate the existing product theorem.

Add:

```lean
theorem primeBasis235_subset_primeScalesUpTo_thirty :
    ({2, 3, 5} : Finset ℕ) ⊆
      DkMath.NumberTheory.Primitive.primeScalesUpTo 30 := by
  ...
```

Proof route:
- prove `IsFinitePrimeBasis ({2,3,5} : Finset ℕ)` locally;
- apply `finitePrimeBasis_subset_primeScalesUpTo_product`;
- rewrite by `finitePrimeBasisProduct_two_three_five`.

## 3. Explicit complete closure at 30

Add the exact equality:

```lean
theorem primeScalesUpTo_thirty_eq :
    DkMath.NumberTheory.Primitive.primeScalesUpTo 30 =
      ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
  ...
```

`decide`, `norm_num`, or a finite extensional proof is acceptable. Do not use `native_decide`.

This theorem is intentionally concrete and makes the basis/closure distinction visible.

## 4. Square endpoint regressions

Add:

```lean
@[simp] theorem squareBody_thirty :
    DkMath.NumberTheory.Primitive.squareBody 30 = 960 := by
  ...

theorem squareBody_thirty_add_one_eq_thirtyOne_sq :
    DkMath.NumberTheory.Primitive.squareBody 30 + 1 = 31 ^ 2 := by
  ...
```

The second theorem should reuse `squareBody_add_one_eq`.

## 5. PCK-005 expansion regression

Add:

```lean
theorem squarePrimeExpansion_thirty_eq_primeScalesUpTo_960 :
    DkMath.NumberTheory.Primitive.squarePrimeExpansion 30 =
      DkMath.NumberTheory.Primitive.primeScalesUpTo 960 := by
  ...
```

Preferred proof:
- apply `squarePrimeExpansion_eq_primeScalesUpTo_squareBody 30`;
- rewrite by `squareBody_thirty`.

This is the concrete finite closure

$$
\mathcal P_{\le30} \longmapsto \mathcal P_{\le960}.
$$

Do not enumerate all primes through 960.

## 6. All fine anchors under 30

Add:

```lean
theorem prime_of_supportDisjointFrom_thirtyClosure_of_le_fine_squareBody
    {q m : ℕ}
    (hq : q ≤ 30)
    (hm : 1 < m)
    (hmUpper :
      m ≤ DkMath.NumberTheory.Primitive.squareBody q)
    (hdisj :
      DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
        (DkMath.NumberTheory.Primitive.primeScalesUpTo 30) m) :
    Nat.Prime m := by
  ...
```

Use the PCK-006 product-anchor theorem with `S = {2,3,5}` and rewrite the product to 30. Do not bypass PCK-006 with a direct PCK-003 call.

## 7. Representative fine square boundaries

Add one packet theorem, preferably:

```lean
theorem representative_fine_square_boundaries_under_thirty :
    DkMath.NumberTheory.Primitive.squareBody 6 + 1 = 7 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 10 + 1 = 11 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 12 + 1 = 13 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 16 + 1 = 17 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 18 + 1 = 19 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 22 + 1 = 23 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 28 + 1 = 29 ^ 2 ∧
    DkMath.NumberTheory.Primitive.squareBody 30 + 1 = 31 ^ 2 := by
  ...
```

Equivalent packet shape is acceptable. Reuse `squareBody_add_one_eq` plus numeral normalization where practical.

## 8. Required 49 basis-vs-closure firewall

Add a concrete negative regression showing that 49 survives the basis but not the complete closure:

```lean
theorem fortyNine_basis_vs_completeClosure_firewall :
    DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
        ({2,3,5} : Finset ℕ) 49 ∧
    ¬ DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
        (DkMath.NumberTheory.Primitive.primeScalesUpTo 30) 49 ∧
    ¬ Nat.Prime 49 := by
  ...
```

Use the witness prime 7 for the complete-closure failure.

This theorem permanently blocks the invalid inference

```text
SupportDisjointFrom {2,3,5} n
  -> n is prime up to 960
```

and the equivalent `gcd(n,30)=1` misuse.

## 9. Optional strict-subset theorem

If trivial, you MAY add:

```lean
theorem primeBasis235_ssubset_primeScalesUpTo_thirty :
    ({2,3,5} : Finset ℕ) ⊂
      DkMath.NumberTheory.Primitive.primeScalesUpTo 30 := by
  ...
```

Do not spend significant proof engineering on it.

## 10. Module docstring interpretation

Record the exact two-stage closure:

$$
\{2,3,5\}
\longrightarrow 30
\longrightarrow \mathcal P_{\le30}
\longrightarrow \mathcal P_{\le960}.
$$

The first arrow is product synchronization.

The second arrow is completion of prime support, not wheel survival.

The third arrow is PCK-005 square expansion.

The same complete support `primeScalesUpTo 30` certifies every fine square world `q ≤ 30`.

The endpoint is `960 = 31^2 - 1`.

Do not claim Legendre, one-prime-per-square-interval, or unbounded generation.

## 11. Firewalls

PCK-007 must not:
- identify `{2,3,5}` with `primeScalesUpTo 30`;
- identify wheel/PHZ survivors with primes;
- enumerate all primes through 960;
- add a new prime-support or primorial definition;
- implement PCK-008;
- add Gnomon resolution/projective theorems;
- import RH, zeta, Xi, PHZ analytic, or CFBRC modules;
- use `sorry`, `admit`, `native_decide`, or a project axiom;
- modify public aggregators.

## 12. Verification

Run at least:

```text
lake build DkMath.NumberTheory.PrimorialUniverse.ThirtySquareWorld
git diff --check
```

Run axiom checks on:
- `primeBasis235_subset_primeScalesUpTo_thirty`
- `primeScalesUpTo_thirty_eq`
- `squarePrimeExpansion_thirty_eq_primeScalesUpTo_960`
- `prime_of_supportDisjointFrom_thirtyClosure_of_le_fine_squareBody`
- `fortyNine_basis_vs_completeClosure_firewall`

## 13. Report

Create:

`lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-009.md`

Record outcome, starting HEAD, changed files, imports, the full basis→product→closure→960 chain, fine-anchor packet, 49 firewall, build/diff/axiom audit, and next authorization.

## 14. Next authorization

If PCK-007 is green, authorize only:

> PCK-008 — primitive-kernel dichotomy wrapper.

PCK-008 should package the already-existing `primeScaleGeneratedBy_or_uniqueFresh_small_split_of_le_squareBody` theorem into the campaign semantic surface. Do not re-prove factorization or fresh-prime uniqueness.