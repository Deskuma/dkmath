# Instructions

## JAC-010

Implement checkpoint JAC-010 GN Finite Difference for the DkMath
Book of Magic layer.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:

- JAC-001 through JAC-009
- rational, complex, and determinant-one Jacobian certificates
- public import and axiom audit
- generic UniqueGap / GapCrystal API
- Jacobian GapCrystal bridge

Stop after JAC-010.

Do not begin PrincipalPartCompletion, higher-dimensional padding,
Demo, submission documents, or presentation assets.

## Mathematical objective

For a univariate polynomial

```text
P(T) = Σ aₙ Tⁿ
```

formalize the GN finite-difference identity:

```text
P(t + h) - P(t)
=
h * Σ aₙ GN n h t
```

and then derive, when `h ≠ 0`:

```text
(P(t + h) - P(t)) / h
=
Σ aₙ GN n h t
```

Use the existing DkMath theorem:

```lean
DkMath.CosmicFormulaBinom.cosmic_id_csr'
```

whose relevant specialization is:

```text
(h + t)^n = h * GN n h t + t^n
```

Do not reprove the binomial GN identity.

## 1. Create the module

Create:

```text
lean/dk_math/DkMath/BookOfMagic/GNFiniteDifference.lean
```

Suggested imports:

```lean
import DkMath.CosmicFormula.CosmicFormulaBinom
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic
```

Adjust the exact imports to the current Mathlib graph, but do not use the
entire root `DkMath` import.

Use:

```lean
namespace DkMath.BookOfMagic

open scoped BigOperators
```

## 2. Define the GN coefficient sum

Prefer a genuine `Polynomial R`, rather than a manually bounded coefficient
array.

Define:

```lean
def GNFiniteDifference
    {R : Type*}
    [CommSemiring R]
    (p : Polynomial R)
    (h t : R) : R :=
  p.sum fun n a ↦
    a * DkMath.CosmicFormulaBinom.GN n h t
```

The `n = 0` term vanishes automatically because:

```text
GN 0 h t = 0
```

Thus this is mathematically the sum over positive exponents without needing
a separate filtered coefficient representation.

## 3. Basic API

Prove a support-sum description:

```lean
theorem GNFiniteDifference_eq_support_sum
    {R : Type*}
    [CommSemiring R]
    (p : Polynomial R)
    (h t : R) :
    GNFiniteDifference p h t =
      ∑ n ∈ p.support,
        p.coeff n *
          DkMath.CosmicFormulaBinom.GN n h t := by
  ...
```

Preferred route:

```lean
simp [GNFiniteDifference, Polynomial.sum_def]
```

or `rfl` if the current definition unfolds directly.

Prove the essential additive rules:

```lean
@[simp]
theorem GNFiniteDifference_zero
    {R : Type*}
    [CommSemiring R]
    (h t : R) :
    GNFiniteDifference (0 : Polynomial R) h t = 0
```

```lean
theorem GNFiniteDifference_add
    {R : Type*}
    [CommSemiring R]
    (p q : Polynomial R)
    (h t : R) :
    GNFiniteDifference (p + q) h t =
      GNFiniteDifference p h t +
      GNFiniteDifference q h t
```

Use `Polynomial.sum_add_index`. The coefficient function is additive in its
coefficient argument.

Prove the monomial rule:

```lean
@[simp]
theorem GNFiniteDifference_monomial
    {R : Type*}
    [CommSemiring R]
    (n : ℕ)
    (a h t : R) :
    GNFiniteDifference (Polynomial.monomial n a) h t =
      a * DkMath.CosmicFormulaBinom.GN n h t
```

Use `Polynomial.sum_monomial_index`.

A constant corollary is useful but optional:

```lean
@[simp]
theorem GNFiniteDifference_C
    {R : Type*}
    [CommSemiring R]
    (a h t : R) :
    GNFiniteDifference (Polynomial.C a) h t = 0
```

Do not add a large collection of routine simp lemmas.

## 4. Division-free main theorem

Prove:

```lean
theorem eval_add_sub_eval_eq_mul_GNFiniteDifference
    {R : Type*}
    [CommRing R]
    (p : Polynomial R)
    (h t : R) :
    p.eval (t + h) - p.eval t =
      h * GNFiniteDifference p h t := by
  ...
```

Preferred proof architecture:

```text
Polynomial.induction_on'
```

### Additive case

Use:

```text
Polynomial.eval_add
GNFiniteDifference_add
the two induction hypotheses
ring
```

### Monomial case

Reduce to:

```text
a * (t + h)^n - a * t^n
=
h * (a * GN n h t)
```

Obtain:

```lean
have hGN :=
  DkMath.CosmicFormulaBinom.cosmic_id_csr'
    (R := R) n h t
```

This gives:

```text
(h + t)^n = h * GN n h t + t^n
```

Rewrite `t + h = h + t`, apply `hGN`, and close by `ring`.

A likely shape is:

```lean
induction p using Polynomial.induction_on' with
| add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add,
      GNFiniteDifference_add, hp, hq]
    ring
| monomial n a =>
    simp only [Polynomial.eval_monomial,
      GNFiniteDifference_monomial]
    have hGN :=
      DkMath.CosmicFormulaBinom.cosmic_id_csr'
        (R := R) n h t
    rw [show t + h = h + t by ac_rfl, hGN]
    ring
```

Adjust case names and simplification to the current induction API.

Do not replace the proof with a fresh expansion of every power.

## 5. Difference-quotient corollary

Over a field, prove:

```lean
theorem differenceQuotient_eq_GNFiniteDifference
    {K : Type*}
    [Field K]
    (p : Polynomial K)
    (h t : K)
    (hh : h ≠ 0) :
    (p.eval (t + h) - p.eval t) / h =
      GNFiniteDifference p h t := by
  ...
```

Preferred route:

```lean
rw [eval_add_sub_eval_eq_mul_GNFiniteDifference]
simp [hh]
```

Use `field_simp` only if ordinary simplification does not close the final
cancellation.

The division-free theorem is the primary theorem. The quotient theorem is a
corollary and must retain the explicit condition `h ≠ 0`.

## 6. Small concrete verification

Add one compact theorem or example showing the cubic monomial specialization:

```lean
example {R : Type*} [CommRing R] (h t : R) :
    Polynomial.eval (t + h) (Polynomial.X ^ 3) -
        Polynomial.eval t (Polynomial.X ^ 3) =
      h * DkMath.CosmicFormulaBinom.GN 3 h t := by
  ...
```

Prefer deriving this from the general theorem or the monomial rule.

Do not independently expand the cubic with `ring` as the only proof source.

This example may remain only if it adds clear documentation value.
Otherwise use it temporarily and remove it after verification.

## 7. Public aggregator

Modify:

```text
lean/dk_math/DkMath/BookOfMagic.lean
```

Add:

```lean
import DkMath.BookOfMagic.GNFiniteDifference
```

Keep the existing imports:

```lean
import DkMath.BookOfMagic.UniqueGapContract
import DkMath.BookOfMagic.GapCrystal
```

Do not make `GNFiniteDifference` depend on Hackathon modules.

Because `DkMath.lean` already imports `DkMath.BookOfMagic`, no new root import
should be required.

## 8. Public checks

Using a temporary file with:

```lean
import DkMath
```

verify:

```lean
#check DkMath.BookOfMagic.GNFiniteDifference
#check DkMath.BookOfMagic.GNFiniteDifference_eq_support_sum
#check DkMath.BookOfMagic.GNFiniteDifference_add
#check DkMath.BookOfMagic.GNFiniteDifference_monomial
#check DkMath.BookOfMagic.eval_add_sub_eval_eq_mul_GNFiniteDifference
#check DkMath.BookOfMagic.differenceQuotient_eq_GNFiniteDifference
```

Remove the temporary check file afterward.

## 9. Verification

Build:

```text
DkMath.BookOfMagic.GNFiniteDifference
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

The existing Jacobian certificate proofs must remain unchanged.

Run:

```text
git diff --check
```

## Restrictions

Do not:

- reprove the definition or binomial identity of `GN`;
- define a competing `GN`;
- make the Book of Magic layer depend on Hackathon code;
- modify the Jacobian map or its certificates;
- introduce `sorry`;
- introduce axioms;
- use `native_decide`;
- begin PrincipalPartCompletion;
- begin higher-dimensional Jacobian padding;
- create Demo or submission assets.

## Report

Report:

1. files created and modified;
2. exact imports;
3. exact definition of `GNFiniteDifference`;
4. basic API theorem statements;
5. proof architecture of the division-free theorem;
6. exact use of `cosmic_id_csr'`;
7. quotient theorem and its cancellation route;
8. any friction with `Polynomial.induction_on'` or `Polynomial.sum`;
9. whether any direct power re-expansion fallback was used;
10. public check results;
11. build results and warnings;
12. existing Jacobian axiom-audit result;
13. `git diff --check` result;
14. confirmation that JAC-011 and later work was not started.

Stop after JAC-010 and wait for review.
