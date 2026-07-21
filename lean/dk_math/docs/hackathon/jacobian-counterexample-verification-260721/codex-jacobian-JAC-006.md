# Instructions

## JAC-006

Implement checkpoint JAC-006 Complex Scalar Lift for the DkMath
Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:

- JAC-001 Polynomial syntax
- JAC-002 Explicit three-point collision
- JAC-003 Formal Jacobian
- JAC-004 Determinant certificate
- JAC-005 Rational counterexample certificate

The rational MVP is complete.

Stop after JAC-006.
Do not begin determinant-one normalization or Book of Magic APIs.

Create:

lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean

## Goal

Transport the existing rational polynomial map, collision certificate,
formal Jacobian, and determinant certificate from `ℚ` to `ℂ`.

Prefer coefficient transport through `MvPolynomial.map`.
Do not duplicate the large polynomial formulas unless the transport route
proves genuinely impractical.

## Imports

Start with:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Counterexample
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
```

Adjust only where current Mathlib requires it.

## Basic complex types

Add:

```lean
abbrev Poly3C := MvPolynomial Var3 ℂ
abbrev Point3C := Var3 → ℂ
```

Define the coefficient embedding:

```lean
def qToC : ℚ →+* ℂ :=
  algebraMap ℚ ℂ
```

Define the induced polynomial ring hom:

```lean
def polyMapQC : Poly3Q →+* Poly3C :=
  MvPolynomial.map qToC
```

Equivalent formulations using `algebraMap ℚ ℂ` directly are acceptable.

## Point transport

Define:

```lean
def castPointQC (p : Point3Q) : Point3C :=
  fun i ↦ qToC (p i)
```

Then define:

```lean
def p0C : Point3C := castPointQC p0Q
def p1C : Point3C := castPointQC p1Q
def p2C : Point3C := castPointQC p2Q
def targetC : Point3C := castPointQC targetQ
```

## Polynomial transport

Define:

```lean
def counterexamplePolyC : Fin 3 → Poly3C :=
  fun i ↦ polyMapQC (counterexamplePoly i)
```

Define its actual polynomial evaluation map:

```lean
def evalCounterexampleC (p : Point3C) : Point3C :=
  fun i ↦ MvPolynomial.eval p (counterexamplePolyC i)
```

Do not define `evalCounterexampleC` by casting the result of
`evalCounterexampleQ`. It must be the actual evaluation of the complex
polynomial map.

## Evaluation transport theorem

Prove:

```lean
theorem evalCounterexampleC_castPointQC
    (p : Point3Q) :
    evalCounterexampleC (castPointQC p) =
      castPointQC (evalCounterexampleQ p) := by
  ...
```

Preferred source theorem:

```lean
MvPolynomial.map_eval
```

Its mathematical content is:

```text
cast (eval rationalPoint rationalPolynomial)
=
eval castPoint (mapCoefficients rationalPolynomial)
```

A likely proof shape is:

```lean
funext i
simpa [evalCounterexampleC, castPointQC, counterexamplePolyC,
  polyMapQC, qToC]
  using
    (MvPolynomial.map_eval
      qToC
      p
      (counterexamplePoly i)).symm
```

Adjust argument order and simplification to current Mathlib.

## Complex collision

Prove:

```lean
theorem eval_p0C :
    evalCounterexampleC p0C = targetC

theorem eval_p1C :
    evalCounterexampleC p1C = targetC

theorem eval_p2C :
    evalCounterexampleC p2C = targetC
```

These should follow from:

```text
evalCounterexampleC_castPointQC
+
eval_p0Q / eval_p1Q / eval_p2Q
```

Do not re-evaluate the full large formulas unless transport simplification
fails unexpectedly.

Also prove:

```lean
theorem p0C_ne_p1C : p0C ≠ p1C
theorem p0C_ne_p2C : p0C ≠ p2C
theorem p1C_ne_p2C : p1C ≠ p2C
```

A direct coordinate proof using `congrFun` and `norm_num` is acceptable.
Transport through injectivity of the rational cast is also acceptable.

Bundle the three-point collision:

```lean
theorem three_point_collision_C :
    p0C ≠ p1C ∧ p0C ≠ p2C ∧ p1C ≠ p2C ∧
      evalCounterexampleC p0C = targetC ∧
      evalCounterexampleC p1C = targetC ∧
      evalCounterexampleC p2C = targetC
```

Do not alter the existing rational certificate.

## Complex formal Jacobian

Define the actual formal Jacobian over `ℂ`:

```lean
def jacobianMatrixC :
    Matrix (Fin 3) (Fin 3) Poly3C :=
  fun i j ↦
    MvPolynomial.pderiv j (counterexamplePolyC i)
```

Prove that it is the coefficientwise image of the rational Jacobian:

```lean
theorem jacobianMatrixC_eq_map :
    jacobianMatrixC =
      polyMapQC.mapMatrix jacobianMatrixQ := by
  ...
```

Use:

```lean
MvPolynomial.pderiv_map
```

Preferred proof shape:

```lean
funext i j
simp [jacobianMatrixC, counterexamplePolyC, polyMapQC,
  jacobianMatrixQ, MvPolynomial.pderiv_map]
```

Do not define a second explicit 3×3 complex Jacobian unless required as a
fallback. The map theorem should be the main route.

## Complex determinant

Prove:

```lean
theorem jacobianMatrixC_det_eq_neg_two :
    jacobianMatrixC.det =
      MvPolynomial.C (-2 : ℂ) := by
  ...
```

Preferred proof chain:

```text
jacobianMatrixC
→ jacobianMatrixC_eq_map
→ RingHom.map_det
→ jacobianMatrixQ_det_eq_neg_two
→ map_C
→ C (-2 : ℂ)
```

Likely ingredients:

```lean
polyMapQC.map_det jacobianMatrixQ
```

or explicitly:

```lean
RingHom.map_det polyMapQC jacobianMatrixQ
```

The exact theorem states that mapping the determinant equals the determinant
of the coefficientwise mapped matrix.

Then prove:

```lean
theorem jacobianMatrixC_det_ne_zero :
    jacobianMatrixC.det ≠ 0
```

using the determinant equality and `norm_num` / `simp`.

## Complex noninjectivity

Prove:

```lean
theorem evalCounterexampleC_notInjective :
    ¬ Function.Injective evalCounterexampleC
```

using `p0C_ne_p1C`, `eval_p0C`, and `eval_p1C`.

Prove:

```lean
theorem evalCounterexampleC_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalCounterexampleC
```

using the injectivity consequence of a left inverse.

## Final complex certificate

Prove:

```lean
theorem jacobianCounterexampleCertificateC :
    jacobianMatrixC.det =
        MvPolynomial.C (-2 : ℂ) ∧
    jacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleC := by
  exact ⟨
    jacobianMatrixC_det_eq_neg_two,
    jacobianMatrixC_det_ne_zero,
    evalCounterexampleC_notInjective
  ⟩
```

This is the JAC-006 completion gate.

## Preferred theorem flow

```text
rational polynomial map
  ↓ coefficient map ℚ → ℂ
complex polynomial map

rational evaluations
  ↓ MvPolynomial.map_eval
complex evaluations

rational formal Jacobian
  ↓ MvPolynomial.pderiv_map
complex formal Jacobian

rational determinant
  ↓ RingHom.map_det
complex determinant
```

This checkpoint should demonstrate transport, not duplicated computation.

## Fallback rule

If the coefficient-transport route encounters substantial API friction:

1. retain `counterexamplePolyC` as the mapped rational polynomials;
2. use direct `simp` / `ring_nf` only for the blocked local theorem;
3. do not rewrite all three large polynomial definitions independently.

Only as a last resort may the complex formulas be independently restated.

Report the exact transport obstruction if this fallback is used.

## Restrictions

Do not:

- modify any rational definitions or theorems;
- redefine the complex map as a cast of the rational output;
- assume evaluation compatibility;
- assume derivative compatibility;
- assume determinant compatibility;
- use `native_decide`;
- introduce `sorry`;
- introduce axioms;
- paste an external CAS certificate;
- begin `Normalized.lean`;
- scale the first coordinate;
- prove determinant `1`;
- begin Book of Magic general APIs;
- create presentation or submission assets yet.

## Verification

Build all seven modules:

```text
DkMath.Hackathon.JacobianCounterexample3.Basic
DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
DkMath.Hackathon.JacobianCounterexample3.Collision
DkMath.Hackathon.JacobianCounterexample3.Jacobian
DkMath.Hackathon.JacobianCounterexample3.Determinant
DkMath.Hackathon.JacobianCounterexample3.Counterexample
DkMath.Hackathon.JacobianCounterexample3.ComplexLift
```

Temporary checks:

```lean
#check evalCounterexampleC_castPointQC
#check three_point_collision_C
#check jacobianMatrixC_eq_map
#check jacobianMatrixC_det_eq_neg_two
#check evalCounterexampleC_notInjective
#check jacobianCounterexampleCertificateC
```

Remove temporary checks after verification.

Run:

```text
git diff --check
```

## Report

Report:

1. exact imports;
2. definitions added;
3. exact coefficient embedding used;
4. evaluation transport theorem and proof route;
5. collision theorem names;
6. Jacobian transport theorem and proof route;
7. determinant transport theorem and proof route;
8. whether `MvPolynomial.map_eval`, `pderiv_map`, and `RingHom.map_det`
   applied directly;
9. any fallback or direct recomputation used;
10. final certificate statement;
11. build result and warnings;
12. `git diff --check` result;
13. confirmation that JAC-007 and later checkpoints were not started.

Stop after JAC-006 and wait for review.
