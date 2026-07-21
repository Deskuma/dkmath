# Instructions

## JAC-003

Implement checkpoint JAC-003 Formal Jacobian for the DkMath
Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Current completed checkpoints:

- JAC-001 Polynomial syntax
- JAC-002 Explicit three-point collision

Do not implement JAC-004 determinant computation yet.

Create:

lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean

Import:

DkMath.Hackathon.JacobianCounterexample3.PolynomialMap

and the minimal current Mathlib modules required for:

- `MvPolynomial.pderiv`
- `Matrix`
- 3×3 matrix notation
- the tactics used in the component proofs

Use the current Mathlib matrix-notation import:

```lean
import Mathlib.LinearAlgebra.Matrix.Notation
```

Do not use the obsolete design-draft import
`Mathlib.Data.Matrix.Notation`.

## Required definitions

Define the formal Jacobian directly from `MvPolynomial.pderiv`.

```lean
def jacobianMatrixQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  fun i j ↦ MvPolynomial.pderiv j (counterexamplePoly i)
```

Define an explicit 3×3 matrix:

```lean
def explicitJacobianQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  !![
    ...;
    ...;
    ...
  ]
```

The explicit entries must be obtained by normalizing the actual
`pderiv` expressions. Do not treat a separately hand-derived matrix as
an independent source of truth.

The expected mathematical entries may be written using:

```lean
s := 1 + x * y
```

conceptually, but avoid introducing a local abbreviation if it makes
simp/ring normalization harder.

Expected rows:

First row, derivatives of `counterexampleP`:

```text
∂P/∂x =
  3 * y * (1 + x*y)^2 * z
  + y^3 * (7 + 6*x*y)

∂P/∂y =
  3 * x * (1 + x*y)^2 * z
  + 2*y*(1 + x*y)*(4 + 3*x*y)
  + x*y^2*(7 + 6*x*y)

∂P/∂z =
  (1 + x*y)^3
```

Second row, derivatives of `counterexampleQ`:

```text
∂Q/∂x =
  3*(1 + x*y)^2*z
  + 6*x*y*(1 + x*y)*z
  + 3*y^2*(4 + 3*x*y)
  + 9*x*y^3

∂Q/∂y =
  1
  + 6*x^2*(1 + x*y)*z
  + 6*x*y*(4 + 3*x*y)
  + 9*x^2*y^2

∂Q/∂z =
  3*x*(1 + x*y)^2
```

Third row, derivatives of `counterexampleR`:

```text
∂R/∂x =
  2 - 6*x*y - 3*x^2*z

∂R/∂y =
  -3*x^2

∂R/∂z =
  -x^3
```

Equivalent polynomial normal forms are acceptable.

## Required theorem

```lean
theorem jacobianMatrixQ_eq_explicit :
    jacobianMatrixQ = explicitJacobianQ := by
  ...
```

Preferred proof route:

```lean
ext i j
fin_cases i <;> fin_cases j
```

For each of the nine goals, unfold only the required definitions:

```lean
jacobianMatrixQ
explicitJacobianQ
counterexamplePoly
counterexampleP
counterexampleQ
counterexampleR
x
y
z
```

Then use ordinary kernel-checked normalization:

```lean
simp
ring
```

or:

```lean
simp
ring_nf
```

## Allowed fallback

If the single matrix equality proof becomes too large or brittle, split
the proof into three row lemmas:

```lean
jacobianMatrixQ_row_zero
jacobianMatrixQ_row_one
jacobianMatrixQ_row_two
```

and combine them into `jacobianMatrixQ_eq_explicit`.

Do not split into nine public theorems unless technically necessary.
Private helper lemmas are acceptable.

## Restrictions

Do not:

- compute the determinant;
- prove that the determinant is `-2`;
- define the final counterexample certificate;
- implement the complex lift;
- implement the determinant-one normalization;
- use `native_decide`;
- introduce `sorry`;
- introduce axioms;
- paste an external CAS certificate;
- define the Jacobian solely as the explicit handwritten matrix.

The actual Jacobian must remain:

```lean
fun i j ↦ MvPolynomial.pderiv j (counterexamplePoly i)
```

## Verification

Build only:

```text
DkMath.Hackathon.JacobianCounterexample3.Basic
DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
DkMath.Hackathon.JacobianCounterexample3.Collision
DkMath.Hackathon.JacobianCounterexample3.Jacobian
```

Add temporary local checks if useful:

```lean
#check jacobianMatrixQ
#check explicitJacobianQ
#check jacobianMatrixQ_eq_explicit
```

Remove temporary checks before completion unless they belong in an
intentional demo file.

## Report

Report:

1. exact imports used;
2. exact form chosen for all nine explicit entries;
3. theorem names added;
4. whether a single `ext/fin_cases` proof closed;
5. any `pderiv` simplification friction;
6. whether row helper lemmas were needed;
7. build result and warnings;
8. confirmation that determinant computation was not started.

Stop after JAC-003 and wait for review.
