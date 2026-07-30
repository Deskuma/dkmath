# EUC-009 Report - Algebraic Quadratic Constructibility Boundary

## Goal

Introduce a precise algebraic model of finite quadratic construction, prove
its closure laws, and lift constructibility from a unit kernel to its finite
CF2D orbit without claiming a completed straightedge-and-compass theorem.

## Repository facts inspected

The pinned Mathlib contains extensive field, polynomial, and quadratic-
extension infrastructure, but the repository search found no complete public
API formalizing the straightedge-and-compass Gauss-Wantzel theorem or a ready
predicate matching this project's intended scalar semantics.

The existing DkMath orbit layer supplies:

```text
Vec.star
UnitKernel.act
kernelOrbitVertex
regularVertex
regularKernel
```

These are sufficient for the Level B lift once scalar closure is available.

## Implementation

Added:

```text
DkMath/NumberTheory/EuclideanGeometry/QuadraticConstructible.lean
```

The syntax `QuadraticExpr` contains rational constants, addition, negation,
multiplication, inverse, and nonnegative square root.  Evaluation into `Real`
is total.  The separate predicate `QuadraticExpr.Valid` recursively requires:

```text
inverse input != 0
sqrt input >= 0
```

This avoids dependent proof fields inside the recursive syntax while retaining
the mathematical side conditions.

## Proof route

`QuadraticallyConstructibleScalar x` means that a valid finite expression
evaluates to `x`.  Witness composition proves closure under:

```text
rational constants
zero and one
addition and subtraction
negation
multiplication
nonzero inverse
nonnegative square root
natural powers
```

The coordinate predicates are then layered as:

```text
QuadraticallyConstructibleVec
QuadraticallyConstructibleUnitKernel
QuadraticallyConstructibleRegularOrbit
```

The CF2D star coordinate formulas use only addition, subtraction, and
multiplication.  Therefore constructible vectors are closed under `star`,
constructible unit kernels are closed under multiplication and powers, and a
constructible kernel acts on a constructible state constructibly.

Since `Vec.one Real` has rational coordinates, every state

```text
kernelOrbitVertex r (Vec.one Real) j
```

is constructible when `r` is.  Specialization gives the Level B theorem:

```text
QuadraticallyConstructibleUnitKernel (regularKernel k)
  -> QuadraticallyConstructibleRegularOrbit k
```

## New public declarations

```text
QuadraticExpr
QuadraticExpr.eval
QuadraticExpr.Valid
QuadraticallyConstructibleScalar
QuadraticallyConstructibleScalar.rat
QuadraticallyConstructibleScalar.zero
QuadraticallyConstructibleScalar.one
QuadraticallyConstructibleScalar.add
QuadraticallyConstructibleScalar.neg
QuadraticallyConstructibleScalar.sub
QuadraticallyConstructibleScalar.mul
QuadraticallyConstructibleScalar.inv
QuadraticallyConstructibleScalar.sqrt
QuadraticallyConstructibleScalar.pow
QuadraticallyConstructibleVec
QuadraticallyConstructibleVec.one
QuadraticallyConstructibleVec.star
QuadraticallyConstructibleUnitKernel
QuadraticallyConstructibleUnitKernel.one
QuadraticallyConstructibleUnitKernel.mul
QuadraticallyConstructibleUnitKernel.pow
quadraticallyConstructibleVec_act
quadraticallyConstructible_kernelOrbitVertex
QuadraticallyConstructibleRegularOrbit
quadraticallyConstructibleRegularOrbit_of_regularKernel
```

## Scope boundary

The qualified word `QuadraticallyConstructible` is intentional.  No theorem
yet identifies this expression semantics with geometric line-circle
constructibility.

This checkpoint reaches implementation Level B.  It does not prove:

```text
IsGaussWantzelIndex k
  -> QuadraticallyConstructibleUnitKernel (regularKernel k)

QuadraticallyConstructibleRegularOrbit k
  <-> IsGaussWantzelIndex k
```

Those statements require cyclotomic or quadratic-extension arguments and, for
the final geometric wording, an equivalence between the algebraic syntax and
straightedge-and-compass constructions.

Periodicity, exact kernel order, and the Fermat-form predicate are kept
logically separate from the closure theorem proved here.

No axiom, `sorry`, or `native_decide` was introduced.

## Build command and result

From `lean/dk_math`:

```text
lake build DkMath.NumberTheory.EuclideanGeometry.QuadraticConstructible
  success

lake build DkMath.CosmicFormula.Rotation.CF2D
  success
```

The focused target emitted no warning for the new declarations.  The shell's
existing `/opt/wonderful/bin/wf-env` permission warning and the pre-existing
`ring_nf` suggestions replayed through CF2D are unrelated to EUC-009.

## Blocked alternatives

A direct line-circle incidence model was not introduced because no complete
matching Mathlib API was found and it would add degeneracy and intersection
choice obligations before the algebraic closure layer is established.

The full Gauss-Wantzel equivalence is not represented by an axiom or placeholder
theorem.

## Next checkpoint

EUC-010 can create the stable public aggregate and compile checks for the
completed algebraic, Euclidean, arithmetic, and Level B constructibility
surfaces.  The sufficient Fermat-index direction remains an explicitly later
research bridge.
