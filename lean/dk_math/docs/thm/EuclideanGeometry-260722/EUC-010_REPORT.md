# EUC-010 Report - Public Aggregation and Final Audit

## Goal

Publish the stable EuclideanGeometry v0 theorem surface, add focused compile
and axiom checks, run the accepted broader build, and record the exact project
boundary.

## Repository facts inspected

The repository uses root aggregation modules under `DkMath/*.lean` and a
separate `DkMathTest` Lean library for inspection and axiom-audit files.

The completed stable modules are:

```text
DkMath.CosmicFormula.Rotation.CF2D.KernelPower
DkMath.CosmicFormula.Rotation.CF2D.CycleDivision
DkMath.CosmicFormula.Rotation.CF2D.RegularOrbit
DkMath.CosmicFormula.Rotation.CF2D.EuclideanRegularOrbit
DkMath.NumberTheory.EuclideanGeometry.FermatForm
DkMath.NumberTheory.EuclideanGeometry.QuadraticConstructible
```

## Implementation

Added the public aggregate:

```text
DkMath/EuclideanGeometry.lean
```

and imported it from:

```text
DkMath.lean
```

Added the compile-check and axiom-audit entry point:

```text
DkMathTest/EuclideanGeometry/Basic.lean
```

The aggregate imports only the stable modules completed in EUC-001 through
EUC-009.  It does not expose a placeholder `GaussWantzelBridge` or a false
constructibility equivalence.

## Public checks

The test entry point checks the following chain:

```text
KernelFamily.kernel_nsmul
regularKernel_pow_eq_one
ExactKernelOrder
regularKernel_exactOrder
regularVertex
regularVertex_q2
regularVertex_injective
regularVertex_ncard_range
realTrigKernel_act_euclidean_eq_rotation
euclideanRegularVertex_mem_unitSphere
euclideanRegularVertex_next_two_pi_div
euclideanRegularVertex_injective
IsGaussWantzelIndex
IsGaussWantzelIndex.exists_totient_eq_two_pow
QuadraticallyConstructibleScalar
QuadraticallyConstructibleUnitKernel.pow
QuadraticallyConstructibleRegularOrbit
quadraticallyConstructibleRegularOrbit_of_regularKernel
```

## Axiom audit

Representative final theorems were inspected with `#print axioms`:

```text
regularKernel_exactOrder
regularVertex_injective
realTrigKernel_act_euclidean_eq_rotation
IsGaussWantzelIndex.exists_totient_eq_two_pow
quadraticallyConstructibleRegularOrbit_of_regularKernel
```

Every audited theorem reports exactly the standard Lean/Mathlib dependency
surface:

```text
propext
Classical.choice
Quot.sound
```

No project-specific axiom appears.  No `sorry` or `native_decide` was added by
the EuclideanGeometry implementation.

## Build command and result

From `lean/dk_math`:

```text
lake build DkMath.EuclideanGeometry DkMathTest.EuclideanGeometry.Basic
  success (8290 jobs)

lake build DkMath
  success (8723 jobs)
```

The shell emitted the pre-existing `/opt/wonderful/bin/wf-env` permission
warning.  The build also replayed pre-existing `ring_nf` suggestions from
`CosmicFormulaDim.lean`.  No new warning was emitted by the EUC-010 files.

## Completed theorem route

The v0 branch establishes:

```text
additive parameter repetition
  -> standard unit-kernel power
  -> normalized 1/k full-cycle return
  -> action return on every q2 level
  -> exact kernel order k
  -> k distinct algebraic orbit states on q2 = 1
  -> Euclidean unit-sphere orbit
  -> oriented successor rotation by 2*pi/k
```

Independently, it establishes:

```text
Gauss-Wantzel Fermat form
  -> Euler totient is a power of two

quadratically constructible regular kernel
  -> quadratically constructible finite regular orbit
```

Thus all minimum v0 success criteria and strong criteria 7 and 8 are proved.
The constructibility layer reaches implementation Level B.

## Blocked alternatives and known TODOs

The following statements remain intentionally unproved:

```text
IsGaussWantzelIndex k
  -> QuadraticallyConstructibleUnitKernel (regularKernel k)

QuadraticallyConstructibleRegularOrbit k
  <-> IsGaussWantzelIndex k

algebraic QuadraticExpr semantics
  <-> geometric straightedge-and-compass constructibility
```

The first requires a sufficient Fermat/cyclotomic construction argument.  The
second additionally requires the converse arithmetic and construction
directions.  The third requires a geometric incidence model or a verified
bridge to one.  None is represented by an axiom, placeholder proof, or
misleading unqualified theorem name.

No claim is made that the five familiar Fermat primes are all Fermat primes.
No polygon edges, convex hull, or interior were required for the finite regular
orbit theorem.

## New public declarations

EUC-010 adds no mathematical theorem.  It adds the stable import surface
`DkMath.EuclideanGeometry` and the test/audit entry point
`DkMathTest.EuclideanGeometry.Basic`.

## Next checkpoint

The EuclideanGeometry v0 sequence is closed at EUC-010.  A future project may
begin from the explicit Level C obligation connecting `IsGaussWantzelIndex` to
constructibility of the one-step regular kernel, without modifying the proven
algebraic and Euclidean orbit core.
