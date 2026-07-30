# EUC-001 Report - Standard Unit-Kernel Algebra Interface

## Goal

Expose the existing CF2D unit-kernel algebra through Lean's standard
commutative-group interface without replacing the explicit `one`, `star`, and
`conj` API.

## Repository facts inspected

`UnitKernel R` already supplies the complete algebraic data over a commutative
ring:

```text
UnitKernel.one
UnitKernel.star
UnitKernel.conj
UnitKernel.star_assoc
UnitKernel.star_comm
UnitKernel.one_star
UnitKernel.star_one
UnitKernel.conj_star
```

No existing `One`, `Mul`, `Inv`, or `CommGroup` instance for `UnitKernel` was
present.  Existing CF2D modules use the explicit operations, so their canonical
internal vocabulary remains unchanged.

## Implementation

Added:

```text
DkMath/CosmicFormula/Rotation/CF2D/KernelPower.lean
```

The module defines a `CommGroup (UnitKernel R)` instance with:

```text
one := UnitKernel.one R
mul := UnitKernel.star
inv := UnitKernel.conj
```

It also records one-way simplification bridges from standard notation to the
existing explicit operations.  The public CF2D aggregate imports the module.

## Proof route

The group laws are direct reuse of the existing preservation-kernel theorems.
No coordinate expansion, trigonometric theorem, topology, or Euclidean model is
used.  In particular, inverse cancellation is exactly `conj_star`, whose proof
ultimately uses the unit square-mass equation.

## Build command and result

From `lean/dk_math`:

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.KernelPower
  success

lake build DkMath.CosmicFormula.Rotation.CF2D
  success
```

The first aggregate attempt found a missing generated dependency file,
`Batteries/Classes/Cast.olean`.  A sequential retry rebuilt the dependency
cache and completed successfully.  This was a build-environment cache issue,
not a Lean elaboration failure in the new module.

The shell also printed the pre-existing profile warning:

```text
/home/deskuma/.bash_profile: /opt/wonderful/bin/wf-env: Permission denied
```

Lean emitted no warning for the new declarations.  No axiom, `sorry`, or
`native_decide` was introduced.

## New public declarations

```text
UnitKernel.instCommGroup
UnitKernel.mul_eq_star
UnitKernel.one_eq_unitKernelOne
UnitKernel.inv_eq_conj
```

The following interfaces are compile-checked in the module:

```text
(1 : UnitKernel ℝ)
r ^ 5
orderOf r
```

## Blocked alternatives

None.  Isolation in `KernelPower.lean` was selected so importing `Basic.lean`
alone does not silently install the standard group vocabulary.  This preserves
an explicit dependency boundary for generic algebraic users.

## Next checkpoint

EUC-002 should prove `KernelFamily.kernel_nsmul`, using standard powers and the
existing `kernel_zero_one` and `kernel_add_star` laws.
