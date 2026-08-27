# EUC-002 Report - Natural Additive Repetition and Kernel Power

## Goal

Prove that natural-number repetition in the additive parameter of a
`KernelFamily` is transported to the corresponding natural power of its unit
kernel:

```text
K(n • t) = K(t) ^ n
```

Also expose the directly related bridge from kernel powers to finite action
iteration, because it is the mechanism used by the next cycle-return phase.

## Repository facts inspected

The implementation reuses:

```text
KernelFamily.kernel_zero_one
KernelFamily.kernel_add_star
UnitKernel.act_one
UnitKernel.act_star
UnitKernel.mul_eq_star
```

The pinned Lean 4.29.0 environment supplies the recursion laws in the required
orientation:

```text
succ_nsmul
pow_succ
Function.iterate_succ_apply
```

## Implementation

Extended:

```text
DkMath/CosmicFormula/Rotation/CF2D/KernelPower.lean
```

with two generic theorems:

```lean
KernelFamily.kernel_nsmul
UnitKernel.pow_act
```

Both remain in the algebraic CF2D layer.  The module imports `Trig.lean` only
for the existing `KernelFamily` definition and laws; it imports no real
analysis, topology, `DkReal`, or Euclidean geometry.

## Proof route

`KernelFamily.kernel_nsmul` is induction on `n`.

```text
n = 0:
  kernel zero is the neutral unit kernel

n + 1:
  successor nsmul becomes n • t + t
  kernel addition becomes star
  the induction hypothesis and pow_succ identify the result
```

`UnitKernel.pow_act` is the parallel induction for actions.  At the successor
step, `act_star` turns multiplication into action composition and
`Function.iterate_succ_apply` identifies that composition with the next finite
iterate.

Neither proof expands the core or beam coordinates.

## Build command and result

From `lean/dk_math`:

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.KernelPower
  success

lake build DkMath.CosmicFormula.Rotation.CF2D
  success
```

The first focused elaboration exposed that the action state had to be
generalized in the induction for `UnitKernel.pow_act`.  After changing the
induction to `induction n generalizing z`, both focused and aggregate builds
completed successfully.

The shell printed the pre-existing `/opt/wonderful/bin/wf-env` permission
warning.  Lean emitted no warning for the new declarations.  No axiom,
`sorry`, or `native_decide` was introduced.

## New public declarations

```text
KernelFamily.kernel_nsmul
UnitKernel.pow_act
```

## Blocked alternatives

No fallback `KernelFamily.kernelPower` recursion was needed.  The standard
power surface introduced by EUC-001 composes directly with the existing
kernel-family law.

Coordinate consequences such as `cfcos_nsmul` and `cfsin_nsmul` were not added:
the kernel equality is stronger, and no current downstream proof requires the
projected forms.

## Next checkpoint

EUC-003 should combine `KernelFamily.kernel_nsmul` with an abstract equation
`k • step = period` and a neutral-period hypothesis.  `UnitKernel.pow_act` then
turns that kernel return into a return theorem for every two-component state.
