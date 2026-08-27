# EUC-005 Report - Exact Order of the Regular Kernel

## Goal

Separate return from first return, define a generic exact-order predicate, and
prove that the positive normalized real `k`-division kernel has exact order
`k`.

## Repository facts inspected

The pinned Mathlib 4.29.0 environment provides:

```text
orderOf_eq_iff
Real.cos_eq_one_iff
Real.cos_eq_one_iff_of_lt_of_lt
Real.sin_eq_zero_iff
```

The local cosine characterization is sufficient: inside `(-2 * pi, 2 * pi)`,
`cos x = 1` holds exactly at `x = 0`.

The completed DkMath route already provides:

```text
KernelFamily.kernel_nsmul
regularKernel_pow_eq_one
regularPhaseStep
normalizedPhaseAngle
```

## Implementation

Extended `KernelPower.lean` with the generic predicate and standard-order
bridge:

```text
ExactKernelOrder
exactKernelOrder_iff_orderOf_eq
```

Extended `CycleDivision.lean` with real minimality and exact-order theorems:

```text
regularKernel_pow_ne_one_of_pos_of_lt
regularKernel_exactOrder
orderOf_regularKernel
```

The theorem holds for every positive `k`, including `k = 1`, where the
smaller-positive-power condition is vacuous.

## Proof route

Route 1 from the design was selected: direct real trigonometric zero
classification.

Assume `0 < m < k` and `regularKernel k ^ m = 1`.  Transport the power backwards
through `KernelFamily.kernel_nsmul`.  Equality of kernels then gives equality of
their core coordinates, hence:

```text
cos (normalizedPhaseAngle (m / k)) = 1
```

The inequalities `0 < m < k` imply:

```text
0 < m / k < 1
0 < normalizedPhaseAngle (m / k) < 2 * Real.pi
```

Mathlib's local cosine theorem forces this strictly positive angle to be zero,
a contradiction.  Combined with the EUC-004 return theorem, this proves exact
order.  The standard `orderOf` equation follows from the generic bridge.

No complex exponential, primitive-root structure, angle quotient, or direct
Euclidean geometry is needed.

## Build command and result

From `lean/dk_math`:

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.KernelPower
  success

lake build DkMath.CosmicFormula.Rotation.CF2D.CycleDivision
  success

lake build DkMath.CosmicFormula.Rotation.CF2D
  success
```

All focused and aggregate builds completed successfully.  The aggregate build
replayed two pre-existing `ring_nf` suggestions from `CosmicFormulaDim.lean`
and the shell's existing `/opt/wonderful/bin/wf-env` permission warning.  Lean
emitted no warning for the declarations added here.  No axiom, `sorry`, or
`native_decide` was introduced.

## New public declarations

```text
ExactKernelOrder
exactKernelOrder_iff_orderOf_eq
regularKernel_pow_ne_one_of_pos_of_lt
regularKernel_exactOrder
orderOf_regularKernel
```

## Blocked alternatives

The complex exponential and `Real.Angle` routes were not selected because the
pinned local cosine characterization closes minimality with a smaller import
and bridge surface.

## Next checkpoint

EUC-006 can now define the generic kernel orbit.  Exact order supplies the
missing ingredient for injectivity of the first `k` states at the faithful
neutral base vector.
