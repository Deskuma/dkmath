# EUC-006 Report - Finite Regular Orbit Before Polygon Geometry

## Goal

Package repeated unit-kernel action as a finite orbit and prove conservation,
successor action, periodicity, distinctness before first return, and exact
finite cardinality without defining a polygon.

## Repository facts inspected

This checkpoint uses:

```text
UnitKernel.q2_act
UnitKernel.act_star
ExactKernelOrder
exactKernelOrder_iff_orderOf_eq
pow_injOn_Iio_orderOf
regularKernel_pow_eq_one
regularKernel_exactOrder
```

Mathlib's `pow_injOn_Iio_orderOf` directly states that powers below an
element's order are injective.  This avoids a custom subtraction-and-
cancellation proof.

## Implementation

Added:

```text
DkMath/CosmicFormula/Rotation/CF2D/RegularOrbit.lean
```

The generic definition is:

```lean
kernelOrbitVertex r z j = UnitKernel.act (r ^ j) z
```

The real specialization uses the faithful neutral base `Vec.one Real` and
indexes the first `k` states by `Fin k`.

## Proof route

Square-mass conservation is immediate from action by the powered unit kernel.
The successor law uses `pow_succ'` so multiplication order agrees directly with
the action-composition theorem.  Periodicity uses `pow_add` and the neutral
`k`th power.

The key faithfulness lemma is:

```text
UnitKernel.act r (Vec.one R) = (r : Vec R)
```

Therefore equality of two neutral-base orbit states gives equality of the
corresponding kernel powers.  Exact order identifies `orderOf r` with `k`, and
`pow_injOn_Iio_orderOf` then identifies the two `Fin k` indices.

Finally, injectivity gives that the range contains exactly `k` states.

## Build command and result

From `lean/dk_math`:

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.RegularOrbit
  success

lake build DkMath.CosmicFormula.Rotation.CF2D
  success
```

Initial focused elaboration required two local corrections.  The specialized
`q2` theorem now invokes generic conservation explicitly, and cyclic successor
uses `pow_mod_orderOf` directly rather than trying to pass through the
non-wrapping successor hypothesis.  The final focused and aggregate builds
completed successfully.

The builds replayed two pre-existing `ring_nf` suggestions from
`CosmicFormulaDim.lean` and the shell's existing `/opt/wonderful/bin/wf-env`
permission warning.  Lean emitted no warning for the final new declarations.
No axiom, `sorry`, or `native_decide` was introduced.

## New public declarations

```text
kernelOrbitVertex
kernelOrbitVertex_q2
kernelOrbitVertex_succ
kernelOrbitVertex_add_period
UnitKernel.act_vecOne
kernelOrbitVertex_vecOne_injective
regularVertex
regularVertex_q2
regularVertex_succ
regularVertexNext
regularVertex_next
regularKernelOrbit_add_period
regularVertex_injective
regularVertex_ncard_range
```

## Blocked alternatives

No arbitrary-base injectivity theorem is claimed.  A general base point may
fail to detect the kernel faithfully; the neutral base has a proved recovery
law.

No edges, convex hull, polygon interior, Euclidean distance, or angle measure
was introduced.  The result is exactly a finite orbit of distinct states on
one conserved algebraic boundary.

## Next checkpoint

EUC-007 can transport these states through the existing Euclidean-plane bridge
and compare one real-trigonometric action with Mathlib's oriented rotation.
