# EUC-007 Report - Euclidean Interpretation of the Regular Orbit

## Goal

Transport the completed algebraic CF2D regular orbit to Mathlib's oriented
Euclidean plane and prove that it is a finite, distinct, equal-angle orbit on
the unit sphere.

## Implementation

Added:

```text
DkMath/CosmicFormula/Rotation/CF2D/EuclideanRegularOrbit.lean
```

The CF2D aggregate module now imports this interpretation layer.

## General action bridge

The central theorem is:

```lean
realTrigKernel_act_euclidean_eq_rotation
```

It proves that coordinate transport sends action by the real trigonometric
unit kernel at `theta` to Mathlib's oriented rotation by the angle represented
by `theta`.  The proof unfolds Mathlib's formula

```text
cos(theta) * v + sin(theta) * J(v)
```

and uses the existing theorem identifying the chosen orientation's
right-angle rotation with the explicit CF2D quarter-turn.  Thus the former
order-four result is preserved as a specialization of a general-angle bridge.

## Transported finite orbit

The definition

```lean
euclideanRegularVertex k j
```

is exactly `regularVertex k j` transported through the existing
`pairToEuclideanPlane`; no Euclidean plane or circle is redefined.

The implementation proves:

```text
norm_euclideanRegularVertex
euclideanRegularVertex_mem_unitSphere
regularStepAngle_eq_two_pi_div
euclideanRegularVertex_next
euclideanRegularVertex_next_two_pi_div
euclideanRegularVertex_injective
euclideanRegularVertex_ncard_range
```

Hence every state has norm one, cyclic succession is rotation by
`2 * pi / k`, the states are pairwise distinct for positive `k`, and their
range has cardinality `k`.

## Mathematical dependency

Unit-sphere membership is the Euclidean reading of the already-proved CF2D
equation `q2 = 1`.  Equal angular spacing follows from the one-step kernel
action bridge.  Distinctness is not inferred from Euclidean pictures: it is
transported from the exact algebraic kernel order established in EUC-005 and
the finite orbit theorem established in EUC-006.

This direction keeps the dependency non-circular:

```text
exact kernel order -> distinct algebraic orbit -> Euclidean equal-angle orbit
```

## Scope boundary

This checkpoint does not define polygon edges, convex hulls, interiors, or
straightedge-and-compass constructibility.  It establishes the Euclidean
vertex orbit that those later notions may interpret.

No axiom, `sorry`, or `native_decide` is introduced.

## Verification

From `lean/dk_math`:

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanRegularOrbit
lake build DkMath.CosmicFormula.Rotation.CF2D
```

Both targets completed successfully.  The build replayed the pre-existing
`ring_nf` suggestions in `CosmicFormulaDim.lean` and the shell's existing
`/opt/wonderful/bin/wf-env` permission warning; these are unrelated to EUC-007.

## Next checkpoint

EUC-008 can now define the Fermat-form arithmetic predicate independently of
this geometric interpretation.  Constructibility remains a later, separate
bridge and must not be inferred from finite periodicity.
