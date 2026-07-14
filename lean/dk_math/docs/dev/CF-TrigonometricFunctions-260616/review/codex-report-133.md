# Codex report 133

## Goal

Lift the solved single-edge semantic mapping bridge through the canonical
four-edge shifted path concatenator.

The pre-geometric rule was preserved: no circle, angle, arc, degree, or pi
vocabulary was introduced in Lean theorem names.

## Implemented Lean results

Target module:

```text
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
```

New path-concatenator bookkeeping theorem:

```text
shiftedFourPathConcatWithSeams_congr_cast_irrel
```

This theorem states that once the four component paths are equal, changing the
seam proof terms does not change the resulting four-edge concatenated path.
It is the required proof-irrelevance bridge for nested `Path.trans` and
`Path.cast` packages.

New mapped-edge-to-observed-edge theorems:

```text
shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_apply
shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge
```

New four-edge mapped-concatenation theorem:

```text
shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges
```

This proves:

```text
map each quotient edge by descended semantic evaluation
  -> relabel endpoints by semantic endpoint equalities
  -> glue the four mapped edges
=
canonical observed semantic via-edge path
```

Thus the edgewise version of the quotient-to-semantic path bridge is now
formalized.

## Experiment result

Lean accepted the proof-irrelevance route directly.

The important implementation observation is that the blocker was not the
semantic action, the fixed boundary, or the cyclic quotient relation. The
blocker was purely the dependent shape of Mathlib `Path`:

```text
Path.map
Path.trans
Path.cast
endpoint proof terms
seam proof terms
```

Once the four edge paths were identified, `Path.ext` reduced the remaining
seam proof differences to proof-irrelevant endpoint bookkeeping.

## Remaining theorem

The next target is the global map-through-gluing theorem:

```text
map the already-glued quotient four-path
=
glue the four mapped quotient edges
```

Candidate direction:

```text
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
```

After that, the older endpoint-casted observed quotient path should compare
to the canonical observed via-edge path, and then to the existing finite
four-level path.

## DkPath inference

This checkpoint gives a clear design requirement for a DkMath-native path
wrapper.

Mathlib `Path` combines three layers:

```text
trace:
  the continuous function from the unit interval

endpoint labels:
  dependent source and target indices

seam witnesses:
  proof terms used to type concatenation
```

For DkMath's `DkPath`, the public API should make these layers explicit.
In particular, the following theorems should be first-class:

```text
map_cast
map_trans
cast_proof_irrel
four_concat_congr_cast_irrel
```

This would make `DkPath <-> Mathlib Path` plausible as a bridge:

```text
DkPath:
  optimized for DkMath trace/seam reasoning

Mathlib Path:
  used as the external topology-compatible continuous path object
```

The current implementation is already functioning as the Mathlib side of that
bridge. The next proof should test whether the global map-through-gluing law
can be obtained generically for `shiftedFourPathConcatWithSeams`, or whether a
specialized theorem for `ShiftedCyclicChart` is the lower-friction route.

## Verification

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
```

passed.
