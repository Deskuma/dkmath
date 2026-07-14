# Codex report 132: mapped edge bridge and next inference

## Implemented result

The edge-level mapping bridge is now formalized in
`DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`.

The main theorem is:

```lean
shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
```

It states that mapping a quotient chart edge path by the descended semantic
evaluation, then relabelling endpoints to the finite fixed-boundary endpoint
API, gives exactly the corresponding observed semantic edge path.

Concrete aliases were also added for edges `0`, `1`, `2`, and `3`:

```lean
shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge
```

## Experimental result

A direct four-edge theorem was tested:

```lean
map shiftedCyclicFourPathViaEdges = shiftedSemanticObservedCyclicFourPathViaEdges
```

The proof did not close by unfolding and simplification. The remaining goal is
not semantic: each mapped edge already agrees with the observed edge. The
remaining obstruction is transporting those four edge equalities through the
nested `Path.trans` and `Path.cast` structure of
`shiftedFourPathConcatWithSeams`.

## Inference for the next implementation

The next useful theorem should not re-open the semantic definitions. It should
be a path-packaging theorem:

```lean
shiftedFourPathConcatWithSeams_map_congr
```

Expected role:

1. Map each of the four component paths.
2. Rewrite mapped component paths using edge-level bridge theorems.
3. Use `shiftedPath_cast_proof_irrel` to ignore differences between mapped
   quotient seam proof terms and finite seam proof terms.

This should turn the current problem from a semantic evaluation theorem into a
generic four-path concatenator normalization theorem.

## Current safe conclusion

Endpoint mismatch is solved.

Single-edge semantic mapping is solved.

The remaining checkpoint is four-edge seam proof alignment under the common
concatenator.
