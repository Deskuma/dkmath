# Codex report 134

## Goal

Prove the global map-through-gluing theorem for the shifted cyclic four-path.

The previous checkpoint proved the edgewise bridge:

```text
map each quotient edge
  -> relabel endpoints
  -> glue four mapped edges
=
canonical observed semantic via-edge path
```

This checkpoint proves that this edgewise package is also obtained by mapping
the already-glued quotient four-path.

## Implemented Lean results

Target module:

```text
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
```

New generic four-path map theorem:

```text
shiftedFourPathConcatWithSeams_map
```

This is the reusable DkMath-named four-edge version of Mathlib's
`Path.map_trans`: mapping the canonical four-edge concatenator agrees with
concatenating the four mapped edges.

New semantic global map-through-gluing theorems:

```text
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
```

These prove that descended semantic evaluation commutes with the canonical
quotient four-path package.

New final comparison theorems:

```text
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
```

The endpoint-cast observed quotient path is now equal to the existing finite
four-level shifted path. The value-level theorem exposes the same result on
the underlying `Vec` values.

## Experiment result

The fully generic theorem was feasible.

The first proof attempt used only `Path.ext; funext; rfl`, but Lean rejected
it because the mapped nested `Path.trans` structure is not definitionally
equal to the nested concatenation of mapped paths.

After destructing the seam equalities and simplifying the common
concatenator, Lean accepted:

```text
cases seam proofs
simp [shiftedFourPathConcatWithSeams]
```

This is an important implementation signal. The four-path map theorem is not
semantic-specific and should belong to the reusable path-packaging layer.

## DkPath inference

The future DkPath layer now has a sharper minimum API.

Already validated by Lean:

```text
cast_apply
map_cast
map_trans
cast_proof_irrel
four_concat_congr
four_concat_congr_cast_irrel
four_concat_map
```

The current result suggests the following bridge strategy:

```text
DkPath trace layer:
  stores or exposes the parameterized trace

DkPath endpoint layer:
  records source and target labels

DkPath seam layer:
  keeps seam witnesses proof-irrelevant at the public API

Mathlib bridge:
  converts DkPath packages to Mathlib Path when topology is needed
```

This should reduce later path proofs to named normalization theorems instead
of repeated dependent-object bookkeeping.

## Next implementation inference

The path-packaging comparison for the current shifted cyclic quotient is now
closed. The next step should not add Euclidean readings yet.

Good next candidates:

```text
1. extract a small reusable DkPath design note or prototype namespace;
2. expose a compact theorem collecting the final path equivalence and q2
   boundary preservation;
3. move toward the intrinsic continuous phase parameter only after the
   path-package API is stable.
```

The main mathematical result of this checkpoint is that the quotient seam
gluing and the semantic fixed-boundary observation commute as paths, before
any circle or angle vocabulary is introduced.

## Verification

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
```

passed.
