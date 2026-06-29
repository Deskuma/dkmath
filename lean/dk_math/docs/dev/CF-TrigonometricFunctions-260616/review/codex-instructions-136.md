# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
DkMath.Analysis docs

Goal:
Stabilize checkpoint 135 and prepare the next path-normalization design step. The shifted cyclic path-packaging comparison is now closed. Do not reopen the completed theorem chain unless a downstream proof reveals a concrete need.

Conclusion:
The endpoint-cast observed quotient closed path is equal to the existing fixed-q2 finite four-level path. The public alias is:

```lean id="g3dcp5"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_final
```

This names the closed checkpoint for downstream imports.

Task A:
Treat the following tag as implemented and closed:

```text id="am3yrt"
semantic-cf2d/shifted-cyclic-path-eval
```

Make sure documentation says the comparison is closed before any Euclidean reading.

Task B:
Preserve the theorem chain.

Key public theorems:

```lean id="a69s2x"
shiftedFourPathConcatWithSeams_map
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_final
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
```

Do not rename these unless there is a strong downstream naming conflict.

Task C:
Keep the result pre-geometric.

Do not introduce theorem names involving:

```text id="mv2ez3"
circle
angle
arc
degree
rotation
piOverFour
fortyFive
oneEighth
```

in `SemanticCF2DPhaseShift.lean`.

Task D:
Use the DkPath design note as the next map.

The validated minimum API candidates are:

```text id="l40y2u"
cast_apply
map_cast
map_trans
cast_proof_irrel
four_concat_congr
four_concat_congr_cast_irrel
four_concat_map
```

Current corresponding theorem names:

```lean id="qotxdx"
shiftedPath_cast_apply
shiftedPath_map_cast
shiftedPath_map_trans
shiftedPath_cast_proof_irrel
shiftedFourPathConcatWithSeams_congr
shiftedFourPathConcatWithSeams_congr_cast_irrel
shiftedFourPathConcatWithSeams_map
```

Task E:
One-step-ahead inference:
A future DkPath layer should separate:

```text id="cjrhjs"
trace:
  parameterized values over unitInterval

endpoint labels:
  source and target names needed by dependent path types

seam witnesses:
  proof terms used for typed concatenation
```

Public API should treat seam witnesses as proof-irrelevant whenever the trace and endpoint labels are unchanged.

Task F:
One-step-ahead experiment:
Create only a tiny isolated prototype if useful.

Suggested namespace:

```lean id="fex1hh"
namespace DkPathPrototype
```

Suggested object:

```text id="dbm28l"
FourPathPackage
```

Suggested fields:

```text id="p7wmwj"
four component paths
four seam witnesses
```

Suggested functions:

```text id="r9j6i8"
toPath
map
```

Suggested theorem:

```text id="o3c4zh"
toPath_map
```

Do not connect the prototype to production code yet. It should graduate only if it shortens a real downstream semantic path proof without changing public theorem meanings.

Task G:
Do not start the Euclidean one-eighth reading from this checkpoint.

The next stable work is path-package design extraction. Euclidean interpretation should come only after the path-normalization API is stable enough that later proofs do not reopen the same Mathlib `Path.cast` bookkeeping.

Task H:
Optional compact downstream theorem:
If downstream modules repeatedly need both final path equality and value-level equality, add a small public section collecting:

```lean id="cp6uo9"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_final
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2
```

Do not create a heavy bundled structure unless a concrete downstream need appears.

Task I:
Required checks after any code or doc change:

```text id="jglxwc"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
