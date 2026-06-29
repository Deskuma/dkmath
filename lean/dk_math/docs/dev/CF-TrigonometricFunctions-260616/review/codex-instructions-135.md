# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Stabilize the completed path-packaging comparison and prepare the next design step. The global map-through-gluing theorem is now implemented, and the endpoint-cast observed quotient path is equal to the existing finite four-level path. The next task is not to add Euclidean interpretation yet, but to expose the result cleanly and extract reusable path-normalization guidance for a future DkPath layer.

Principle:
Keep this layer pre-geometric. Do not introduce circle, angle, arc, degree, rotation, piOverFour, fortyFive, or Euclidean one-eighth terminology in theorem names in this file. Treat the current result as path packaging and semantic observation, not geometry.

Current implemented API:

```lean id="kfmzlh"
shiftedFourPathConcatWithSeams_map
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
```

Task A:
Add a compact final theorem if useful for downstream imports.

Candidate name:

```lean id="kq8t9z"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_final
```

Suggested meaning:
It should either alias `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath`, or package the final path equality together with the value-level theorem in a simple public-facing location.

Do not over-engineer this. If an alias adds no value, skip it and only update documentation.

Task B:
Add or update documentation to say that `semantic-cf2d/shifted-cyclic-path-eval` is closed.

The documentation should say:

```text id="dvhfgl"
The quotient-side closed path, after endpoint casting, is equal to the existing
fixed-q2 finite four-level path. The comparison is purely path-packaging:
Path.map, Path.trans, Path.cast, and seam proof irrelevance.
```

Task C:
Start a DkPath design note, but do not implement a full DkPath layer yet unless it is very small and isolated.

Good location candidates:

```text id="vg8264"
DkMath/Analysis/docs/design-dkpath-layer.md
```

or a short section inside the existing phase-shift design doc.

The note should record the validated minimum API:

```text id="x0o0zv"
cast_apply
map_cast
map_trans
cast_proof_irrel
four_concat_congr
four_concat_congr_cast_irrel
four_concat_map
```

Task D:
One-step-ahead inference:
The future DkPath layer should separate three layers.

```text id="v3ol6t"
trace:
  the parameterized value over unitInterval

endpoint labels:
  source and target labels used for dependent typing

seam witnesses:
  proof terms used to type concatenation
```

Public theorem design:

```text id="nwejdk"
Seam witnesses should be proof-irrelevant at the public API level.
Path normalization theorems should be named and reusable.
Mathlib Path should remain the external topology bridge.
```

Task E:
One-step-ahead experiment:
Create a tiny prototype only if it stays isolated.

Possible namespace:

```lean id="yvxbgo"
namespace DkPathPrototype
```

Possible structure:

```lean id="ob4t8t"
structure FourPathPackage where
  -- four component paths
  -- four seam witnesses
```

Possible functions:

```text id="vwk0ve"
toPath
map
```

Possible theorem:

```text id="pbg2si"
toPath_map
```

Do not connect this prototype to production code yet. The purpose is only to test whether future DkPath can hide `Path.cast` and seam proof bookkeeping.

Task F:
Do not add the Euclidean one-eighth reading yet.

The next Euclidean bridge should only begin after the path packaging API is stable and documented.

Task G:
If touching code, preserve theorem placement.

Generic theorem placement:

```text id="ix2bjv"
shiftedFourPathConcatWithSeams_map
```

should stay near the generic four-path concatenator section, not buried in semantic-specific code.

Semantic theorem placement:

```text id="f20boo"
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
```

should remain near the shifted cyclic semantic path comparison section.

Task H:
Update docs.

Required docs:

```text id="tgaz8q"
DkReal.lean
design-phase-center-shift-104.md
```

Optional new docs:

```text id="xkxph9"
design-dkpath-layer.md
codex-report-135.md
```

Task I:
Required checks.

```text id="t38cqe"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
