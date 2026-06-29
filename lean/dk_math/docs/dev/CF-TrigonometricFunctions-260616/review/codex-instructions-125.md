# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by advancing the comparison between `shiftedSemanticObservedCyclicFourPath` and `shiftedSemanticFinFourLevelPath`. Do not force the full path equality unless the `Path.trans` parameterization unfolds cleanly. The immediate goal is to identify and prove small `Path.trans` normalization facts or first-segment comparison facts.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path-packaging normalization between quotient traversal and fixed-boundary observation.

Context:
The following comparison-preparation facts are implemented:

```lean id="bfvv9c"
shiftedPath_cast_apply
shiftedSemanticCyclicChartEval_edgePath_zero
shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
```

The intended full comparison remains:

```lean id="anc64i"
shiftedSemanticObservedCyclicFourPath hcore z =
  shiftedSemanticFinFourLevelPath hcore z
```

This is still expected to require `Path.trans` and `Path.cast` normalization.

Part A:
Inspect existing Mathlib API for `Path.trans` pointwise evaluation.

Use local commands during exploration if helpful:

```lean id="if3mr8"
#check Path.trans
#check Path.cast
#print Path.trans
#print Path.cast
```

Look for existing simp theorems or equations that describe `(p.trans q) t`.

Do not keep exploratory `#check` or `#print` commands in the final file unless project style allows it.

Part B:
If Mathlib exposes a convenient theorem for `Path.trans`, add a small local wrapper with project-specific naming.

Candidate theorem direction:

```lean id="p35csa"
theorem shiftedPath_trans_apply_source
    {α : Type _} [TopologicalSpace α]
    {a b c : α}
    (p : Path a b) (q : Path b c) :
    (p.trans q) 0 = p 0
```

and:

```lean id="mvhk6s"
theorem shiftedPath_trans_apply_target
    {α : Type _} [TopologicalSpace α]
    {a b c : α}
    (p : Path a b) (q : Path b c) :
    (p.trans q) 1 = q 1
```

If these are already available from `.source` and `.target`, add only if they help downstream readability.

Part C:
Try to prove a first-segment comparison for the closed quotient path only if the `Path.trans` parameterization is manageable.

Start with a very modest theorem, not the full equality.

Candidate theorem direction:

```lean id="rbt8dd"
theorem shiftedSemanticObservedCyclicFourPath_first_endpoint
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z 0 =
      shiftedSemanticFinLevelEdge hcore z (0 : Fin 4) 0
```

This may already follow from source comparison and finite four-level source. If it is redundant, skip it.

Part D:
Try a value-level comparison before full path equality.

Candidate theorem:

```lean id="m3tt9x"
theorem shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_source
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    (shiftedSemanticObservedCyclicFourPath hcore z 0).1 =
      (shiftedSemanticFinFourLevelPath hcore z 0).1
```

and the analogous target theorem. These may be immediate from the already implemented source/target comparisons. Add them only if they help later rewriting.

Part E:
賢狼のおまけ challenge:
Try an edge-local observed path, avoiding the fourfold `Path.trans`.

Define a path by evaluating a single quotient edge path:

```lean id="iz19rn"
def shiftedSemanticObservedCyclicEdgePath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    Path
      (shiftedSemanticFinLeftLevelEndpoint hcore z i)
      (shiftedSemanticFinRightLevelEndpoint hcore z i) := by
  ...
```

Expected route:
Use `shiftedCyclicChartEdgePath i`, compose with `shiftedSemanticCyclicChartEval`, then cast endpoints using
`shiftedSemanticCyclicChartEval_left` and
`shiftedSemanticCyclicChartEval_right`.

Then prove:

```lean id="nhjmk4"
theorem shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticObservedCyclicEdgePath hcore z i =
      shiftedSemanticFinLevelPath hcore z i
```

This may be much easier than the fourfold comparison and would be very valuable. If full equality is noisy, try value-level equality first:

```lean id="ejs2xb"
theorem shiftedSemanticObservedCyclicEdgePath_val
    ...
```

Part F:
If Part E succeeds, it becomes the preferred bridge:
single-edge observed quotient path equals direct finite level path.
Then the full four-path comparison can later be assembled from four edge-level path equalities and trans/cast normalization.

Part G:
If `Path.trans` remains noisy, keep the full comparison TODO and update docs with the precise obstacle:

```text id="z6kjex"
The remaining obstruction is not semantic. Each edge comparison is available.
The remaining task is normalizing the nested `Path.trans` and endpoint `Path.cast`
structure used by the two closed four-path packages.
```

Part H:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="xqze7b"
implemented:
  Path.trans endpoint helper if added
  value-level endpoint comparison if added
  observed single-edge path if added
  single-edge observed/direct comparison if successful

remaining:
  nested four-path trans/cast normalization
  full observed four-path equality
  Euclidean one-eighth reading later
```

Required checks:

```text id="l55iun"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
