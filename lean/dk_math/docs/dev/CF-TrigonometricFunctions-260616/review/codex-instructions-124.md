# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by preparing the comparison between `shiftedSemanticObservedCyclicFourPath` and `shiftedSemanticFinFourLevelPath`. Do not force the full path equality if `Path.trans` and `Path.cast` normalization becomes noisy. First add small normalization and endpoint-comparison lemmas.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path-comparison infrastructure between quotient chart traversal and fixed-boundary observation.

Context:
`shiftedSemanticObservedCyclicFourPath` is implemented as the fixed-`q2` boundary observation of `shiftedCyclicFourPath`. The local edge comparison theorem is already available:

```lean id="s9oetq"
shiftedSemanticCyclicChartEval_edgePath
```

The intended but not yet proved full theorem is:

```lean id="objhn8"
shiftedSemanticObservedCyclicFourPath hcore z =
  shiftedSemanticFinFourLevelPath hcore z
```

This may require `Path.trans` and `Path.cast` normalization lemmas.

Part A:
Search for existing Mathlib simp theorems for `Path.cast` and `Path.trans`.

If existing theorems are available, use them. If not, try adding small local lemmas with non-conflicting names.

Candidate cast lemma:

```lean id="eivvpe"
theorem shiftedPath_cast_apply
    {α : Type _} [TopologicalSpace α]
    {a b c d : α}
    (p : Path a b) (hac : a = c) (hbd : b = d)
    (t : unitInterval) :
    (p.cast hac hbd) t = p t := by
  ...
```

If this is already simp or rfl-like, mark only if useful.

Part B:
Add endpoint comparison between the observed quotient path and the finite four-level path.

Candidate theorems:

```lean id="vrv64s"
theorem shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z 0 =
      shiftedSemanticFinFourLevelPath hcore z 0

theorem shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z 1 =
      shiftedSemanticFinFourLevelPath hcore z 1
```

Expected route:
Use source/target aliases and `shiftedSemanticCyclicChartEval_left_zero`.

Part C:
Try a first-edge local comparison only if it is clean.

The challenge is that `shiftedCyclicFourPath` is built by nested `Path.trans`, so the first edge occupies only the first segment of the unit interval. If the `Path.trans` parameterization API is not convenient, do not force this.

Fallback theorem:
Compare the standalone edge path evaluation, which is already known. Add a wrapper specialized to edge `0` if useful:

```lean id="ixpx5n"
theorem shiftedSemanticCyclicChartEval_edgePath_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    shiftedSemanticCyclicChartEval hcore z
      (shiftedCyclicChartEdgePath (0 : Fin 4) t) =
        shiftedSemanticFinLevelEdge hcore z (0 : Fin 4) t
```

Part D:
If endpoint comparisons and cast normalization are clean, try the full equality as an optional challenge:

```lean id="z3vo69"
theorem shiftedSemanticObservedCyclicFourPath_eq_finFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z =
      shiftedSemanticFinFourLevelPath hcore z
```

If this becomes noisy, stop and keep the TODO. Add a comment explaining whether the obstruction is `Path.trans` interval splitting, `Path.cast`, or endpoint type coercion.

Part E:
賢狼のおまけ challenge:
Try proving an evaluated closed path equality only after applying `Subtype.val`, which may be easier than full path equality in the level-set type.

Candidate theorem:

```lean id="khu4qy"
theorem shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    (shiftedSemanticObservedCyclicFourPath hcore z t).1 =
      (shiftedSemanticFinFourLevelPath hcore z t).1
```

This may still be hard, but it avoids some subtype equality friction. If it is not easy, leave it as TODO.

Part F:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="kd5gi5"
implemented:
  endpoint comparison between observed quotient path and finite four-level path
  cast/trans helper lemmas if added
  first-edge wrapper if added

implemented if successful:
  full path equality or value-level equality

remaining:
  full path comparison after Path.trans/cast normalization
  Euclidean one-eighth reading later
```

Required checks:

```text id="lxa13f"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
