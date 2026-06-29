# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by proving the compatibility between descended semantic evaluation and path packaging. The endpoint mismatch is already solved. The remaining obstruction is that semantic evaluation must commute with the nested `Path.trans` and `Path.cast` structure used by `shiftedFourPathConcatWithSeams`.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path-packaging compatibility, not Euclidean interpretation.

Context:
The endpoint-casted observed path is stable:

```lean id="gyxg0t"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2
```

The old quotient and finite paths already match their canonical via-edge versions:

```lean id="l9qk8u"
shiftedCyclicFourPath_eq_viaEdges
shiftedSemanticFinFourLevelPath_eq_viaEdges
```

The canonical observed/direct comparison is already available:

```lean id="hdi7yp"
shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
```

The next target is the bridge:

```lean id="mti79u"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
  =
shiftedSemanticObservedCyclicFourPathViaEdges
```

Part A:
Inspect whether Mathlib already has `Path.map` or equivalent path mapping helpers.

Use temporary exploration only if helpful:

```lean id="zkqjwm"
#check Path.map
#check Path.trans
#check Path.cast
#print Path.trans
#print Path.cast
```

Do not keep exploratory commands in the final file unless project style allows it.

Part B:
If `Path.map` exists, use it. If not, define a local helper.

Candidate helper:

```lean id="c3o0a5"
def shiftedPathMap
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f)
    {a b : α} (p : Path a b) :
    Path (f a) (f b) where
  toFun t := f (p t)
  continuous_toFun := hf.comp p.continuous_toFun
  source' := by
    rw [p.source]
  target' := by
    rw [p.target]
```

Only add this if no suitable Mathlib helper exists.

Part C:
Prove map compatibility with `Path.cast`, or specialize it to the semantic evaluation.

Generic candidate:

```lean id="qn30og"
theorem shiftedPathMap_cast
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f)
    {a b c d : α}
    (p : Path a b)
    (hac : c = a) (hbd : d = b) :
    shiftedPathMap f hf (p.cast hac hbd) =
      (shiftedPathMap f hf p).cast
        (by rw [hac])
        (by rw [hbd])
```

If the generic version is noisy, use a specialized theorem for `shiftedSemanticCyclicChartEval`.

Part D:
Prove map compatibility with `Path.trans`.

Generic candidate:

```lean id="lkxq7g"
theorem shiftedPathMap_trans
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f)
    {a b c : α}
    (p : Path a b) (q : Path b c) :
    shiftedPathMap f hf (p.trans q) =
      (shiftedPathMap f hf p).trans (shiftedPathMap f hf q)
```

This may fail definitionally depending on `Path.trans`. If it is noisy, try a pointwise theorem:

```lean id="x4p3jl"
theorem shiftedPathMap_trans_apply
    ...
```

or skip the generic theorem and specialize to the current four-path.

Part E:
Try a specialized four-concat compatibility theorem.

Candidate target:

```lean id="h5puu2"
theorem shiftedSemanticCyclicChartEval_fourConcatWithSeams
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
      shiftedSemanticObservedCyclicFourPathViaEdges hcore z
```

Expected route:
Use `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply`.
Use `shiftedCyclicFourPath_eq_viaEdges`.
Use the map-cast and map-trans compatibility lemmas, or unfold the four-path concatenator if the specialized proof is easier.

Part F:
If Part E succeeds, prove the final casted comparison.

```lean id="jhcos4"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
      shiftedSemanticFinFourLevelPath hcore z := by
  calc
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
        shiftedSemanticObservedCyclicFourPathViaEdges hcore z :=
          shiftedSemanticCyclicChartEval_fourConcatWithSeams hcore z
    _ = shiftedSemanticFinFourLevelPathViaEdges hcore z :=
          shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges hcore z
    _ = shiftedSemanticFinFourLevelPath hcore z := by
          symm
          exact shiftedSemanticFinFourLevelPath_eq_viaEdges hcore z
```

Part G:
One-step-ahead experiment:
If the casted final comparison succeeds, add a value-level final theorem:

```lean id="lig9wm"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t).1 =
      (shiftedSemanticFinFourLevelPath hcore z t).1 :=
  congrArg Subtype.val
    (congrFun
      (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath hcore z)
      t)
```

Part H:
If generic map compatibility is too noisy, do not force it. Add a precise TODO:

```text id="ri1x8q"
The endpoint mismatch is solved. The remaining obstruction is compatibility of
descended semantic evaluation with the nested `Path.trans` and `Path.cast`
structure of `shiftedFourPathConcatWithSeams`.
```

Part I:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="lc631y"
implemented:
  path-map helper if needed
  map-cast compatibility if successful
  map-trans compatibility if successful
  semantic evaluation four-concat compatibility if successful

implemented if successful:
  casted observed path equals finite four-level path
  value-level final theorem

remaining:
  exact map-trans/cast compatibility obstruction if not finished
  Euclidean one-eighth reading later
```

Required checks:

```text id="pemvg5"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
