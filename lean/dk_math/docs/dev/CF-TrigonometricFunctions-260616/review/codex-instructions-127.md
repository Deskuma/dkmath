# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by comparing the older closed four-path definitions with the new canonical via-edge versions. Do not force the final old-observed equals old-finite theorem until the old-to-canonical comparison lemmas are stable.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path-packaging normalization between older closed path definitions and canonical via-edge four-paths.

Context:
The generic four-edge concatenator is implemented:

```lean id="g2bkr1"
shiftedFourPathConcatWithSeams
shiftedFourPathConcatWithSeams_congr
```

The canonical via-edge comparison is implemented:

```lean id="ivhp6b"
shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
```

The remaining comparison should pass through old-to-canonical bridge theorems.

Part A:
Define a canonical quotient four path via the common concatenator.

Candidate definition:

```lean id="cfdm6c"
def shiftedCyclicFourPathViaEdges :
    Path (shiftedCyclicChartLeft (0 : Fin 4))
      (shiftedCyclicChartLeft (0 : Fin 4)) :=
  shiftedFourPathConcatWithSeams
    (shiftedCyclicChartEdgePath (0 : Fin 4))
    (shiftedCyclicChartEdgePath (1 : Fin 4))
    (shiftedCyclicChartEdgePath (2 : Fin 4))
    (shiftedCyclicChartEdgePath (3 : Fin 4))
    shiftedCyclicChartRight_zero_eq_one_left
    shiftedCyclicChartRight_one_eq_two_left
    shiftedCyclicChartRight_two_eq_three_left
    shiftedCyclicChartRight_three_eq_zero_left
```

Part B:
Compare the existing quotient closed path with the canonical quotient via-edge path.

Candidate theorem:

```lean id="ye21kv"
theorem shiftedCyclicFourPath_eq_viaEdges :
    shiftedCyclicFourPath = shiftedCyclicFourPathViaEdges := by
  rfl
```

If `rfl` fails, unfold both definitions and try `simp [shiftedCyclicFourPathViaEdges, shiftedFourPathConcatWithSeams]`.

If it becomes noisy, keep a TODO explaining the exact difference in `Path.trans` nesting.

Part C:
Compare the existing finite four-level path with the canonical finite via-edge path.

Candidate theorem:

```lean id="rcmgml"
theorem shiftedSemanticFinFourLevelPath_eq_viaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFinFourLevelPath hcore z =
      shiftedSemanticFinFourLevelPathViaEdges hcore z
```

Expected route:
Try `rfl` first. If not, unfold both definitions and use `simp [shiftedSemanticFinFourLevelPathViaEdges, shiftedFourPathConcatWithSeams]`.

Part D:
Compare the observed closed quotient path with the canonical observed via-edge path.

Candidate theorem:

```lean id="zq8v0f"
theorem shiftedSemanticObservedCyclicFourPath_eq_viaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z =
      shiftedSemanticObservedCyclicFourPathViaEdges hcore z
```

Expected route:
Use `Path.ext`.
Use the old quotient path comparison from Part B.
Then reduce to the already implemented single-edge comparison if needed.

If direct path equality is hard, try a value-level theorem first:

```lean id="lhxqyz"
theorem shiftedSemanticObservedCyclicFourPath_val_eq_viaEdges_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    (shiftedSemanticObservedCyclicFourPath hcore z t).1 =
      (shiftedSemanticObservedCyclicFourPathViaEdges hcore z t).1
```

Part E:
If Parts B, C, and D succeed, prove the final old-definition comparison.

Candidate theorem:

```lean id="evhhdl"
theorem shiftedSemanticObservedCyclicFourPath_eq_finFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z =
      shiftedSemanticFinFourLevelPath hcore z := by
  calc
    shiftedSemanticObservedCyclicFourPath hcore z =
        shiftedSemanticObservedCyclicFourPathViaEdges hcore z := ...
    _ = shiftedSemanticFinFourLevelPathViaEdges hcore z :=
        shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges hcore z
    _ = shiftedSemanticFinFourLevelPath hcore z := by
        symm
        exact shiftedSemanticFinFourLevelPath_eq_viaEdges hcore z
```

Do not force this if Part D is noisy.

Part F:
一歩先ゆくおまけ実験:
If final old-definition comparison succeeds, add a value-level theorem as a convenient rewriting form.

Candidate theorem:

```lean id="lgcai4"
theorem shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    (shiftedSemanticObservedCyclicFourPath hcore z t).1 =
      (shiftedSemanticFinFourLevelPath hcore z t).1 :=
  congrArg Subtype.val
    (congrFun
      (shiftedSemanticObservedCyclicFourPath_eq_finFourLevelPath hcore z)
      t)
```

If the full path equality does not succeed, try only this value-level theorem through the via-edge comparison.

Part G:
If Part B or C succeeds but Part D fails, update TODO precisely:

```text id="q3gut3"
The quotient-side closed path and finite closed path match their canonical via-edge versions, but the observed quotient path still needs a lemma commuting evaluation with the canonical four-path concatenator.
```

Part H:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="nbx6mi"
implemented:
  quotient four-path via-edge canonical form
  old quotient four-path to canonical comparison
  old finite four-level path to canonical comparison

implemented if successful:
  observed old path to canonical observed comparison
  final observed old path equals finite old path
  value-level final comparison

remaining:
  evaluation-commutes-with-four-path-concat if needed
  Euclidean one-eighth reading later
```

Required checks:

```text id="ff2kz3"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
