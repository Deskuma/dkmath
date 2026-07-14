# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by resolving seam proof alignment after mapping. The map/trans/cast compatibility pieces are now available. The next target is to prove that descended semantic evaluation sends the quotient seam equalities to the finite fixed-boundary seam equalities used by `shiftedFourPathConcatWithSeams`.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is seam alignment for path packaging, not Euclidean interpretation.

Context:
The following map/path compatibility helpers are implemented:

```lean id="c4e9tz"
shiftedPath_map_cast
shiftedPath_map_trans
```

The endpoint-casted observed path is stable:

```lean id="fku3i4"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2
```

The canonical via-edge comparison is already available:

```lean id="jj7lxx"
shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
```

The remaining bridge is blocked by seam proof alignment after mapping.

Part A:
Add theorem wrappers showing that quotient endpoint evaluation agrees with finite endpoint APIs.

These may already exist in some form. If so, create only aliases with names suitable for the current comparison.

Candidate names:

```lean id="gfajz7"
theorem shiftedSemanticCyclicChartEval_right_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticCyclicChartEval hcore z
      (shiftedCyclicChartRight (0 : Fin 4)) =
        shiftedSemanticFinRightLevelEndpoint hcore z (0 : Fin 4)

theorem shiftedSemanticCyclicChartEval_left_one
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticCyclicChartEval hcore z
      (shiftedCyclicChartLeft (1 : Fin 4)) =
        shiftedSemanticFinLeftLevelEndpoint hcore z (1 : Fin 4)
```

Repeat for `1→2`, `2→3`, and `3→0` only if concrete seam alignment needs them.

Part B:
Prove mapped quotient seam equality aligns with finite seam equality.

Candidate theorem shape for the first seam:

```lean id="gkkwsk"
theorem shiftedSemanticCyclicChartEval_seam_zero_eq_fin_seam
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    congrArg (fun p =>
      shiftedSemanticCyclicChartEval hcore z p)
      shiftedCyclicChartRight_zero_eq_one_left =
        shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z
```

This exact proof equality may be too strict because proof irrelevance or generated proof terms may not match definitionally. If it is noisy, use a value-level seam theorem instead:

```lean id="se9l6i"
theorem shiftedSemanticCyclicChartEval_seam_zero_value
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticFinRightLevelEndpoint hcore z (0 : Fin 4) =
      shiftedSemanticFinLeftLevelEndpoint hcore z (1 : Fin 4)
```

If the value-level theorem is already available, expose it as the seam alignment alias needed for the concat proof.

Part C:
Prefer value-level seam alignment over proof-term equality.

Reason:
`Path.cast` depends on equality proofs, but in Lean equality proofs in propositions are usually proof-irrelevant. Direct proof-term equality may be unnecessary and noisy. It may be easier to use `Subsingleton.elim` or rely on proof irrelevance when casts differ only by proof terms.

Try this helper if needed:

```lean id="txe2gd"
theorem shiftedPath_cast_proof_irrel
    {α : Type _} [TopologicalSpace α]
    {a b c d : α}
    (p : Path a b)
    (h₁ h₂ : c = a)
    (k₁ k₂ : d = b) :
    p.cast h₁ k₁ = p.cast h₂ k₂ := by
  cases h₁
  cases k₁
  simp
```

If this fails due to proof dependencies, try `apply Path.ext; funext t; rfl`.

Part D:
Use the seam alignment and map compatibility helpers to prove the four-concat compatibility theorem.

Candidate theorem:

```lean id="lcibqo"
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
Use `shiftedPath_map_trans` and `shiftedPath_map_cast`.
Use seam alignment aliases or proof-irrelevance for casts.

Part E:
If Part D succeeds, prove the final casted comparison.

```lean id="vunadn"
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

Part F:
One-step-ahead experiment:
If the final casted path comparison succeeds, add a value-level final theorem.

```lean id="duqd6h"
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

Part G:
If proof-term seam alignment is too hard, do not force it. Add a precise TODO:

```text id="edyqgm"
The map/trans/cast compatibility lemmas are available. The remaining obstruction
is proof alignment between mapped quotient seam equalities and the finite seam
equalities used by the canonical via-edge concatenator.
```

Part H:
Do not add Euclidean reading yet.

Part I:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="f4r3ky"
implemented:
  seam endpoint evaluation aliases
  mapped-seam value alignment
  cast proof-irrelevance helper if needed

implemented if successful:
  semantic evaluation four-concat compatibility
  casted observed path equals finite four-level path
  value-level final comparison

remaining:
  proof-term seam alignment if not finished
  Euclidean one-eighth reading later
```

Required checks:

```text id="g58tsr"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
