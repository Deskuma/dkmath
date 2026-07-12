# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 954a280713e2afe9f2e664264b1bd95b33612145

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:516) に `sourcePressureSortedFailureState_to_orientedNeighborDiagnostic_or_pairOverlap` を追加しました。`SortedFailureState -> FailureResolutionState -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction` の合成を、そのまま公開面の薄い theorem として固定しています。

レポートは [report-petal-249.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-249.md:1) に追加しました。

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

差分は `PressureState.lean` の変更と `report-petal-249.md` の新規追加です。

## Review

## 判定

採用。
`SortedFailureState` から refined exit まで直通になった。

追加：

```lean
theorem sourcePressureSortedFailureState_to_orientedNeighborDiagnostic_or_pairOverlap
```

内容はこれ。

```text
SortedFailureState L
  -> OrientedNeighborDiagnosticState L W W'
   ∨ PairOverlapObstruction A B
```

中身は指定通り、

```lean
sourcePressureSortedFailureState_to_failureResolutionState
sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
```

の合成。状態表の入口から出口までが一本化された。

## 増えた事実

状態遷移はこう読める。

```text
SortedFailure
  -> FailureResolution
  -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction
```

つまり、

```text
S -> R -> D ∨ PO
```

が public theorem として固定された。

これはかなり使いやすい。caller はもう `FailureResolutionState` を手で経由しなくてよい。

## 現在の状態表

```text
SortedFailure
  -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction

FailureResolution
  -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction

RecoveredAdjacent
  -> OrientedNeighborDiagnostic

AdjacentOverlap
  -> PairOverlapObstruction
```

状態機械の主要出口が揃った。

## 次に攻める定理

次は `BeamSeedState` からも同じ refined exit を出す。

`BeamSeedState` と `FailureResolutionState` は既に相互に読めるので、薄く通るはず。

```lean
theorem sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureBeamSeedState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

## Codex 指示

```text
Goal:
  Lift the refined diagnostic/obstruction split to BeamSeedState.

Add in PressureState.lean:

  theorem sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureBeamSeedState L) :
      (∃ W W',
        SourcePressureOrientedNeighborDiagnosticState L W W') ∨
        ∃ A B,
          SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
            SourcePressureLocalIslandWitnessPairOverlapObstruction A B

Use:
  sourcePressureBeamSeedState_to_failureResolutionState
  sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

次で、

```text
SortedFailure -> D ∨ PO
FailureResolution -> D ∨ PO
BeamSeed -> D ∨ PO
```

が揃う。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index d254ec6c..c2b3b4de 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -497,4 +497,32 @@ theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pa
       (sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
         hoverlap)
 
+/--
+Sorted failure reaches the same refined diagnostic/obstruction split.
+
+This theorem composes the sorted-failure entry point with the existing
+failure-resolution transition, then exposes the pair-refined exit:
+
+```text
+SortedFailure
+  -> OrientedNeighborDiagnostic
+   ∨ PairOverlapObstruction
+```
+
+It is intentionally only a lift through the state automaton.  It does not add
+repair, canonical selection, global coverage, or propagation beyond the
+adjacent pair supplied by the obstruction branch.
+-/
+theorem sourcePressureSortedFailureState_to_orientedNeighborDiagnostic_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureSortedFailureState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
+    (sourcePressureSortedFailureState_to_failureResolutionState h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-249.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-249.md
new file mode 100644
index 00000000..b43fed40
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-249.md
@@ -0,0 +1,70 @@
+# Report: petal-249
+
+## Goal
+
+Lift the refined failure-resolution split to `SourcePressureSortedFailureState`.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem sourcePressureSortedFailureState_to_orientedNeighborDiagnostic_or_pairOverlap
+```
+
+This theorem composes:
+
+```lean
+sourcePressureSortedFailureState_to_failureResolutionState
+sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
+```
+
+and exposes the sorted-failure entry point directly as:
+
+```text
+SortedFailureState L
+  -> OrientedNeighborDiagnosticState L W W'
+   OR
+     AdjacentPairInList L A B
+     + PairOverlapObstruction A B
+```
+
+## Automaton Reading
+
+The state chain now has a sharper public exit from sorted failure:
+
+```text
+S -> R -> D ∨ PO
+```
+
+where:
+
+- `S` is sorted failure,
+- `R` is failure resolution,
+- `D` is an oriented neighbor diagnostic,
+- `PO` is a concrete pair-level overlap obstruction.
+
+This gives callers a direct theorem from the sorted-failure surface without
+manually stepping through the intermediate resolution state.
+
+## Guardrails
+
+This is only a state-lift theorem.  It does not add:
+
+- overlap repair,
+- canonical obstructing-pair selection,
+- global coverage,
+- aggregation over all adjacent pairs,
+- transport or propagation,
+- convergence or Collatz termination.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
````
`````
