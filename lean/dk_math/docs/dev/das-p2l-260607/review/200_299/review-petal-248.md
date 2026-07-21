# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: d69e7f3b4d8fcee65fb382a1f18f6460079bb451

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:465) に、list-level の `AdjacentOverlapState` から concrete pair-level obstruction を取り出す補題を追加しました。続けて [同ファイル](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:483) に、`FailureResolutionState` を「oriented neighbor diagnostic」または「pair overlap obstruction」へ分岐する refined theorem も追加しています。

レポートは [report-petal-248.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-248.md:1) に作成しました。

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

現在の差分は `PressureState.lean` の変更と `report-petal-248.md` の新規追加です。

## Review

## 判定

採用。
`OverlapState` が具体 pair obstruction まで落ちた。

追加：

```lean id="p3o8t2"
theorem sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
```

```lean id="mri786"
theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
```

これで `FailureResolutionState` の出口がかなり鋭くなった。

## 増えた事実

これまで：

```text id="hvqkk0"
FailureResolution
  -> OrientedNeighborDiagnostic
   ∨ AdjacentOverlapState
```

今回：

```text id="ir6tvk"
FailureResolution
  -> OrientedNeighborDiagnostic
   ∨ PairOverlapObstruction
```

つまり list-level overlap ではなく、実際の隣接 pair `A B` が取れる。

```lean id="x8v7vg"
∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

これは使いやすい。
状態表では、

```text id="gol1y8"
R -> D ∨ PO
```

まで来た。

## 現在の状態認識

接続済み：

```text id="im56dg"
SortedFailure
  -> FailureResolution
  -> BeamSeed

BeamSeed
  -> CenteredPulseBox

NeighborCandidate
  -> endpoint membership
  -> W' centered diagnostic

RecoveredAdjacent
  -> OrientedNeighborDiagnostic

FailureResolution
  -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction
```

かなり盤面が整理された。

## 次に攻める場所

次は `SortedFailure` から一気にこの refined split へ持ち上げる。

狙い：

```lean id="nvv32s"
theorem sourcePressureSortedFailureState_to_orientedNeighborDiagnostic_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureSortedFailureState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

証明は薄い。

```lean id="kr1pec"
sourcePressureSortedFailureState_to_failureResolutionState h
|> sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
```

これが通れば、入口 `SortedFailure` から状態機械の refined exit まで一本で読める。

## 次の Codex 指示

```text id="ii8jh4"
Goal:
  Lift the refined failure-resolution split to SortedFailureState.

Add in PressureState.lean:

  theorem sourcePressureSortedFailureState_to_orientedNeighborDiagnostic_or_pairOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureSortedFailureState L) :
      (∃ W W',
        SourcePressureOrientedNeighborDiagnosticState L W W') ∨
        ∃ A B,
          SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
            SourcePressureLocalIslandWitnessPairOverlapObstruction A B

Use:
  sourcePressureSortedFailureState_to_failureResolutionState
  sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の次

その後は `BeamSeed` からも同じ refined split を出す。

```lean id="qn65qb"
sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap
```

これで入口が複数になる。

```text id="vxb3f2"
SortedFailure -> D ∨ PO
FailureResolution -> D ∨ PO
BeamSeed -> D ∨ PO
```

状態表が一気に実用になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 4d89c77e..d254ec6c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -453,4 +453,48 @@ theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_ov
         hrec)
   · exact Or.inr hoverlap

+/--
+Adjacent-overlap state exposes a concrete adjacent pair carrying the pair-level
+overlap obstruction.
+
+This refines the mnemonic overlap state from list-level obstruction to the
+addressed pair that witnesses it.  It still does not repair the overlap or
+select a canonical obstructing pair; the pair is merely the existential pair
+provided by the existing obstruction theorem.
+-/
+theorem sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureAdjacentOverlapState L) :
+    ∃ A B,
+      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+        SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction h
+
+/--
+Failure resolution splits into either an oriented neighbor diagnostic or a
+concrete adjacent pair-level overlap obstruction.
+
+This is the pair-refined version of
+`sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState`.
+The recovered branch reaches the Beam-facing oriented diagnostic state; the
+overlap branch now exposes the addressed obstructing adjacent pair.
+-/
+theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases
+    sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
+      h with hdiag | hoverlap
+  · exact Or.inl hdiag
+  · exact Or.inr
+      (sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
+        hoverlap)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-248.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-248.md
new file mode 100644
index 00000000..cc540aca
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-248.md
@@ -0,0 +1,104 @@
+# Report: petal-248
+
+## Goal
+
+Refine `SourcePressureAdjacentOverlapState` from a list-level overlap state into a concrete
+pair-level overlap obstruction.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
+```
+
+This theorem turns
+
+```lean
+SourcePressureAdjacentOverlapState L
+```
+
+into an addressed adjacent pair:
+
+```lean
+∃ A B,
+  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+    SourcePressureLocalIslandWitnessPairOverlapObstruction A B
+```
+
+It is a thin state-level wrapper over the existing pair extraction theorem:
+
+```lean
+exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
+```
+
+Also added:
+
+```lean
+theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
+```
+
+This refines the previous failure-resolution split from
+
+```text
+oriented diagnostic OR list-level overlap state
+```
+
+to
+
+```text
+oriented diagnostic OR concrete adjacent pair-level overlap obstruction
+```
+
+## Automaton Reading
+
+The pressure-state automaton now has a sharper failure-resolution exit:
+
+```text
+FailureResolutionState L
+  -> OrientedNeighborDiagnosticState L W W'
+   OR
+     AdjacentPairInList L A B
+     + PairOverlapObstruction A B
+```
+
+So the mnemonic transition is:
+
+```text
+R -> D ∨ PO
+```
+
+where:
+
+- `R` is failure resolution,
+- `D` is an oriented neighbor diagnostic,
+- `PO` is a pair-level overlap obstruction.
+
+This is useful because callers no longer have to stay at the coarse list-overlap
+surface when the next argument needs the actual adjacent pair.
+
+## Guardrails
+
+This checkpoint deliberately does not prove any of the following:
+
+- overlap repair,
+- canonical obstructing-pair selection,
+- global coverage,
+- aggregation over all adjacent pairs,
+- transport or propagation of diagnostics,
+- convergence or Collatz termination.
+
+The theorem only exposes the concrete pair that already exists behind the
+list-level overlap obstruction.
+
+## Verification
+
+Passed before this report was written:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
````
`````
