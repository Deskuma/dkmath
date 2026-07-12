# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 045681f484f2cbfdbb82972ac98254f5a5e3c96f

## Report

FailureResolutionState の分岐を oriented diagnostic か overlap state に接続しました。

更新: [PressureState.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean)

追加 theorem:

```lean
theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      SourcePressureAdjacentOverlapState L
```

証明は指定通り、`sourcePressureFailureResolutionState_cases` で recovered / overlap に分けて、recovered 側は前回追加した `sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState` に流しています。

レポート: [report-petal-247.md](/home/deskuma/develop/lean/dkmath/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-247.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

これで状態遷移はかなり読みやすくなりました。

```text
FailureResolution
  -> OrientedNeighborDiagnostic
   ∨ AdjacentOverlap
```

overlap はまだ obstruction として残し、repair/coverage/transport/convergence は主張していません。

## Review

## 判定

採用。
`FailureResolutionState` が状態表の次段へ落ちた。

追加 theorem：

```lean
theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      SourcePressureAdjacentOverlapState L
```

これで状態遷移は、

```text
FailureResolution
  -> OrientedNeighborDiagnostic
   ∨ AdjacentOverlap
```

になった。

## 増えた事実

`RecoveredAdjacent` 側は、前回の theorem で `OrientedNeighborDiagnostic` へ接続済み。
今回、それを `FailureResolution` 全体の分岐に持ち上げた。

流れはこう。

```text
FailureResolutionState
  -> RecoveredAdjacentState ∨ AdjacentOverlapState

RecoveredAdjacentState
  -> ∃ W W', OrientedNeighborDiagnosticState L W W'

Therefore:
FailureResolutionState
  -> (∃ W W', OrientedNeighborDiagnosticState L W W') ∨ AdjacentOverlapState L
```

状態表としてかなり読みやすい。

## 現在の状態表

```text
SortedFailure
  -> FailureResolution

FailureResolution
  -> OrientedNeighborDiagnostic
   ∨ AdjacentOverlap

RecoveredAdjacent
  -> OrientedNeighborDiagnostic
```

ここまでで、recovered 側は Beam-facing diagnostic まで到達。
残っているのは overlap 側の具体化。

## 次に攻める定理

次は `AdjacentOverlapState` を pair-level obstruction に落とす。

既存で使えそうな theorem：

```lean
exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
```

狙い：

```lean
theorem sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureAdjacentOverlapState L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

これが通れば、次に強化版：

```lean
theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

が狙える。

## Codex 指示

```text
Goal:
  Refine AdjacentOverlapState from list-level overlap to concrete pair-level
  overlap obstruction.

Add in PressureState.lean:

  theorem sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureAdjacentOverlapState L) :
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B

Use:
  exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction

Then add, if one-line:

  theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureFailureResolutionState L) :
      (∃ W W',
        SourcePressureOrientedNeighborDiagnosticState L W W') ∨
        ∃ A B,
          SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
            SourcePressureLocalIslandWitnessPairOverlapObstruction A B

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の一手

`R -> D ∨ O` はできた。
次は `O` を具体ペアへ落とす。

```text
FailureResolution
  -> OrientedNeighborDiagnostic
   ∨ PairOverlapObstruction
```

ここまで通れば、状態表の分岐はかなり実体を持つ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 07bb129e..4d89c77e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -422,4 +422,35 @@ theorem sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosti
     ⟨A, B,
       sourcePressureOrientedNeighborDiagnosticState_of_forward hin hdiag⟩
 
+/--
+Failure resolution splits into either an oriented neighbor diagnostic or an
+adjacent-overlap state.
+
+This is the mnemonic automaton branch after the recovered branch has been
+upgraded to oriented local diagnostics:
+
+```text
+FailureResolution
+  -> OrientedNeighborDiagnostic
+   ∨ AdjacentOverlap
+```
+
+The recovered side uses
+`sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState`.
+The overlap side is kept as the explicit obstruction state.  No overlap repair,
+coverage, aggregation, transport, or convergence is claimed.
+-/
+theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
+      SourcePressureAdjacentOverlapState L := by
+  rcases sourcePressureFailureResolutionState_cases h with hrec | hoverlap
+  · exact Or.inl
+      (sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
+        hrec)
+  · exact Or.inr hoverlap
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-247.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-247.md
new file mode 100644
index 00000000..1a5427b7
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-247.md
@@ -0,0 +1,115 @@
+# Report: petal-247
+
+## Goal
+
+Connect:
+
+```text
+SourcePressureFailureResolutionState
+  -> exists SourcePressureOrientedNeighborDiagnosticState
+   ∨ SourcePressureAdjacentOverlapState
+```
+
+## Result
+
+Implemented successfully.
+
+Updated file:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+```
+
+Added theorem:
+
+```lean
+theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
+      SourcePressureAdjacentOverlapState L
+```
+
+## Proof Chain
+
+Used:
+
+```lean
+sourcePressureFailureResolutionState_cases
+sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
+```
+
+The split is:
+
+```text
+FailureResolutionState
+  -> RecoveredAdjacentState
+   ∨ AdjacentOverlapState
+```
+
+Recovered branch:
+
+```text
+RecoveredAdjacentState
+  -> exists OrientedNeighborDiagnosticState
+```
+
+Overlap branch:
+
+```text
+AdjacentOverlapState
+```
+
+## Automaton Reading
+
+The mnemonic transition is now:
+
+```text
+R
+  -> D
+   ∨ O
+```
+
+where:
+
+```text
+R = failure resolution
+D = oriented neighbor diagnostic
+O = adjacent overlap obstruction
+```
+
+This is a useful checkpoint because the recovered branch no longer stops at
+pair-local recovered accounting; it now reaches the Beam-facing oriented
+diagnostic state.
+
+## Guardrails
+
+No theorem added:
+
+- overlap repair;
+- canonical pair selection;
+- list-wide coverage;
+- aggregation;
+- transport;
+- propagation;
+- Collatz convergence.
+
+The overlap branch remains an explicit obstruction state.
+
+## Verification
+
+Commands run from:
+
+```text
+lean/dk_math
+```
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
````
`````
