# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 5609774dff86c575165cfd0061ef5fb201601fbc

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:723) に `FailureResolutionState` から box 版 split へ進む theorem を追加し、あわせて [SortedFailureState 版](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:748) と [BeamSeedState 版](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:771) も追加しました。

追加 theorem:

```lean
sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
sourcePressureSortedFailureState_to_orientedNeighborBox_or_pairOverlap
sourcePressureBeamSeedState_to_orientedNeighborBox_or_pairOverlap
```

`D` 側だけを `SourcePressureOrientedNeighborBoxState` に強化し、overlap 側は concrete pair-level obstruction のまま保持しています。

レポートは [report-petal-253.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-253.md:1) に追加しました。

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Review

## 判定

採用。
三つの入口がすべて **Box ∨ PairOverlap** へ到達した。

追加：

```lean id="oedxgx"
sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
sourcePressureSortedFailureState_to_orientedNeighborBox_or_pairOverlap
sourcePressureBeamSeedState_to_orientedNeighborBox_or_pairOverlap
```

これで状態出口はこうなった。

```text id="xwy2sd"
R -> Box ∨ PO
S -> Box ∨ PO
B -> Box ∨ PO
```

`D` 側だけを `SourcePressureOrientedNeighborBoxState` に強化し、overlap 側は concrete pair-level obstruction のまま保持している。実装筋は良い。

## 増えた事実

これまで：

```text id="0mcui8"
FailureResolution / SortedFailure / BeamSeed
  -> OrientedNeighborDiagnostic ∨ PairOverlapObstruction
```

今回：

```text id="uyvg90"
FailureResolution / SortedFailure / BeamSeed
  -> OrientedNeighborBox ∨ PairOverlapObstruction
```

つまり diagnostic branch が二点 box まで強化された。

`Box` は、

```text id="oz8c3e"
OrientedNeighborDiagnosticState L W W'
+
CenteredLocalPulseBox W
+
CenteredLocalPulseBox W'
```

なので、左右 endpoint が sign / height / jump を持つ。

## 現在の状態表

```text id="pegqxm"
SortedFailure
  -> Box ∨ PO

FailureResolution
  -> Box ∨ PO

BeamSeed
  -> Box ∨ PO
```

これは強い。
状態表の主要入口は、もう `Box` か `PO` へ落ちる。

## 次に攻める場所

次は `Box` の projection を作る。

`SourcePressureOrientedNeighborBoxState` は、

```text id="35hx7u"
D
boxLeft
boxRight
```

を持つ。caller はまずこれを使いたい。

追加候補：

```lean id="h5xh9c"
SourcePressureOrientedNeighborBoxState.left_box
SourcePressureOrientedNeighborBoxState.right_box
SourcePressureOrientedNeighborBoxState.diagnostic
```

形：

```lean id="v0i254"
theorem SourcePressureOrientedNeighborBoxState.left_box
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    SourcePressureBeamCenteredLocalPulseBox n k r L W
```

```lean id="uh6gun"
theorem SourcePressureOrientedNeighborBoxState.right_box
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    SourcePressureBeamCenteredLocalPulseBox n k r L W'
```

```lean id="tq0jxa"
theorem SourcePressureOrientedNeighborBoxState.diagnostic
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    SourcePressureOrientedNeighborDiagnosticState L W W'
```

これは薄いが重要。
次の transport / comparison で毎回 `rcases h with ⟨hD, hL, hR⟩` を書かずに済む。

## 次の Codex 指示

```text id="j167l7"
Goal:
  Add projection lemmas for SourcePressureOrientedNeighborBoxState.

Add in PressureState.lean:

  theorem SourcePressureOrientedNeighborBoxState.diagnostic
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureOrientedNeighborBoxState L W W') :
      SourcePressureOrientedNeighborDiagnosticState L W W'

  theorem SourcePressureOrientedNeighborBoxState.left_box
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureOrientedNeighborBoxState L W W') :
      SourcePressureBeamCenteredLocalPulseBox n k r L W

  theorem SourcePressureOrientedNeighborBoxState.right_box
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureOrientedNeighborBoxState L W W') :
      SourcePressureBeamCenteredLocalPulseBox n k r L W'

Proof:
  rcases h with ⟨hD, hL, hR⟩
  exact ...

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の次

projection が入ったら、いよいよ比較へ進む。

候補：

```text id="drx34f"
Box(W,W')
  -> signs(W)
  -> signs(W')
  -> compare W.val and W'.val
```

まずは orientation から `AdjacentPairInList L W W'` を取り出す projection も欲しい。

```lean id="vt0w1t"
SourcePressureOrientedNeighborDiagnosticState.adjacentPair
```

これで、

```text id="xx610p"
Box
  -> D
  -> AdjacentPairInList L W W'
```

が使える。

次の目標は、

```text id="8eh4lc"
Box の projection 群
+
orientation projection
```

を整えて、pair 比較へ入ること。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 993fecd1..6d485d5d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -710,4 +710,74 @@ theorem sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap
   sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
     (sourcePressureBeamSeedState_to_failureResolutionState h)
 
+/--
+Failure resolution splits into either a two-endpoint oriented neighbor box or a
+concrete pair-level overlap obstruction.
+
+This is the boxed version of
+`sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap`.
+Only the diagnostic branch is strengthened, by packaging state `D` into
+`SourcePressureOrientedNeighborBoxState`.  The overlap branch is kept as the
+same concrete adjacent-pair obstruction.
+-/
+theorem sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureFailureResolutionState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborBoxState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
+  rcases
+    sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
+      h with hdiag | hoverlap
+  · rcases hdiag with ⟨W, W', hD⟩
+    exact Or.inl
+      ⟨W, W',
+        sourcePressureOrientedNeighborDiagnosticState_to_boxState hD⟩
+  · exact Or.inr hoverlap
+
+/--
+Sorted failure reaches the boxed diagnostic/obstruction split.
+
+This lifts the sorted-failure entry point through failure resolution and then
+through the boxed diagnostic branch.  It remains a local state-automaton
+wrapper and does not add coverage, propagation, overlap repair, or convergence.
+-/
+theorem sourcePressureSortedFailureState_to_orientedNeighborBox_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureSortedFailureState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborBoxState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
+    (sourcePressureSortedFailureState_to_failureResolutionState h)
+
+/--
+Beam seed reaches the boxed diagnostic/obstruction split.
+
+This is the Beam-facing entry point for the same boxed split:
+
+```text
+BeamSeed
+  -> OrientedNeighborBox
+   ∨ PairOverlapObstruction
+```
+-/
+theorem sourcePressureBeamSeedState_to_orientedNeighborBox_or_pairOverlap
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (h : SourcePressureBeamSeedState L) :
+    (∃ W W',
+      SourcePressureOrientedNeighborBoxState L W W') ∨
+      ∃ A B,
+        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
+          SourcePressureLocalIslandWitnessPairOverlapObstruction A B :=
+  sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
+    (sourcePressureBeamSeedState_to_failureResolutionState h)
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-253.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-253.md
new file mode 100644
index 00000000..ab81cee2
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-253.md
@@ -0,0 +1,83 @@
+# Report: petal-253
+
+## Goal
+
+Lift the refined diagnostic/overlap split from oriented diagnostic state `D` to
+the two-endpoint box state.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
+theorem sourcePressureSortedFailureState_to_orientedNeighborBox_or_pairOverlap
+theorem sourcePressureBeamSeedState_to_orientedNeighborBox_or_pairOverlap
+```
+
+The main split is now:
+
+```text
+FailureResolutionState L
+  -> OrientedNeighborBoxState L W W'
+   OR
+     AdjacentPairInList L A B
+     + PairOverlapObstruction A B
+```
+
+The sorted-failure and Beam-seed versions are thin lifts through the existing
+state transitions.
+
+## Proof Shape
+
+The failure-resolution theorem uses:
+
+```lean
+sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
+sourcePressureOrientedNeighborDiagnosticState_to_boxState
+```
+
+Only the diagnostic branch is strengthened from `D` to the two-endpoint box.
+The overlap branch is left as the already-refined concrete pair-level overlap
+obstruction.
+
+## Automaton Reading
+
+The state exits are now:
+
+```text
+R -> Box ∨ PO
+S -> Box ∨ PO
+B -> Box ∨ PO
+```
+
+where:
+
+- `R` is failure resolution,
+- `S` is sorted failure,
+- `B` is Beam seed,
+- `Box` is the two-endpoint oriented neighbor box,
+- `PO` is a concrete pair-level overlap obstruction.
+
+## Guardrails
+
+This checkpoint only packages an already-local diagnostic branch.  It does not
+add:
+
+- transport or propagation,
+- list-wide coverage,
+- aggregation,
+- canonical witness selection,
+- overlap repair,
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
