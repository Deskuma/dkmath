# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 175ef0ac8ae656295f91d6b3be289d40a6990b0b

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:484) に `SourcePressureOrientedNeighborBoxState` を追加し、[同ファイル](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:502) に `sourcePressureOrientedNeighborDiagnosticState_to_boxState` を追加しました。

設計は `SourcePressureOrientedNeighborDiagnosticState L W W'` に加えて、左右それぞれの `SourcePressureBeamCenteredLocalPulseBox` を持つ形です。これで各 endpoint の sign pattern、3 点 margin bounds、2 点 net-drop bounds を既存の一端点 box contract 経由で保持します。

レポートは [report-petal-252.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-252.md:1) に追加しました。

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Review

## 判定

採用。
`OrientedNeighborDiagnosticState` が、二点 box 状態へ昇格した。

追加：

```lean id="qjmwaz"
def SourcePressureOrientedNeighborBoxState
```

```lean id="zrqbsx"
theorem sourcePressureOrientedNeighborDiagnosticState_to_boxState
```

内容は、

```text id="lhpnv9"
OrientedNeighborDiagnosticState L W W'
+
CenteredLocalPulseBox W
+
CenteredLocalPulseBox W'
```

左右 endpoint がそれぞれ `SourcePressureBeamCenteredLocalPulseBox` を持つ形。設計として良い。既存の一端点 box contract を再利用しているので、定義が膨れず、今後一端点 box を強化しても追従できる。

## 増えた事実

これで状態 `D` は、単なる diagnostic ではなく、**二点 local pulse box** に変換できる。

```text id="4b3rot"
D(W,W')
  -> Box(W,W')
```

より具体的には、

```text id="0n2u23"
W:
  sign pattern
  margin height bounds
  net-drop bounds

W':
  sign pattern
  margin height bounds
  net-drop bounds
```

が両方揃う。

## 状態表の更新

現在の主経路：

```text id="a3wkov"
SortedFailure
  -> D ∨ PO

FailureResolution
  -> D ∨ PO

BeamSeed
  -> D ∨ PO

D
  -> OrientedNeighborBoxState
```

つまり、

```text id="zlm9jq"
S/R/B -> D ∨ PO
D -> Box2
```

まで到達。

これはかなり良い。
状態遷移表が「名前だけ」ではなく、実際に証拠を運べるようになってきた。

## 次に攻める定理

次は上流入口から一気に二点 box まで持ち上げる。

狙いはこれ。

```lean id="myk0wo"
theorem sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborBoxState L W W') ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

証明は、

```text id="fad3ca"
FailureResolution -> D ∨ PO
D -> Box2
```

の合成。

続けて、必要なら `SortedFailure` / `BeamSeed` 版も作る。

## Codex 指示

```text id="xw1c3r"
Goal:
  Lift the refined diagnostic/overlap split from D to two-endpoint BoxState.

Add in PressureState.lean:

  theorem sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (h : SourcePressureFailureResolutionState L) :
      (∃ W W',
        SourcePressureOrientedNeighborBoxState L W W') ∨
        ∃ A B,
          SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
            SourcePressureLocalIslandWitnessPairOverlapObstruction A B

Use:
  sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
  sourcePressureOrientedNeighborDiagnosticState_to_boxState

If easy, also add:

  sourcePressureSortedFailureState_to_orientedNeighborBox_or_pairOverlap
  sourcePressureBeamSeedState_to_orientedNeighborBox_or_pairOverlap

using existing sorted/seed refined splits.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

これで入口がこうなる。

```text id="n1r4mc"
FailureResolution
  -> Box2 ∨ PO

SortedFailure
  -> Box2 ∨ PO

BeamSeed
  -> Box2 ∨ PO
```

ここまで行くと、状態表の実用面はかなり強い。
その次は `Box2` と `PO` を比較対象にして、transport / obstruction の分岐を数値で読む段階へ入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 876d46f4..993fecd1 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -464,6 +464,83 @@ theorem sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
     sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left haddr' hexit'
   exact ⟨hprev, hcenter, haddr', hnext⟩
 
+/--
+Two-endpoint box state for an oriented neighbor diagnostic.
+
+This packages state `D` together with the finite local pulse box at both
+endpoints.  Each endpoint box contains:
+
+* the three-margin sign pattern around the native depth;
+* margin-height bounds at previous, center, and next depths;
+* net-drop bounds at the entry and exit adjacent edges.
+
+Using the existing `SourcePressureBeamCenteredLocalPulseBox` keeps the
+one-endpoint box contract authoritative and prevents this two-endpoint state
+from silently drifting if the pulse-box API is refined later.
+
+This is still a local two-endpoint package.  It does not assert transport,
+propagation, coverage, aggregation, overlap repair, or convergence.
+-/
+def SourcePressureOrientedNeighborBoxState
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (W W' : SourcePressureLocalIslandWitness n k r) : Prop :=
+  SourcePressureOrientedNeighborDiagnosticState L W W' ∧
+    SourcePressureBeamCenteredLocalPulseBox n k r L W ∧
+      SourcePressureBeamCenteredLocalPulseBox n k r L W'
+
+/--
+Package an oriented neighbor diagnostic into the two-endpoint box state.
+
+The oriented diagnostic supplies the endpoint sign patterns through
+`sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs` and
+`sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs`.
+The finite height and jump boxes are supplied pointwise by
+`sourcePressureMarginInt_bounds_window` and
+`sourcePressureNetDropInt_bounds_window`.
+-/
+theorem sourcePressureOrientedNeighborDiagnosticState_to_boxState
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
+    SourcePressureOrientedNeighborBoxState L W W' := by
+  rcases h with
+    ⟨hin, hdiag, hentry, haddr, hexit, hentry', haddr', hexit'⟩
+  let hD : SourcePressureOrientedNeighborDiagnosticState L W W' :=
+    ⟨hin, hdiag, hentry, haddr, hexit, hentry', haddr', hexit'⟩
+  rcases
+    sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
+      hD with
+    ⟨hprev, hcenter, haddrLeft, hnext⟩
+  rcases
+    sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
+      hD with
+    ⟨hprev', hcenter', haddrRight, hnext'⟩
+  have hboxLeft : SourcePressureBeamCenteredLocalPulseBox n k r L W :=
+    ⟨sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem hin,
+      hprev,
+      hcenter,
+      haddrLeft,
+      hnext,
+      sourcePressureMarginInt_bounds_window n k (r + (W.val - 1)),
+      sourcePressureMarginInt_bounds_window n k (r + W.val),
+      sourcePressureMarginInt_bounds_window n k (r + W.val + 1),
+      sourcePressureNetDropInt_bounds_window n k r (W.val - 1),
+      sourcePressureNetDropInt_bounds_window n k r W.val⟩
+  have hboxRight : SourcePressureBeamCenteredLocalPulseBox n k r L W' :=
+    ⟨sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem hin,
+      hprev',
+      hcenter',
+      haddrRight,
+      hnext',
+      sourcePressureMarginInt_bounds_window n k (r + (W'.val - 1)),
+      sourcePressureMarginInt_bounds_window n k (r + W'.val),
+      sourcePressureMarginInt_bounds_window n k (r + W'.val + 1),
+      sourcePressureNetDropInt_bounds_window n k r (W'.val - 1),
+      sourcePressureNetDropInt_bounds_window n k r W'.val⟩
+  exact ⟨hD, hboxLeft, hboxRight⟩
+
 /--
 Recovered adjacent state enters the oriented neighbor diagnostic state.
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-252.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-252.md
new file mode 100644
index 00000000..cd09a2c3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-252.md
@@ -0,0 +1,77 @@
+# Report: petal-252
+
+## Goal
+
+Package `SourcePressureOrientedNeighborDiagnosticState` into a two-endpoint
+box state.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+def SourcePressureOrientedNeighborBoxState
+theorem sourcePressureOrientedNeighborDiagnosticState_to_boxState
+```
+
+The new box state packages:
+
+```text
+OrientedNeighborDiagnosticState L W W'
++ CenteredLocalPulseBox W
++ CenteredLocalPulseBox W'
+```
+
+Each endpoint box carries:
+
+- the previous/center/next margin sign pattern,
+- margin-height bounds at previous, center, and next depths,
+- net-drop bounds at the entry and exit adjacent edges.
+
+## Design Choice
+
+The definition reuses the existing one-endpoint contract:
+
+```lean
+SourcePressureBeamCenteredLocalPulseBox
+```
+
+instead of duplicating every bound inline.  This keeps the authoritative
+one-endpoint box API in one place.  If the one-endpoint pulse-box contract is
+refined later, the two-endpoint state follows it automatically.
+
+## Proof Shape
+
+The constructor theorem uses:
+
+```lean
+sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
+sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
+sourcePressureMarginInt_bounds_window
+sourcePressureNetDropInt_bounds_window
+```
+
+Membership of `W` and `W'` is projected from the stored adjacent-pair-in-list
+orientation.
+
+## Guardrails
+
+This is still only a local two-endpoint package.  It does not add:
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
