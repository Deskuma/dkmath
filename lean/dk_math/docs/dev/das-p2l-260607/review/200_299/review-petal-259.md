# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: ab881661b25e091931326813ed61761667cc4d63

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:818) に追加しました。

```lean
theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
```

内容は狙い通りです。

```text
forward Box(W,W') + sorted(L)
  -> W.val < W'.val

reverse Box(W',W) + sorted(L)
  -> W'.val ≤ W.val

よって reverse Box は不可能
```

レポート:
[report-petal-259.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-259.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureState` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `git diff --check` 成功

差分は `PressureState.lean` と `report-petal-259.md` です。

## Review

## 判定

採用。
`Box(W,W')` の reverse orientation が、sorted witness list の下で排除された。

追加：

```lean id="y23tga"
theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
```

これで、

```text id="bnfwkf"
Box(W,W') + sorted(L)
  -> ¬ Box(W',W)
```

が直接使える。証明は `W.val < W'.val` と `W'.val ≤ W.val` の衝突で閉じている。

## 増えた事実

比較層の orientation が固定された。

```text id="zidxjd"
forward Box(W,W') + sorted(L)
  -> W.val < W'.val
  -> reverse Box(W',W) impossible
```

これで `Box` 側は、単なる二点診断ではなく、

```text id="c64so3"
sorted list 上で一方向にしか存在できない二点診断
```

になった。

## 現在の状態表

```text id="3yoxrx"
SortedFailure / FailureResolution / BeamSeed
  -> Box ∨ PO

Box + sorted(L)
  -> W.val < W'.val
  -> W.val ≠ W'.val
  -> ¬ W'.val ≤ W.val
  -> ¬ reverse Box
```

ここまでで、`Box` 側の forward orientation はかなり固い。

## 次に攻める定理

次は `Box ∨ PO` の分岐に sortedness を加えて、comparison-ready な形へ持ち上げる。

まず `FailureResolutionState` 版。

```lean id="jpl3b3"
theorem sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborBoxState L W W' ∧
        W.val < W'.val ∧
          ¬ SourcePressureOrientedNeighborBoxState L W' W) ∨
      ∃ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
          SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

これで、

```text id="yaf6d7"
FailureResolution + sorted(L)
  -> forward Box comparison
   ∨ PairOverlap
```

になる。

## Codex 指示

```text id="xsx46f"
Goal:
  Lift Box ∨ PairOverlap into a comparison-ready split under sortedness.

Add in PressureState.lean:

  theorem sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
      (h : SourcePressureFailureResolutionState L) :
      (∃ W W',
        SourcePressureOrientedNeighborBoxState L W W' ∧
          W.val < W'.val ∧
            ¬ SourcePressureOrientedNeighborBoxState L W' W) ∨
        ∃ A B,
          SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
            SourcePressureLocalIslandWitnessPairOverlapObstruction A B

Use:
  sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
  SourcePressureOrientedNeighborBoxState.val_lt_of_sorted
  SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted

If easy, also add SortedFailureState and BeamSeedState wrappers.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次でこうなる。

```text id="utjpnb"
R + sorted(L) -> ForwardBoxComparison ∨ PO
S + sorted(L) -> ForwardBoxComparison ∨ PO
B + sorted(L) -> ForwardBoxComparison ∨ PO
```

`Box` 側は forward comparison、`PO` 側は obstruction。
この分岐ができると、pair comparison 層の表面が完成する。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 011887ec..0f7d29fd 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -806,6 +806,26 @@ theorem SourcePressureOrientedNeighborBoxState.not_val_ge_of_sorted
     ¬ W'.val ≤ W.val :=
   not_le_of_gt (hbox.val_lt_of_sorted hsorted)

+/--
+A sorted witness list forbids the same box from appearing in the reverse
+orientation.
+
+The forward box gives `W.val < W'.val`; a reverse box over the same sorted list
+would give `W'.val ≤ W.val`.  The two facts are incompatible.  This is a local
+orientation exclusion only: it does not select a canonical box globally and does
+not assert coverage of all possible neighbor pairs.
+-/
+theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    ¬ SourcePressureOrientedNeighborBoxState L W' W := by
+  intro hrev
+  exact hbox.not_val_ge_of_sorted hsorted
+    (hrev.val_le_of_sorted hsorted)
+
 /--
 Package an oriented neighbor diagnostic into the two-endpoint box state.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-259.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-259.md
new file mode 100644
index 00000000..4dcc79e3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-259.md
@@ -0,0 +1,85 @@
+# Report: petal-259
+
+## Goal
+
+Exclude reverse box orientation under the same sorted witness list.
+
+Target theorem:
+
+```lean
+theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
+```
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
+```
+
+The proof is the expected local contradiction:
+
+```text
+forward box + sorted(L) -> W.val < W'.val
+reverse box + sorted(L) -> W'.val <= W.val
+```
+
+These two facts are incompatible.
+
+## Meaning
+
+The oriented two-endpoint box now has an explicit anti-symmetry-style surface:
+
+```text
+SourcePressureOrientedNeighborBoxState L W W'
+  + SourcePressureLocalIslandWitnessListSortedBefore L
+  -> not SourcePressureOrientedNeighborBoxState L W' W
+```
+
+This is the first direct reverse-orientation exclusion theorem at the box
+layer.
+
+## Guardrails
+
+This theorem is still local to:
+
+* the explicit forward box;
+* the proposed reverse box;
+* the same sorted witness list.
+
+It does not choose a canonical box, does not sort an arbitrary list, does not
+claim all pairs are represented, and does not add any global Collatz claim.
+
+## Verification
+
+Commands run from `lean/dk_math`:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+```
+
+`git diff --check` is run as the final whitespace gate.
+
+## Next Branch Prediction
+
+The next layer can use the split:
+
+```text
+Box(W,W') or PairOverlap
+```
+
+On the `Box` side, sortedness now fixes the forward orientation and rules out
+the reverse box.  On the `PairOverlap` side, the obstruction remains separate.
+
+The natural next theorem shape is:
+
+```text
+sorted(L)
+  + (oriented box or pair overlap)
+  -> (forward-oriented value comparison and not reverse box) or pair overlap
+```
+
+This would prepare the pair-comparison layer without merging the obstruction
+branch into the diagnostic branch.
````
`````
