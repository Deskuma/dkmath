# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 6d484623544625d373a0e18055246cfaee3ae966

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:785) に、`val_lt_of_sorted` から使いやすい小補題を追加しました。

追加 theorem:

- `SourcePressureOrientedNeighborBoxState.val_ne_of_sorted`
- `SourcePressureOrientedNeighborBoxState.not_val_ge_of_sorted`

これで次が直接使えます。

```text
Box(W,W') + sorted(L)
  -> W.val ≠ W'.val
  -> ¬ W'.val ≤ W.val
```

レポート:
[report-petal-258.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-258.md)

検証:

- `lake build DkMath.Collatz.PetalBridge.PressureState` 成功
- `lake build DkMath.Collatz.PetalBridge` 成功
- `git diff --check` 成功

差分は `PressureState.lean` と `report-petal-258.md` です。

## Review

## 判定

採用。
`val_lt_of_sorted` から、非衝突・逆向き排除用の小補題が出た。

追加：

```lean id="ymsj6d"
SourcePressureOrientedNeighborBoxState.val_ne_of_sorted
SourcePressureOrientedNeighborBoxState.not_val_ge_of_sorted
```

これで、

```text id="jvjpcd"
Box(W,W') + sorted(L)
  -> W.val ≠ W'.val
  -> ¬ W'.val ≤ W.val
```

が直接使える。`val_lt_of_sorted` の caller-facing wrapper として良い位置。

## 増えた事実

比較層の基本 API が揃った。

```text id="4h8z82"
Box(W,W') + sorted(L)
  -> W.val < W'.val
  -> W.val ≤ W'.val
  -> W.val ≠ W'.val
  -> ¬ W'.val ≤ W.val
```

これで reverse branch を潰しやすくなった。

## 現在の状態表

```text id="7cw50z"
SortedFailure / FailureResolution / BeamSeed
  -> Box ∨ PO

Box + sorted(L)
  -> W before W'
  -> W.val < W'.val
  -> W.val ≠ W'.val
  -> not reverse value order
```

ここまでで、`Box` は順序付き二点局所状態としてかなり完成してきた。

## 次に攻める定理

次は **reverse box orientation の排除**。

`Box(W,W')` と `Box(W',W)` が同じ sorted list 上で同時にあると、

```text id="j84nab"
W.val < W'.val
W'.val < W.val
```

になって矛盾する。

狙い：

```lean id="6i9utx"
theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (hbox : SourcePressureOrientedNeighborBoxState L W W')
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    ¬ SourcePressureOrientedNeighborBoxState L W' W
```

証明は薄い。

```lean id="7lq3za"
intro hrev
exact hbox.not_val_ge_of_sorted hsorted
  (hrev.val_le_of_sorted hsorted)
```

これが入ると、pair comparison で「逆向き候補」を消せる。

## Codex 指示

```text id="a5r07y"
Goal:
  Exclude reverse box orientation under the same sorted witness list.

Add in PressureState.lean:

  theorem SourcePressureOrientedNeighborBoxState.not_reverse_box_of_sorted
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (hbox : SourcePressureOrientedNeighborBoxState L W W')
      (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
      ¬ SourcePressureOrientedNeighborBoxState L W' W

Proof idea:
  intro hrev
  exact hbox.not_val_ge_of_sorted hsorted
    (hrev.val_le_of_sorted hsorted)

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

これで、

```text id="2wqb7d"
forward Box
  -> reverse Box impossible
```

になる。

その次は `Box ∨ PO` の分岐で、`Box` 側を forward orientation として確定し、`PO` 側を obstruction として別処理する pair comparison 層へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 1ce48b95..011887ec 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -776,6 +776,36 @@ theorem SourcePressureOrientedNeighborBoxState.val_le_of_sorted
     W.val ≤ W'.val :=
   le_of_lt (hbox.val_lt_of_sorted hsorted)
 
+/--
+Sorted oriented neighbor boxes have distinct endpoint depths.
+
+This is a caller-facing corollary of `val_lt_of_sorted`, useful when later
+non-collision arguments need only inequality rather than the full order.
+-/
+theorem SourcePressureOrientedNeighborBoxState.val_ne_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    W.val ≠ W'.val :=
+  ne_of_lt (hbox.val_lt_of_sorted hsorted)
+
+/--
+Sorted oriented neighbor boxes rule out the reverse value order.
+
+This is the negative-orientation wrapper for callers that want to discharge a
+reverse comparison branch directly from the sorted box state.
+-/
+theorem SourcePressureOrientedNeighborBoxState.not_val_ge_of_sorted
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hbox : SourcePressureOrientedNeighborBoxState L W W')
+    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
+    ¬ W'.val ≤ W.val :=
+  not_le_of_gt (hbox.val_lt_of_sorted hsorted)
+
 /--
 Package an oriented neighbor diagnostic into the two-endpoint box state.
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-258.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-258.md
new file mode 100644
index 00000000..75fb7d6a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-258.md
@@ -0,0 +1,85 @@
+# Report: petal-258
+
+## Goal
+
+Add small caller-facing consequences of:
+
+```lean
+SourcePressureOrientedNeighborBoxState.val_lt_of_sorted
+```
+
+The target is the non-collision / reverse-order-exclusion surface:
+
+```text
+Box(W,W') + sorted(L)
+  -> W.val < W'.val
+  -> W.val != W'.val
+  -> not W'.val <= W.val
+```
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem SourcePressureOrientedNeighborBoxState.val_ne_of_sorted
+theorem SourcePressureOrientedNeighborBoxState.not_val_ge_of_sorted
+```
+
+Both are direct wrappers over `val_lt_of_sorted`.
+
+## Meaning
+
+Downstream callers no longer need to destruct or re-prove the strict order
+when they only need one of the following lighter facts:
+
+```lean
+W.val != W'.val
+not W'.val <= W.val
+```
+
+This keeps later non-collision and reverse-orientation branches short and
+stable.
+
+## Guardrails
+
+These theorems do not add a new mathematical invariant.  They are API wrappers
+around the sorted oriented neighbor box comparison:
+
+```lean
+hbox.val_lt_of_sorted hsorted
+```
+
+They remain local to the explicit two-endpoint box and the supplied sortedness
+invariant.  They do not imply global uniqueness of pressure depths, global
+coverage, transport, propagation, or convergence.
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
+Both builds completed successfully.
+
+`git diff --check` is run as the final whitespace gate for this checkpoint.
+
+## Next Branch Prediction
+
+The next useful layer is pair comparison proper.
+
+Candidate branch:
+
+```text
+Box(W,W') + sorted(L)
+  -> W.val < W'.val
+  -> reverse order impossible
+  -> pair-comparison branch can select the forward orientation
+```
+
+If a caller needs address-level negation rather than value-level negation, add
+the corresponding wrapper at the address-before layer.  Otherwise,
+`not_val_ge_of_sorted` should be enough for the next local comparison branch.
````
`````
