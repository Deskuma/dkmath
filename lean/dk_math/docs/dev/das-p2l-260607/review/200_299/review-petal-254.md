# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 3590d2c81eef42ef0d32917d3cfa679e1c86014e

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:493) に box projection 群を追加しました。

追加 theorem:

```lean
SourcePressureOrientedNeighborBoxState.diagnostic
SourcePressureOrientedNeighborBoxState.left_box
SourcePressureOrientedNeighborBoxState.right_box
```

あわせて次段の比較で必要になる orientation projection も追加しています。

```lean
SourcePressureOrientedNeighborDiagnosticState.adjacentPair
SourcePressureOrientedNeighborBoxState.adjacentPair
```

これで `Box(W,W') -> D(W,W') -> AdjacentPairInList L W W'` が直接使えるようになりました。

レポートは [report-petal-254.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-254.md:1) に追加しました。

確認済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Review

## 判定

採用。
`Box` が caller-facing surface として使いやすくなった。

追加：

```lean id="7ek7et"
SourcePressureOrientedNeighborBoxState.diagnostic
SourcePressureOrientedNeighborBoxState.left_box
SourcePressureOrientedNeighborBoxState.right_box
```

さらに比較用 hook として、

```lean id="4h0lua"
SourcePressureOrientedNeighborDiagnosticState.adjacentPair
SourcePressureOrientedNeighborBoxState.adjacentPair
```

も入った。これで、

```text id="iylv02"
Box(W,W')
  -> D(W,W')
  -> AdjacentPairInList L W W'
```

が直接使える。

## 増えた事実

`SourcePressureOrientedNeighborBoxState L W W'` から、次が即座に取れる。

```text id="snqzea"
D(W,W')
left endpoint pulse box W
right endpoint pulse box W'
ordered adjacent pair W -> W'
```

これで `Box` を毎回 `rcases` しなくてよい。

状態表では、

```text id="gop6fx"
Box
  -> D
  -> AdjacentPairInList

Box
  -> left_box
  -> right_box
```

が整った。

## 現在の状態表

```text id="klnd26"
SortedFailure
  -> Box ∨ PO

FailureResolution
  -> Box ∨ PO

BeamSeed
  -> Box ∨ PO

Box
  -> D
  -> AdjacentPairInList

Box
  -> PulseBox(W)
  -> PulseBox(W')
```

ここまでで「入口」「出口」「中身の取り出し」が揃った。

## 次に攻める定理

次は **Box 内の向き比較**。

`AdjacentPairInList L W W'` から、`W` と `W'` の順序・位置・値の関係が何か取れるかを見る。

候補はまずこれ。

```lean id="9e7rxc"
SourcePressureOrientedNeighborBoxState.adjacent_before
```

ただし既存名に合わせるなら、`AdjacentPairInList` から `SourcePressureLocalIslandWitnessBefore W W'` が取れるかを調べる。

狙い：

```lean id="ddke56"
theorem SourcePressureOrientedNeighborBoxState.before
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureOrientedNeighborBoxState L W W') :
    SourcePressureLocalIslandWitnessBefore W W'
```

もし `Before` が直接出ないなら、まず `AdjacentPairInList` の projection を探す。

## Codex 指示

```text id="9paj4d"
Goal:
  Extract the ordered before/value relation from SourcePressureOrientedNeighborBoxState.

Inspect:
  SourcePressureLocalIslandWitnessAdjacentPairInList
  SourcePressureLocalIslandWitnessBefore
  any theorem from AdjacentPairInList to Before / val order / list order

Try to add in PressureState.lean:

  theorem SourcePressureOrientedNeighborBoxState.before
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureOrientedNeighborBoxState L W W') :
      SourcePressureLocalIslandWitnessBefore W W'

If Before is not available, add the strongest direct projection available from
h.adjacentPair, for example:

  theorem SourcePressureOrientedNeighborBoxState.left_before_right_val
      ... :
      W.val < W'.val

or report the exact existing relation.

Use:
  h.adjacentPair
  existing AdjacentPairInList projection lemmas

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

`Box(W,W')` は二点の局所 pulse。
次はこの二点の **順序** を取る。

```text id="2tf41b"
Box(W,W')
  -> W before W'
  -> compare W.val and W'.val
```

ここが取れると、pair comparison 層に入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 6d485d5d..9981cedd 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -489,6 +489,63 @@ def SourcePressureOrientedNeighborBoxState
     SourcePressureBeamCenteredLocalPulseBox n k r L W ∧
       SourcePressureBeamCenteredLocalPulseBox n k r L W'

+/-- Project the oriented diagnostic component from a two-endpoint box state. -/
+theorem SourcePressureOrientedNeighborBoxState.diagnostic
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborBoxState L W W') :
+    SourcePressureOrientedNeighborDiagnosticState L W W' := by
+  rcases h with ⟨hD, _hL, _hR⟩
+  exact hD
+
+/-- Project the left endpoint centered local pulse box from a two-endpoint box state. -/
+theorem SourcePressureOrientedNeighborBoxState.left_box
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborBoxState L W W') :
+    SourcePressureBeamCenteredLocalPulseBox n k r L W := by
+  rcases h with ⟨_hD, hL, _hR⟩
+  exact hL
+
+/-- Project the right endpoint centered local pulse box from a two-endpoint box state. -/
+theorem SourcePressureOrientedNeighborBoxState.right_box
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborBoxState L W W') :
+    SourcePressureBeamCenteredLocalPulseBox n k r L W' := by
+  rcases h with ⟨_hD, _hL, hR⟩
+  exact hR
+
+/--
+Project the ordered adjacent-pair address from an oriented diagnostic state.
+
+This is the orientation hook needed by the next comparison layer:
+
+```text
+Box -> D -> AdjacentPairInList L W W'
+```
+-/
+theorem SourcePressureOrientedNeighborDiagnosticState.adjacentPair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborDiagnosticState L W W') :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' := by
+  rcases h with ⟨hin, _hdiag, _hentry, _haddr, _hexit, _hentry', _haddr', _hexit'⟩
+  exact hin
+
+/-- Project the ordered adjacent-pair address from a two-endpoint box state. -/
+theorem SourcePressureOrientedNeighborBoxState.adjacentPair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureOrientedNeighborBoxState L W W') :
+    SourcePressureLocalIslandWitnessAdjacentPairInList L W W' :=
+  h.diagnostic.adjacentPair
+
 /--
 Package an oriented neighbor diagnostic into the two-endpoint box state.

diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-254.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-254.md
new file mode 100644
index 00000000..6b20795b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-254.md
@@ -0,0 +1,81 @@
+# Report: petal-254
+
+## Goal
+
+Add projection lemmas for `SourcePressureOrientedNeighborBoxState`.
+
+## Implemented
+
+Added in `DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+theorem SourcePressureOrientedNeighborBoxState.diagnostic
+theorem SourcePressureOrientedNeighborBoxState.left_box
+theorem SourcePressureOrientedNeighborBoxState.right_box
+```
+
+These project the three stored components of the two-endpoint box:
+
+```text
+Box(W,W') -> D(W,W')
+Box(W,W') -> left endpoint pulse box W
+Box(W,W') -> right endpoint pulse box W'
+```
+
+## Extra Comparison Hook
+
+Also added the next natural orientation projections:
+
+```lean
+theorem SourcePressureOrientedNeighborDiagnosticState.adjacentPair
+theorem SourcePressureOrientedNeighborBoxState.adjacentPair
+```
+
+These establish the comparison-ready path:
+
+```text
+Box(W,W') -> D(W,W') -> AdjacentPairInList L W W'
+```
+
+## Meaning
+
+The two-endpoint box is now usable as a caller-facing surface.  Downstream
+proofs no longer need to destruct the box manually to access the diagnostic,
+the left endpoint local box, the right endpoint local box, or the ordered
+adjacent-pair address.
+
+## Next Direction
+
+The natural next comparison layer is:
+
+```text
+Box(W,W')
+  -> signs(W)
+  -> signs(W')
+  -> AdjacentPairInList L W W'
+  -> compare W.val and W'.val
+```
+
+This checkpoint prepared the projection API required for that move.
+
+## Guardrails
+
+These are projection theorems only.  They do not add:
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
