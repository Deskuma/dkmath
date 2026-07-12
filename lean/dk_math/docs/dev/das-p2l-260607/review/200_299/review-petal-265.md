# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 38dbceaa8acafc7923826f347575707c01e61f7d

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:999) に FPC 向け projection を追加しました。

- `SourcePressureForwardPairComparisonState.left_mem`
- `SourcePressureForwardPairComparisonState.right_mem`
- `SourcePressureForwardPairComparisonState.left_signs`
- `SourcePressureForwardPairComparisonState.right_signs`

実装は `h.left_box.signs` / `h.right_box.signs` への薄い転送です。これで `FPC -> left/right signs + val_lt + adjacentPair` の呼び出し面が揃いました。

レポートは [report-petal-265.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-265.md:1) に追加済みです。

検証:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

すべて通過しました。

## Review

## 判定

採用。
`ForwardPairComparisonState` から左右 endpoint の sign surface が直に取れるようになった。

追加：

```lean id="dr9v4o"
SourcePressureForwardPairComparisonState.left_mem
SourcePressureForwardPairComparisonState.right_mem
SourcePressureForwardPairComparisonState.left_signs
SourcePressureForwardPairComparisonState.right_signs
```

実装は `h.left_box.signs` / `h.right_box.signs` への薄い転送。これで `FPC` から、左右の membership と sign-and-target payload を直接呼び出せる。

## 増えた事実

`SourcePressureForwardPairComparisonState L W W'` から、現在これが揃う。

```text id="8k7xmc"
FPC
  -> AdjacentPairInList L W W'
  -> left_box / right_box
  -> left_signs / right_signs
  -> W.val < W'.val
  -> ¬ reverse Box
```

左右 sign はそれぞれ、

```text id="41r8db"
endpoint ∈ L
previous margin <= 0
center margin   >  0
addressed depth target
next margin     <= 0
```

を持つ。これで pair-comparison theorem の入口として、かなり扱いやすくなった。

## 現在の状態表

```text id="tyd7g7"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> left/right signs
  -> W.val < W'.val
  -> AdjacentPairInList
```

良い。`PressureState` はかなり実用 API になってきた。

## 次に攻める定理

次は `FPC` から **左右中心がともに正**、かつ **左が右より前** を束ねる。

狙い：

```lean id="z56hfj"
theorem SourcePressureForwardPairComparisonState.center_pos_pair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    0 < SourcePressureMarginInt n k (r + W.val) ∧
      0 < SourcePressureMarginInt n k (r + W'.val) ∧
        W.val < W'.val
```

これは `h.left_signs`, `h.right_signs`, `h.val_lt` だけで取れる。

さらに次に使いやすい形：

```lean id="f7yal6"
theorem SourcePressureForwardPairComparisonState.center_targets_pair
```

で、左右の addressed target も束ねる。

## Codex 指示

```text id="9asqsf"
Goal:
  Add the first actual pair-comparison facts from
  SourcePressureForwardPairComparisonState.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.center_pos_pair
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        0 < SourcePressureMarginInt n k (r + W'.val) ∧
          W.val < W'.val

  theorem SourcePressureForwardPairComparisonState.center_targets_pair
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      SourcePressureBeamAddressedDepthTarget L W.val ∧
        SourcePressureBeamAddressedDepthTarget L W'.val ∧
          W.val < W'.val

Use:
  h.left_signs
  h.right_signs
  h.val_lt

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `FPC` はこう読める。

```text id="p5ux66"
FPC
  -> left center positive
  -> right center positive
  -> both addressed targets
  -> W.val < W'.val
```

ここから、左右 pulse の「正中心が順序を持って並ぶ」比較補題へ入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index ac4bbc57..4d639001 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -995,6 +995,56 @@ theorem SourcePressureForwardPairComparisonState.not_reverse_box
     ¬ SourcePressureOrientedNeighborBoxState L W' W :=
   h.forward.not_reverse_box
 
+/-- The left endpoint of a forward pair comparison state is a member of the list. -/
+theorem SourcePressureForwardPairComparisonState.left_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    W ∈ L :=
+  h.left_box.signs.1
+
+/-- The right endpoint of a forward pair comparison state is a member of the list. -/
+theorem SourcePressureForwardPairComparisonState.right_mem
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    W' ∈ L :=
+  h.right_box.signs.1
+
+/--
+Project the sign-and-target surface for the left endpoint of a forward pair
+comparison state.
+-/
+theorem SourcePressureForwardPairComparisonState.left_signs
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    W ∈ L ∧
+      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+        0 < SourcePressureMarginInt n k (r + W.val) ∧
+          SourcePressureBeamAddressedDepthTarget L W.val ∧
+            SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 :=
+  h.left_box.signs
+
+/--
+Project the sign-and-target surface for the right endpoint of a forward pair
+comparison state.
+-/
+theorem SourcePressureForwardPairComparisonState.right_signs
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    W' ∈ L ∧
+      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+        0 < SourcePressureMarginInt n k (r + W'.val) ∧
+          SourcePressureBeamAddressedDepthTarget L W'.val ∧
+            SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 :=
+  h.right_box.signs
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-265.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-265.md
new file mode 100644
index 00000000..854b6417
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-265.md
@@ -0,0 +1,103 @@
+# Report: petal-265
+
+## Goal
+
+Add caller-facing projections from
+`SourcePressureForwardPairComparisonState`.
+
+Target projections:
+
+```text
+FPC
+  -> left endpoint membership
+  -> right endpoint membership
+  -> left endpoint sign-and-target surface
+  -> right endpoint sign-and-target surface
+```
+
+## Implemented
+
+Added the following theorems in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+SourcePressureForwardPairComparisonState.left_mem
+SourcePressureForwardPairComparisonState.right_mem
+SourcePressureForwardPairComparisonState.left_signs
+SourcePressureForwardPairComparisonState.right_signs
+```
+
+The proofs are thin projections through the endpoint pulse boxes:
+
+```lean
+h.left_box.signs
+h.right_box.signs
+```
+
+## Meaning
+
+The forward pair-comparison state now exposes the immediate diagnostic payload
+that comparison callers need:
+
+```text
+FPC
+  -> left signs
+  -> right signs
+  -> W.val < W'.val
+  -> adjacent pair
+```
+
+This avoids making downstream pair-comparison lemmas manually unpack:
+
+```text
+FPC -> left_box/right_box -> SourcePressureBeamCenteredLocalPulseBox.signs
+```
+
+## Guardrails
+
+This checkpoint is projection-only.
+
+It does not assert:
+
+- propagation between endpoints;
+- endpoint uniqueness beyond already proved forward order;
+- overlap repair;
+- global coverage;
+- Collatz convergence.
+
+The pair-overlap obstruction branch remains separate.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+```
+
+The final gate for this checkpoint also runs:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next natural branch is to expose comparison-ready bundled signs:
+
+```lean
+theorem SourcePressureForwardPairComparisonState.endpoint_signs
+```
+
+or to move directly into the first comparison theorem:
+
+```text
+FPC
+  -> left center positive
+  -> right center positive
+  -> W.val < W'.val
+```
+
+The latter is likely more useful: it starts the actual pair-comparison layer
+while still relying only on explicit local witness data.
````
`````
