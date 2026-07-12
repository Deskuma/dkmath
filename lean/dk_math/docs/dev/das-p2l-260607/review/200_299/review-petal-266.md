# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 00710562cd387171099a23f48d69203cfeff5a0a

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1052) に、FPC から直接読める比較補題を 2 本追加しました。

- `SourcePressureForwardPairComparisonState.center_pos_pair`
- `SourcePressureForwardPairComparisonState.center_targets_pair`

これで `FPC` から、左右 center の正性、左右 addressed target、そして `W.val < W'.val` が直接取れます。レポートは [report-petal-266.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-266.md:1) に追加済みです。

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
`ForwardPairComparisonState` から、左右 center の比較 surface が直接取れるようになった。

追加：

```lean id="tmlvdv"
SourcePressureForwardPairComparisonState.center_pos_pair
SourcePressureForwardPairComparisonState.center_targets_pair
```

これで `FPC` から、

```text id="h4joar"
left center positive
right center positive
left addressed target
right addressed target
W.val < W'.val
```

が直に取れる。`h.left_signs`, `h.right_signs`, `h.val_lt` を束ねる薄い theorem として良い。

## 増えた事実

`FPC` は、もはや単なる projection 集合ではなく、**左右の正中心が順序付きで並ぶ状態**として読める。

```text id="bw8zlv"
FPC
  -> 0 < margin(r + W.val)
  -> 0 < margin(r + W'.val)
  -> target(W.val)
  -> target(W'.val)
  -> W.val < W'.val
```

これは pair-comparison 層の最初の実体じゃ。

## 現在の状態表

```text id="3dy7m4"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> left/right center positive
  -> left/right addressed targets
  -> W.val < W'.val
```

ここまでで、正向き branch はかなり読みやすくなった。

## 次に攻める定理

次は二つをまとめた caller-facing theorem を置くとよい。

```lean id="btls4e"
theorem SourcePressureForwardPairComparisonState.center_pair_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    0 < SourcePressureMarginInt n k (r + W.val) ∧
      0 < SourcePressureMarginInt n k (r + W'.val) ∧
        SourcePressureBeamAddressedDepthTarget L W.val ∧
          SourcePressureBeamAddressedDepthTarget L W'.val ∧
            W.val < W'.val
```

これは `center_pos_pair` と `center_targets_pair` の合成で通る。

## Codex 指示

```text id="dzs2xm"
Goal:
  Bundle the two FPC center comparison facts into one caller-facing theorem.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.center_pair_surface
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        0 < SourcePressureMarginInt n k (r + W'.val) ∧
          SourcePressureBeamAddressedDepthTarget L W.val ∧
            SourcePressureBeamAddressedDepthTarget L W'.val ∧
              W.val < W'.val

Use:
  h.center_pos_pair
  h.center_targets_pair

Proof shape:
  rcases h.center_pos_pair with ⟨hposL, hposR, hlt⟩
  rcases h.center_targets_pair with ⟨htargetL, htargetR, _hlt'⟩
  exact ⟨hposL, hposR, htargetL, htargetR, hlt⟩

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `FPC` は一発でこう読める。

```text id="71m5up"
FPC
  -> two positive centers
  -> two addressed targets
  -> strict ordered centers
```

その後は左右の boundary sign を使って、

```text id="x6uth4"
previous <= 0
center > 0
next <= 0
```

を二点で比較する段階へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 4d639001..350af6d6 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1045,6 +1045,43 @@ theorem SourcePressureForwardPairComparisonState.right_signs
             SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 :=
   h.right_box.signs
 
+/--
+Both endpoint centers of a forward pair comparison state are positive, and the
+left endpoint is strictly before the right endpoint in value order.
+-/
+theorem SourcePressureForwardPairComparisonState.center_pos_pair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    0 < SourcePressureMarginInt n k (r + W.val) ∧
+      0 < SourcePressureMarginInt n k (r + W'.val) ∧
+        W.val < W'.val := by
+  rcases h.left_signs with
+    ⟨_hmemL, _hprevL, hcenterL, _htargetL, _hnextL⟩
+  rcases h.right_signs with
+    ⟨_hmemR, _hprevR, hcenterR, _htargetR, _hnextR⟩
+  exact ⟨hcenterL, hcenterR, h.val_lt⟩
+
+/--
+Both endpoint centers of a forward pair comparison state are addressed beam
+targets, and the left endpoint is strictly before the right endpoint in value
+order.
+-/
+theorem SourcePressureForwardPairComparisonState.center_targets_pair
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureBeamAddressedDepthTarget L W.val ∧
+      SourcePressureBeamAddressedDepthTarget L W'.val ∧
+        W.val < W'.val := by
+  rcases h.left_signs with
+    ⟨_hmemL, _hprevL, _hcenterL, htargetL, _hnextL⟩
+  rcases h.right_signs with
+    ⟨_hmemR, _hprevR, _hcenterR, htargetR, _hnextR⟩
+  exact ⟨htargetL, htargetR, h.val_lt⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-266.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-266.md
new file mode 100644
index 00000000..8ed9fd9b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-266.md
@@ -0,0 +1,104 @@
+# Report: petal-266
+
+## Goal
+
+Add the first actual pair-comparison facts from
+`SourcePressureForwardPairComparisonState`.
+
+Target surface:
+
+```text
+FPC
+  -> left center positive
+  -> right center positive
+  -> both addressed targets
+  -> W.val < W'.val
+```
+
+## Implemented
+
+Added the following theorems in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+SourcePressureForwardPairComparisonState.center_pos_pair
+SourcePressureForwardPairComparisonState.center_targets_pair
+```
+
+The proofs use:
+
+```lean
+h.left_signs
+h.right_signs
+h.val_lt
+```
+
+## Meaning
+
+The forward pair-comparison state now has its first direct comparison facts.
+
+The two endpoints are not merely boxed and adjacent.  The forward branch now
+explicitly exposes:
+
+- the left center margin is positive;
+- the right center margin is positive;
+- the left endpoint is an addressed beam target;
+- the right endpoint is an addressed beam target;
+- the left endpoint value is strictly before the right endpoint value.
+
+This is the first real pair-comparison surface.  It turns the previous
+projection layer into a compact theorem interface for comparing the two
+positive centers.
+
+## Guardrails
+
+This checkpoint remains local to the explicit `FPC` witness pair.
+
+It does not assert:
+
+- propagation from one endpoint to the other;
+- uniqueness of positive centers;
+- absence of all other centers;
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
+The next natural branch is to bundle the two comparison facts into a single
+caller-facing theorem if downstream proofs repeatedly need both:
+
+```lean
+theorem SourcePressureForwardPairComparisonState.center_pair_surface
+```
+
+Candidate payload:
+
+```text
+0 < margin(W.center)
+0 < margin(W'.center)
+Target(W.val)
+Target(W'.val)
+W.val < W'.val
+```
+
+If callers need finer control, keep the current two-theorem surface and proceed
+directly to comparing the left/right pulse boxes by their signed boundary
+patterns.
````
`````
