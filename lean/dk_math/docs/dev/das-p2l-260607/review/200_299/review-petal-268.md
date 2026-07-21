# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 8ef4983d8879d22c6b0cf72056811e1f692c9cff

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1114) に `SourcePressureForwardPairComparisonState.boundary_sign_pair_surface` を追加しました。

これで `FPC` から、左右 2 点の局所 pulse 符号をまとめて取れます。

```text
left previous <= 0
left center > 0
left next <= 0
right previous <= 0
right center > 0
right next <= 0
W.val < W'.val
```

レポートは [report-petal-268.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-268.md:1) に追加済みです。

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
`FPC` から左右 2 点の boundary sign surface が一発で取れるようになった。

追加：

```lean
theorem SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
```

内容は狙い通り。

```text
left previous <= 0
left center   > 0
left next     <= 0

right previous <= 0
right center   > 0
right next     <= 0

W.val < W'.val
```

`h.left_signs`, `h.right_signs`, `h.val_lt` を束ねる薄い theorem としてきれいに閉じている。

## 増えた事実

`ForwardPairComparisonState` は、左右の局所 pulse が順序付きで並ぶ状態として読めるようになった。

```text
FPC
  -> left local pulse boundary signs
  -> right local pulse boundary signs
  -> W.val < W'.val
```

これで pair-comparison 層は、中心正性だけでなく、左右の前後境界も同時に扱える。

## 現在の状態表

```text
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> center_pair_surface
  -> boundary_sign_pair_surface
```

かなり整った。
正向き branch はもう「二つの正中心が順序付きで並び、それぞれ前後が非正」という局所 pulse pair になっている。

## 次に攻める定理

次は `boundary_sign_pair_surface` から、左右 center の非隣接・分離を読む。

すぐ狙える小補題はこれ。

```lean
theorem SourcePressureForwardPairComparisonState.centers_distinct
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val ≠ r + W'.val
```

証明は `W.val < W'.val` から `omega` でよいはず。

さらに使いやすい形：

```lean
theorem SourcePressureForwardPairComparisonState.center_index_lt
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val < r + W'.val
```

これが先にあると、margin index 比較に使いやすい。

## Codex 指示

```text
Goal:
  Add index-level center order consequences from
  SourcePressureForwardPairComparisonState.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.center_index_lt
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      r + W.val < r + W'.val

  theorem SourcePressureForwardPairComparisonState.center_index_ne
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      r + W.val ≠ r + W'.val

Use:
  h.val_lt
  omega

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `FPC` は index 比較まで降りる。

```text
FPC
  -> W.val < W'.val
  -> r + W.val < r + W'.val
  -> center indices are distinct
```

その後、左右 boundary sign と center index order を組み合わせて、positive center の並び・分離・干渉を読む補題へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index c8f1d7a4..4ee70e8f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1104,6 +1104,29 @@ theorem SourcePressureForwardPairComparisonState.center_pair_surface
   rcases h.center_targets_pair with ⟨htargetL, htargetR, _hlt'⟩
   exact ⟨hposL, hposR, htargetL, htargetR, hlt⟩

+/--
+Boundary-sign pair surface for the forward pair branch.
+
+Both endpoints are local pulses with nonpositive neighboring margins and a
+positive center margin, and the left endpoint is strictly before the right
+endpoint in value order.
+-/
+theorem SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
+      0 < SourcePressureMarginInt n k (r + W.val) ∧
+        SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+          SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+            0 < SourcePressureMarginInt n k (r + W'.val) ∧
+              SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
+                W.val < W'.val := by
+  rcases h.left_signs with ⟨_, hprevL, hcenterL, _, hnextL⟩
+  rcases h.right_signs with ⟨_, hprevR, hcenterR, _, hnextR⟩
+  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, h.val_lt⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-268.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-268.md
new file mode 100644
index 00000000..4bb629df
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-268.md
@@ -0,0 +1,95 @@
+# Report: petal-268
+
+## Goal
+
+Add the boundary-sign pair surface for
+`SourcePressureForwardPairComparisonState`.
+
+Target surface:
+
+```text
+FPC
+  -> left local pulse signs
+  -> right local pulse signs
+  -> left center before right center
+```
+
+## Implemented
+
+Added the following theorem in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+```lean
+SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
+```
+
+The proof uses:
+
+```lean
+h.left_signs
+h.right_signs
+h.val_lt
+```
+
+## Meaning
+
+The forward pair-comparison branch now exposes both endpoints as ordered local
+pulses:
+
+```text
+left previous <= 0
+left center > 0
+left next <= 0
+right previous <= 0
+right center > 0
+right next <= 0
+W.val < W'.val
+```
+
+This complements `center_pair_surface`.  The center theorem gives the compact
+positive-center/target payload; this theorem gives the surrounding boundary
+signs needed for pulse-shape comparison.
+
+## Guardrails
+
+This checkpoint is local to the explicit `FPC` pair.
+
+It does not assert:
+
+- uniqueness of local pulses;
+- absence of other positive centers;
+- global non-overlap;
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
+The next natural branch is to make a full pulse-pair surface that combines:
+
+```text
+boundary_sign_pair_surface
+center_pair_surface
+adjacentPair
+```
+
+However, this may be redundant unless a caller needs all three at once.  A more
+useful next step may be the first theorem that compares the two local pulse
+windows using the boundary signs and strict value order.
````
`````
