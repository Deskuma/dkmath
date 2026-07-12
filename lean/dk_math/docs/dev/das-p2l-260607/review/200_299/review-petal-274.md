# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 918b43ec00865d05db0d310c15e2bc5a8049a30b

## Report

Implemented and verified.

Added in [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1290):

`SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface`

Also added the checkpoint report:

[report-petal-274.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-274.md)

Verification passed:

- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`

What is now established as fact: in any `SourcePressureForwardPairComparisonState L W W'`, both local pulse windows carry their boundary sign pattern, the center indices are strictly ordered and distinct, and additionally the left center’s next boundary index is still strictly before the right center:

```lean
r + W.val + 1 < r + W'.val
```

So this is stronger than “the centers differ”: it rules out immediate contact at the index layer. It remains a local explicit-pair theorem, not a global coverage or Collatz convergence claim.

現在、事実として確立されていることは、任意の `SourcePressureForwardPairComparisonState L W W'` において、両方の局所パルスウィンドウがそれぞれの境界符号パターンを保持しており、中心インデックスは厳密に順序付けられかつ互いに異なり、さらに左側の中心の次の境界インデックスが依然として右側の中心よりも厳密に手前にある、ということです。

```lean
r + W.val + 1 < r + W'.val
```

したがって、これは「中心が異なる」よりも強力です。つまり、インデックス層での直接の接触が除外されます。これはローカルな明示的ペア定理のままであり、グローバルな範囲やコラッツの収束主張ではありません。

## Review

## 判定

採用。
`indexed_boundary_separation_surface` に、第一干渉定理由来の index-level gap が統合された。

追加：

```lean id="puz0av"
SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface
```

これで `FPC` から一発で、

```text id="n49ivz"
left boundary signs
right boundary signs
r + W.val < r + W'.val
r + W.val ≠ r + W'.val
r + W.val + 1 < r + W'.val
```

が取れる。`indexed_boundary_separation_surface` と `left_next_index_lt_right_center_index` を束ねるだけの薄い theorem だが、次段 caller にはかなり効く形じゃ。

## 増えた事実

今回で、局所 pulse pair の読みはここまで強くなった。

```text id="m7x0og"
FPC
  -> left previous <= 0
  -> left center   > 0
  -> left next     <= 0

  -> right previous <= 0
  -> right center   > 0
  -> right next     <= 0

  -> left center index < right center index
  -> left center index ≠ right center index
  -> left next boundary index < right center index
```

特に最後の

```lean id="fv4c4k"
r + W.val + 1 < r + W'.val
```

が重要。
これは「中心が違う」だけではなく、**左中心の次境界すら、右中心より手前にある**ことを示す。

## 現在の状態表

```text id="lhwkes"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> indexed_boundary_gap_surface
```

これで `FPC` の caller-facing surface はかなり完成度が高い。

## 数学的意味

これは `FPC` branch における **即時接触の排除** じゃ。

以前は、

```text id="i3memi"
二つの正中心は異なる
```

だった。

いまは、

```text id="q163kz"
左中心
左 next boundary
gap
右中心
```

という順序が Lean で固定された。

つまり、正中心どうしが隣接して潰れることはなく、少なくとも左の `next <= 0` boundary を越えた先に右の正中心が現れる。

## 次に攻める定理

次は、この長い surface から、よく使う最後の inequality を短名 projection として出すとよい。

```lean id="qi8ej8"
theorem SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    r + W.val + 1 < r + W'.val
```

中身は既に `left_next_index_lt_right_center_index` と同じなので、alias 的 theorem になる。
ただし命名が意味を持つ。後段の干渉・window separation ではこちらの名前の方が読みやすい。

さらに、boundary context 付き projection もよい。

```lean id="h14w7z"
theorem SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_before_right_center
```

これは、

```text id="nk4bcb"
left next <= 0
left next boundary < right center
```

を同時に返す。

## Codex 指示

```text id="ze2sh5"
Goal:
  Add compact projections from indexed_boundary_gap_surface for the next
  window-interference layer.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      r + W.val + 1 < r + W'.val

  theorem SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_before_right_center
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
        r + W.val + 1 < r + W'.val

Use:
  h.indexed_boundary_gap_surface

Proof shape:
  rcases h.indexed_boundary_gap_surface with
    ⟨_, _, hnextL, _, _, _, _, _, hgap⟩
  exact ...

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で、

```text id="nuxf89"
left next boundary:
  nonpositive
  strictly before right center
```

が短く呼べるようになる。

その後は、`right previous boundary` との位置関係へ進める。
ここから **left next boundary と right previous boundary の間にある gap / contact / window separation** を読む段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 3143d18c..02c0eaac 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1279,6 +1279,33 @@ theorem SourcePressureForwardPairComparisonState.left_next_boundary_lt_right_cen
   have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
   omega
 
+/--
+Boundary-sign pair surface bundled with the first interference gap.
+
+This strengthens `indexed_boundary_separation_surface` by adding the fact that
+the left endpoint's next boundary index is still strictly before the right
+positive center.  It is a local pair-comparison statement, not a global
+coverage or uniqueness claim.
+-/
+theorem SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface
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
+                r + W.val < r + W'.val ∧
+                  r + W.val ≠ r + W'.val ∧
+                    r + W.val + 1 < r + W'.val := by
+  rcases h.indexed_boundary_separation_surface with
+    ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, hlt, hne⟩
+  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR,
+    hlt, hne, h.left_next_index_lt_right_center_index⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-274.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-274.md
new file mode 100644
index 00000000..30020072
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-274.md
@@ -0,0 +1,101 @@
+# Report: petal-274
+
+## Goal
+
+Bundle the boundary sign surface with the index-level gap produced by the first
+interference theorem.
+
+## Implemented
+
+Added:
+
+- `SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface`
+
+This theorem combines:
+
+- `SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface`
+- `SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index`
+
+## Established Fact
+
+For any concrete forward pair comparison state
+
+```lean
+h : SourcePressureForwardPairComparisonState L W W'
+```
+
+Lean now proves the combined local surface:
+
+```lean
+SourcePressureMarginInt n k (r + (W.val - 1)) <= 0
+0 < SourcePressureMarginInt n k (r + W.val)
+SourcePressureMarginInt n k (r + W.val + 1) <= 0
+SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
+0 < SourcePressureMarginInt n k (r + W'.val)
+SourcePressureMarginInt n k (r + W'.val + 1) <= 0
+r + W.val < r + W'.val
+r + W.val != r + W'.val
+r + W.val + 1 < r + W'.val
+```
+
+The new piece is the final inequality:
+
+```lean
+r + W.val + 1 < r + W'.val
+```
+
+so downstream callers can use the left next boundary and the right positive
+center separation without rebuilding the first interference theorem.
+
+## What Can Be Concluded
+
+In a `SourcePressureForwardPairComparisonState`, the two local pulse windows
+carry their usual boundary sign pattern, and the right positive center is
+strictly beyond the left center's next boundary index.
+
+This is stronger than merely saying the center indices are distinct.  It says
+that the immediate successor index of the left center is still strictly before
+the right center.
+
+## Guardrails
+
+This remains a local theorem about an explicit forward pair comparison state.
+It does not prove:
+
+- global uniqueness of positive centers;
+- global coverage of all witness candidates;
+- complete non-overlap of arbitrary windows;
+- Collatz termination or convergence.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+```
+
+The final whitespace gate is:
+
+```text
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next useful theorem is probably a compact projection from
+`indexed_boundary_gap_surface`, for example:
+
+```lean
+SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center
+```
+
+or a pair-window interference surface that names the fact:
+
+```text
+left next boundary < right center
+```
+
+as a reusable obstruction against immediate contact between two forward pulse
+centers.
````
`````
