# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 6de91e8429daeaa83b458bc1d3b7aaed77cab649

## Report

実装しました。

追加した theorem:

- [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1260) `SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index`
- [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1273) `SourcePressureForwardPairComparisonState.left_next_boundary_lt_right_center_index`

結果レポート:

- [report-petal-273.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-273.md)

確認:

- `lake build DkMath.Collatz.PetalBridge.PressureState` passed
- `lake build DkMath.Collatz.PetalBridge` passed
- `git diff --check` passed

結論として確定できる事実は、`SourcePressureForwardPairComparisonState L W W'` の下では、右中心 index `r + W'.val` は左中心の次境界 `r + W.val + 1` より真に右にある、ということです。つまり、この局所 forward pair では「隣接中心」は排除され、margin-index 層でも少なくとも 1 つ分の分離が Lean により固定されました。

ただし、これは明確に局所 theorem です。全体被覆、正中心の大域一意性、Collatz 収束までは主張していません。

## Review

## 判定

採用。
`FPC` の value-level interference が、margin-index 層へ持ち上がった。

追加：

```lean
SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index
SourcePressureForwardPairComparisonState.left_next_boundary_lt_right_center_index
```

これで `SourcePressureForwardPairComparisonState L W W'` から、

```text
r + W.val + 1 < r + W'.val
r + (W.val + 1) < r + W'.val
```

が直接取れる。`left_succ_lt_right_val` を `omega` で index 化する薄い補題として、ちょうどよい。

## 増えた事実

前 checkpoint では、

```text
W.val + 1 < W'.val
```

今回で、

```text
r + W.val + 1 < r + W'.val
```

まで落ちた。

つまり、margin-index 言語で、

```text
left next boundary < right center
```

が言えるようになった。

これは `SourcePressureMarginInt` を直接扱う次段にかなり効く。

## 現在の状態表

```text
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> boundary signs
  -> center index order
  -> center index separation
  -> left next boundary < right center
```

`FPC` は、単なる二中心比較ではなく、左 pulse window の次境界を越えて右中心が現れる状態になった。

## 次に攻める定理

次は report 予測どおり、boundary sign surface と index-level gap を束ねる。

```lean
theorem SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W') :
    SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + W.val) ∧
        SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
          SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
            0 < SourcePressureMarginInt n k (r + W'.val) ∧
              SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
                r + W.val < r + W'.val ∧
                  r + W.val ≠ r + W'.val ∧
                    r + W.val + 1 < r + W'.val
```

これは `indexed_boundary_separation_surface` に `left_next_index_lt_right_center_index` を足すだけ。

## Codex 指示

```text
Goal:
  Bundle the boundary sign surface with the index-level gap produced by the
  first interference theorem.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + W.val) ∧
          SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
            SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
              0 < SourcePressureMarginInt n k (r + W'.val) ∧
                SourcePressureMarginInt n k (r + W'.val + 1) ≤ 0 ∧
                  r + W.val < r + W'.val ∧
                    r + W.val ≠ r + W'.val ∧
                      r + W.val + 1 < r + W'.val

Use:
  h.indexed_boundary_separation_surface
  h.left_next_index_lt_right_center_index

Proof shape:
  rcases h.indexed_boundary_separation_surface with
    ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR, hlt, hne⟩
  exact ⟨hprevL, hcenterL, hnextL, hprevR, hcenterR, hnextR,
    hlt, hne, h.left_next_index_lt_right_center_index⟩

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で `FPC` は一発でこう読める。

```text
left pulse signs
right pulse signs
left center < right center
left center ≠ right center
left next boundary < right center
```

その後は、`right previous boundary` と `left next boundary` の間の関係を見る。ここから pulse window の分離面がさらに鋭くなる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index f80a22c7..3143d18c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1251,6 +1251,34 @@ theorem SourcePressureForwardPairComparisonState.left_succ_lt_right_val
   have hne : W'.val ≠ W.val + 1 := h.not_right_val_eq_left_succ
   omega
 
+/--
+Index-level form of the first interference theorem.
+
+The right positive center lies strictly beyond the left center's next boundary
+index.  This is the margin-index version of `left_succ_lt_right_val`.
+-/
+theorem SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    r + W.val + 1 < r + W'.val := by
+  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
+  omega
+
+/--
+Syntactic variant of `left_next_index_lt_right_center_index` using
+`r + (W.val + 1)` as the left boundary expression.
+-/
+theorem SourcePressureForwardPairComparisonState.left_next_boundary_lt_right_center_index
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    r + (W.val + 1) < r + W'.val := by
+  have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
+  omega
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-273.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-273.md
new file mode 100644
index 00000000..a1f94932
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-273.md
@@ -0,0 +1,100 @@
+# Report: petal-273
+
+## Goal
+
+Add the index-level form of the first interference theorem for
+`SourcePressureForwardPairComparisonState`.
+
+## Implemented
+
+Added two caller-facing theorems in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+- `SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index`
+- `SourcePressureForwardPairComparisonState.left_next_boundary_lt_right_center_index`
+
+Both are direct index-level consequences of the established value-level theorem:
+
+- `SourcePressureForwardPairComparisonState.left_succ_lt_right_val`
+
+The proof is intentionally thin:
+
+```lean
+have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
+omega
+```
+
+## Established Fact
+
+For any forward pair comparison state `h : SourcePressureForwardPairComparisonState L W W'`,
+Lean now proves:
+
+```lean
+r + W.val + 1 < r + W'.val
+```
+
+and the syntactic variant:
+
+```lean
+r + (W.val + 1) < r + W'.val
+```
+
+This means the right positive center is strictly beyond the left center's next
+boundary index.  The previous checkpoint proved this at the witness-value level;
+this checkpoint fixes the same fact at the exact index layer used by
+`SourcePressureMarginInt`.
+
+## What This Rules Out
+
+Within a concrete `SourcePressureForwardPairComparisonState`:
+
+- the right center cannot be equal to the successor of the left center;
+- the left center's next index is strictly before the right center index;
+- the two local pulse centers are separated by at least one index-level gap.
+
+## Guardrails
+
+This is a local theorem about an explicit forward pair comparison state.
+It does not claim:
+
+- global uniqueness of positive centers;
+- global coverage of all candidate addresses;
+- full non-overlap of complete windows beyond the proved boundary-center inequality;
+- Collatz convergence or termination.
+
+The result is a stable local interference fact suitable for the next comparison
+layer.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+```
+
+The broader gate for this checkpoint is:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next useful branch is to bundle this index-level separation with the already
+available boundary sign surface:
+
+```lean
+SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface
+```
+
+That would give downstream callers a single theorem containing:
+
+- left boundary signs;
+- right boundary signs;
+- strict center-index separation;
+- strict left-next-boundary-before-right-center separation.
+
+This should help the pair-comparison layer reason about local pulse interference
+without repeatedly reconstructing the same `omega` step.
````
`````
