# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: c29f9e05343c808ee54a79626b0520c123d34918

## Report

Implemented and verified.

Added in [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1346):

`SourcePressureForwardPairComparisonState.left_next_interference_surface`

Added report:

[report-petal-276.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-276.md)

Verification passed:

- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`

What is now established as fact: for any `SourcePressureForwardPairComparisonState L W W'`, Lean can directly project the compact interference pattern:

```lean
0 < SourcePressureMarginInt n k (r + W.val) ∧
  SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
    0 < SourcePressureMarginInt n k (r + W'.val) ∧
      r + W.val + 1 < r + W'.val
```

So locally, the left center is positive, its immediate next index has already dropped to nonpositive, and the right positive center appears strictly later. This fixes the “no immediate successor contact” pattern in a caller-friendly form.

現在、任意の `SourcePressureForwardPairComparisonState L W W'` に対して、Leanにおいて以下のコンパクトな干渉パターンを直接導出できることが確立されています。

```lean
0 < SourcePressureMarginInt n k (r + W.val) ∧
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
0 < SourcePressureMarginInt n k (r + W'.val) ∧
r + W.val + 1 < r + W'.val
```

つまり局所的に見ると、左側の中心（正の値）があり、その直後のインデックスでは値が非正（0以下）に低下しており、右側の正の中心はそれよりも確実に後の位置に現れる、という構成になっています。これにより、「直後の要素との接触がない」というパターンが、呼び出し側にとって扱いやすい形で定式化されています。

## Review

## 判定

採用。
`FPC` から、左中心・左 next boundary・右中心をまとめた compact interference surface が取れるようになった。

追加：

```lean id="q9bqtc"
SourcePressureForwardPairComparisonState.left_next_interference_surface
```

内容はこれ。

```lean id="g00yg6"
0 < SourcePressureMarginInt n k (r + W.val) ∧
  SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
    0 < SourcePressureMarginInt n k (r + W'.val) ∧
      r + W.val + 1 < r + W'.val
```

`indexed_boundary_gap_surface` から必要成分だけを抜く projection として、よく整理されている。

## 増えた事実

これで `FPC` は、かなり短くこう読める。

```text id="c36f8r"
left center > 0
left next boundary <= 0
left next boundary < right center
right center > 0
```

つまり、左正中心の直後でいったん非正に落ち、その後に右正中心が現れる。
これは「隣接できない」という結果を、後段がそのまま使える形にしたものじゃ。

## 現在の状態表

```text id="qotmho"
SortedFailure + sorted(L)
  -> FPC ∨ PO

FailureResolution + sorted(L)
  -> FPC ∨ PO

BeamSeed + sorted(L)
  -> FPC ∨ PO

FPC
  -> indexed_boundary_gap_surface
  -> left_next_interference_surface
```

`FPC` の local interference API は、かなり呼びやすくなった。

## 次に攻める定理

次は、左 next boundary と右 previous boundary の位置関係を固定するとよい。

すでに

```lean id="zqjsr3"
W.val + 1 < W'.val
```

があるので、自然に

```lean id="ophq31"
r + W.val + 1 ≤ r + (W'.val - 1)
```

が出るはず。

これは重要。
なぜなら、左 pulse の `next <= 0` と右 pulse の `previous <= 0` のあいだに、同じ boundary を共有するか、あるいは gap corridor があるかを読む入口になるからじゃ。

## Codex 指示

```text id="d18oxq"
Goal:
  Relate the left next boundary to the right previous boundary in a forward pair
  comparison state.

Add in PressureState.lean:

  theorem SourcePressureForwardPairComparisonState.left_next_boundary_le_right_previous_boundary
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      r + W.val + 1 ≤ r + (W'.val - 1)

Use:
  h.left_succ_lt_right_val
  omega

Optionally add the sign-bundled projection:

  theorem SourcePressureForwardPairComparisonState.boundary_corridor_surface
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W') :
      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
        SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
          r + W.val + 1 ≤ r + (W'.val - 1)

Use:
  h.indexed_boundary_gap_surface
  h.left_next_boundary_le_right_previous_boundary

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

次で、二つの正中心の間にある非正 boundary corridor が見える。

```text id="8vgn9n"
left center > 0
left next <= 0
left next <= right previous
right previous <= 0
right center > 0
```

ここまで来ると、`FPC` は「二つの正 pulse が、非正 corridor を挟んで並ぶ」という形になる。これは window separation 層へのかなり良い入口じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 8bdb83b3..4d7044d0 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1336,6 +1336,26 @@ theorem SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_b
     ⟨_, _, hnextL, _, _, _, _, _, hgap⟩
   exact ⟨hnextL, hgap⟩

+/--
+Compact left-next interference surface for local window comparison.
+
+It records the left positive center, the immediate nonpositive boundary after
+that center, the right positive center, and the strict index gap from the left
+next boundary to the right center.
+-/
+theorem SourcePressureForwardPairComparisonState.left_next_interference_surface
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    0 < SourcePressureMarginInt n k (r + W.val) ∧
+      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+        0 < SourcePressureMarginInt n k (r + W'.val) ∧
+          r + W.val + 1 < r + W'.val := by
+  rcases h.indexed_boundary_gap_surface with
+    ⟨_, hcenterL, hnextL, _, hcenterR, _, _, _, hgap⟩
+  exact ⟨hcenterL, hnextL, hcenterR, hgap⟩
+
 /--
 Constructor from the forward box comparison state to the pair-comparison-facing
 state.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-276.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-276.md
new file mode 100644
index 00000000..1bdfbbf0
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-276.md
@@ -0,0 +1,77 @@
+# Report: petal-276
+
+## Goal
+
+Add a compact left-next interference surface for the next local
+window-comparison layer.
+
+## Implemented
+
+Added:
+
+- `SourcePressureForwardPairComparisonState.left_next_interference_surface`
+
+This theorem projects from:
+
+- `SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface`
+
+## Established Fact
+
+For any concrete forward pair comparison state
+
+```lean
+h : SourcePressureForwardPairComparisonState L W W'
+```
+
+Lean now exposes the compact surface:
+
+```lean
+0 < SourcePressureMarginInt n k (r + W.val)
+  ∧ SourcePressureMarginInt n k (r + W.val + 1) <= 0
+  ∧ 0 < SourcePressureMarginInt n k (r + W'.val)
+  ∧ r + W.val + 1 < r + W'.val
+```
+
+## What Can Be Concluded
+
+This fixes a reusable local interference pattern:
+
+- the left center is positive;
+- the immediate next index after the left center is nonpositive;
+- the right center is positive;
+- the left next index is strictly before the right center.
+
+Thus a forward pair comparison cannot place the right positive center at the
+left center's immediate successor.  The local window has already dropped to a
+nonpositive boundary before the right positive center appears.
+
+## Guardrails
+
+This is still a local theorem for an explicit forward pair comparison state.
+It does not assert global coverage, global uniqueness of positive centers,
+arbitrary window disjointness, or Collatz termination.
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
+Final whitespace gate:
+
+```text
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next natural layer can either:
+
+- name a dedicated left-next interference predicate, or
+- add symmetric right-side projections if a caller starts needing them.
+
+For now this compact theorem is probably enough for downstream local
+window-comparison proofs.
````
`````
