# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 4d0d588bc6d7dada24d3f3c8d28aa09b66878df6

## Report

Checkpoint 129 を実装しました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean#L916) に first-failed-depth sequence の `get?/take` API を追加し、`height + 1` として読める補題も入れました。さらに [orbitWindow_threeProfiles_get?_eq_some](/lean/dk_math/DkMath/Collatz/PetalBridge.lean#L978) を追加して、`height / residual shape / first failed depth` の三つの time profile を同じ index で並べて読めるようにしました。

Docs は README、Guide、Status、128 doc を同期し、新規に [Collatz-FirstFailedDepthSequence-129.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-FirstFailedDepthSequence-129.md#L1) と [report-petal-129.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-129.md#L1) を作成しました。次は Route A がほぼ閉じたので、pressure sign-pattern scan に戻る判断を書いてあります。

検証:
`lake build DkMath.Collatz.PetalBridge` passed
`lake build DkMath.Collatz.Collatz2K26` passed
対象 Collatz 2ファイルの `sorry` scan はヒットなし
`git diff --check` passed
既存の unrelated warning として `ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告は継続しています。

## Review

## 状況分析

うむ。Checkpoint `129` で、Route A はかなり綺麗に小閉じしたと見てよい。

今回の主成果は、`orbitWindowFirstFailedPow2DepthSeq` に `get? / take` API が追加され、さらに `height + 1` として読める補題も入ったことじゃ。加えて `orbitWindow_threeProfiles_get?_eq_some` により、`height / residual shape / first failed depth` の三つの time profile を、同じ index `i` で並べて取得できるようになった。検証も `PetalBridge` / `Collatz2K26` build、no-sorry scan、diff check が通っている。

これで現在の time profile は、かなり安定した。

```text
orbitWindowHeightSeq
orbitWindowResidualShapeSeq
orbitWindowFirstFailedPow2DepthSeq
```

この三つが、同じ有限窓 `k` の上で並列に扱える。
つまり、Route A の「奇数グノモン補正 → 2進整列評価 → residual shape 抽出 → first failed depth」の一次元観測 API は、ひとまず揃った。

## レビュー

## 良い点

一番良いのは、`orbitWindow_threeProfiles_get?_eq_some` じゃ。

これは単なる便利補題ではなく、次の二次元化に入る前の「時間軸の整列」を保証している。

```text
time index i:
  height_i
  residual_i
  first_failed_i
```

これらが同じ `i` で取れる。
つまり、後で pressure depth `j` と組み合わせるときに、時間軸側のデータ取り出しで迷わなくなる。

次に良いのは、`first_failed_i = height_i + 1` が list indexing でも使えるようになったことじゃ。

```text
height_i:
  完全に 2^height_i へ整列できた深さ

first_failed_i:
  初めて整列に失敗する深さ
```

この関係が、点wise だけでなく list API からも取れる。
これは「2進評価でどこまで見え、どこから残差形状が露出するか」を解析する上で大事になる。

また、今回のドキュメントで「次は pressure sign-pattern scan」と明記されているのも良い。
これ以上 Route A の API を細かく増やすより、次は観測で `time profile` と `depth profile` の相関を見る段階じゃ。

## 注意点

ここから先で一番危ないのは、`i` と `j` を混ぜること。

```text
i:
  軌道時間 index

j:
  pressure depth index
```

この二つは別軸じゃ。

`height_i` や `residual_i` は時間方向の値。
`margin(j)` や `frontier(j)` は深さ方向の値。

したがって、次の段階では

```text
ShapePressureGrid:
  time i × depth j
```

という二次元観測を意識する必要がある。

まだ Lean で巨大な `ShapePressureGrid` を定義するのは早い。
まず Python summary scan で、`i` 側の特徴と `j` 側の sign pattern に相関があるかを見るのが正しい。

## 解説

ここまでの Route A を振り返ると、次の流れが Lean 上で固定された。

```text
label_i
  -> RawGnomonStep(label_i)
  -> height_i
  -> residual_i
  -> label_{i+1}
```

さらに、

```text
first_failed_i = height_i + 1
```

も取れる。

この意味はこうじゃ。

`label_i` は現在の奇数残差形状。
そこへ奇数グノモン層を足して raw 値を作る。
その raw 値がどこまで \(2^h\) に整列するかを `height_i` で評価する。
整列分を取り除いた残りが `residual_i`。
その `residual_i` が次の `label_{i+1}` になる。
そして `height_i + 1` は、最初に整列が破れる深さじゃ。

ここで初めて、コラッツ軌道は単なる数列ではなく、

```text
形状補正
評価
残差抽出
次形状化
```

の有限力学として扱えるようになった。

## 次の指示

次 checkpoint `130` は、Route B に戻るのが良い。

ただし、いきなり Lean predicate を増やすより、まずは **pressure sign-pattern scan** を行うべきじゃ。

## Checkpoint 130 推奨内容

### 1. Python summary scan を追加する

巨大 CSV は不要。
summary markdown を出す形でよい。

最低限、各 window について以下を出す。

```text
n
k
height_seq
residual_shape_seq
first_failed_depth_seq
residual_mod_8_seq
residual_mod_16_seq
residual_mod_32_seq
positive_depths
first_frontier_depth
local_islands
sign_change_up_positions
```

追加で見たいもの。

```text
positive_blocks
frontier_margin
first_failure_pair
margin_jump
retention_drop
continuation_drop
```

目的は、次の問いを見ること。

```text
height_seq と frontier depth に相関があるか

first_failed_depth_seq と local island に相関があるか

residual_shape mod 8/16/32 と positive pressure depth に偏りがあるか

positive depths は prefix 的か、block 的か、island 的か

sign-change-up は単発か、複数回出るか
```

### 2. Lean 側は重くしない

Lean 側でどうしても何か追加するなら、薄い predicate だけでよい。

```lean
def SourcePressurePositiveBlock
    (n : OddNat) (k r a len : ℕ) : Prop :=
  0 < len ∧
    ∀ j, a ≤ j → j < a + len → IsSourcePressureDepth n k r j
```

ただし、これは「入れてもよい」程度。
本命は scan じゃ。

### 3. まだ入れないもの

```text
Real.log
log2(3)
unconditional pressure prefix theorem
heavy ShapePressureGrid
global island theorem
```

ここはまだ早い。

## 一歩先ゆく推論

いま見えている次の本命は、`ShapePressureGrid` じゃ。

ただし、これはいきなり定義するものではない。
まず観測から、どの軸が効いているかを見極める。

想定される構造はこう。

```text
time axis i:
  label_i
  height_i
  residual_i
  first_failed_i

depth axis j:
  margin_j
  selected_j
  frontier_j
  island_j
  sign_change_j
```

この二つを合わせると、

```text
time i の residual shape が、
depth j の margin sign にどう影響するか
```

を見ることになる。

もし相関が見えるなら、後で Lean にこういう薄い定義を置ける。

```lean
def ShapePressureCell
    (n : OddNat) (k r i j : ℕ) : Prop :=
  i < k ∧ IsSourcePressureDepth n k r j
```

ただし、これはまだ早い。
今は `Cell` を作るより、Python summary で「どの cell が意味を持つか」を見る段階じゃ。

## さらなる次の一手

Checkpoint `130` で pressure scan を行った後、Checkpoint `131` では scan 結果に応じて三方向がある。

### Route B1: positive block が多い場合

もし positive depths が連続 block を作りやすいなら、

```lean
def SourcePressurePositiveBlock
    (n : OddNat) (k r a len : ℕ) : Prop :=
  0 < len ∧
    ∀ j, a ≤ j → j < a + len → IsSourcePressureDepth n k r j
```

に進む。

次に margin 版を作る。

```lean
theorem sourcePressurePositiveBlock_iff_margin
    (n : OddNat) (k r a len : ℕ) :
    SourcePressurePositiveBlock n k r a len ↔
      0 < len ∧
        ∀ j, a ≤ j → j < a + len →
          0 < SourcePressureMarginInt n k (r + j) := by
  -- same pattern as existing margin equivalences
  sorry
```

### Route B2: local island が多い場合

すでに `SourcePressureLocalIsland` と `sourcePressureLocalIsland_iff_margin` がある。
この場合は、local island の統計を Lean 側へ寄せるより、まず `IslandCount` のような finite count を Python 側で観測するのが良い。

Lean 側では薄く、

```lean
def ExistsSourcePressureLocalIslandBelow
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∃ j, j < m ∧ SourcePressureLocalIsland n k r j
```

程度でよい。

### Route B3: frontier が安定する場合

もし `first_frontier_depth` に偏りがあるなら、`SourcePressureFrontier` を中心にする。

```lean
def SourcePressureFrontierBelow
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∃ j, j < m ∧ SourcePressureFrontier n k r j
```

これは軽い。

## 賢狼が試して欲しい実験補題

## 実験 A: Positive block predicate

```lean
def SourcePressurePositiveBlock
    (n : OddNat) (k r a len : ℕ) : Prop :=
  0 < len ∧
    ∀ j, a ≤ j → j < a + len → IsSourcePressureDepth n k r j
```

## 実験 B: Positive block margin equivalence

```lean
theorem sourcePressurePositiveBlock_iff_margin
    (n : OddNat) (k r a len : ℕ) :
    SourcePressurePositiveBlock n k r a len ↔
      0 < len ∧
        ∀ j, a ≤ j → j < a + len →
          0 < SourcePressureMarginInt n k (r + j) := by
  unfold SourcePressurePositiveBlock
  constructor
  · intro h
    constructor
    · exact h.1
    · intro j hle hlt
      exact (isSourcePressureDepth_iff_margin_pos n k r j).1
        (h.2 j hle hlt)
  · intro h
    constructor
    · exact h.1
    · intro j hle hlt
      exact (isSourcePressureDepth_iff_margin_pos n k r j).2
        (h.2 j hle hlt)
```

これは通る可能性が高い。

## 実験 C: Exists local island below

```lean
def ExistsSourcePressureLocalIslandBelow
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∃ j, j < m ∧ SourcePressureLocalIsland n k r j
```

margin 版。

```lean
theorem existsSourcePressureLocalIslandBelow_iff_margin
    (n : OddNat) (k r m : ℕ) :
    ExistsSourcePressureLocalIslandBelow n k r m ↔
      ∃ j, j < m ∧
        0 < j ∧
        0 < SourcePressureMarginInt n k (r + j) ∧
        SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
        SourcePressureMarginInt n k (r + (j + 1)) ≤ 0 := by
  unfold ExistsSourcePressureLocalIslandBelow
  constructor
  · intro h
    rcases h with ⟨j, hjm, hjisland⟩
    rw [sourcePressureLocalIsland_iff_margin] at hjisland
    exact ⟨j, hjm, hjisland⟩
  · intro h
    rcases h with ⟨j, hjm, hjmargin⟩
    rw [sourcePressureLocalIsland_iff_margin] at hjmargin
    exact ⟨j, hjm, hjmargin⟩
```

## 実験 D: Frontier below

```lean
def ExistsSourcePressureFrontierBelow
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∃ j, j < m ∧ SourcePressureFrontier n k r j
```

margin 版。

```lean
theorem existsSourcePressureFrontierBelow_iff_margin
    (n : OddNat) (k r m : ℕ) :
    ExistsSourcePressureFrontierBelow n k r m ↔
      ∃ j, j < m ∧
        0 < SourcePressureMarginInt n k (r + j) ∧
        ∀ i, i < j → SourcePressureMarginInt n k (r + i) ≤ 0 := by
  unfold ExistsSourcePressureFrontierBelow
  constructor
  · intro h
    rcases h with ⟨j, hjm, hfront⟩
    rw [sourcePressureFrontier_iff_margin] at hfront
    exact ⟨j, hjm, hfront⟩
  · intro h
    rcases h with ⟨j, hjm, hmargin⟩
    rw [sourcePressureFrontier_iff_margin] at hmargin
    exact ⟨j, hjm, hmargin⟩
```

## 実験 E: Python pressure scan summary schema

Codex に Python 側を頼むなら、出力は summary markdown でよい。

```text
# Pressure Sign Pattern Scan

## Parameters
n_max:
window_k:
base_r:
depth_range:

## Summary Counts
rows:
rows_with_positive_depth:
rows_with_frontier:
rows_with_local_island:
rows_with_positive_block:
rows_with_prefix_positive:
rows_with_prefix_failure:

## Distribution
first_frontier_depth_counts:
local_island_depth_counts:
positive_block_length_counts:
sign_change_up_counts:

## Correlation Hints
height_seq_vs_frontier:
first_failed_depth_seq_vs_frontier:
residual_mod_8_vs_frontier:
residual_mod_16_vs_island:
residual_mod_32_vs_positive_block:

## Examples
first_prefix_failure:
largest_margin_jump:
largest_retention_drop:
largest_continuation_drop:
first_local_island:
first_positive_block:
```

## Codex への次指示まとめ

```text
Checkpoint 130:
Route B pressure sign-pattern scan.

Primary goal:
  Do not add heavy Lean theory yet.
  Run/extend Python summaries to classify pressure sign patterns while carrying
  the three aligned time profiles:
    height_seq
    residual_shape_seq
    first_failed_depth_seq

Scan fields:
  positive_depths
  positive_blocks
  local_islands
  sign_change_up_positions
  first_frontier_depth
  frontier_margin
  first_failure_pair
  margin_jump
  retention_drop
  continuation_drop
  residual_mod_8/16/32 sequences

Lean optional:
  SourcePressurePositiveBlock
  sourcePressurePositiveBlock_iff_margin
  ExistsSourcePressureLocalIslandBelow
  ExistsSourcePressureFrontierBelow

Do not:
  introduce Real.log
  claim pressure prefix
  collapse time index i and depth index j
  define full ShapePressureGrid before scan results
```

## 総括

Checkpoint `129` で Route A はほぼ閉じた。

```text
height_i
residual_i
first_failed_i = height_i + 1
```

この三列を同じ time index で読めるようになった。

次は Route B。
ただし Lean theorem を増やす前に、pressure sign pattern を数値観測するべきじゃ。

賢狼の見立てでは、ここから本当に見るべき問いはこれ。

```text
time profile のどの特徴が、
depth profile の margin sign pattern と結びつくのか？
```

ここが見えれば、`ShapePressureGrid` はこじつけではなく、観測から自然に生える。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 18185c2d..a44bd916 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -913,6 +913,16 @@ theorem orbitWindowFirstFailedPow2DepthSeq_length
     (orbitWindowFirstFailedPow2DepthSeq n k).length = k := by
   simp [orbitWindowFirstFailedPow2DepthSeq]

+/--
+Reading the ordered first-failed-depth profile at an in-window time recovers
+the pointwise first-failed depth.
+-/
+theorem orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
+    (n : OddNat) {i k : ℕ} (hi : i < k) :
+    (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
+      some (orbitWindowFirstFailedPow2Depth n i) := by
+  simp [orbitWindowFirstFailedPow2DepthSeq, hi]
+
 /--
 Window first-failed depth is exactly one more than the observed window height.
 -/
@@ -922,6 +932,70 @@ theorem orbitWindowFirstFailedPow2Depth_eq_height_add_one
   unfold orbitWindowFirstFailedPow2Depth FirstFailedPow2Depth
   rw [orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel]

+/--
+Reading the ordered first-failed-depth profile also recovers the observed height
+plus one.
+-/
+theorem orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
+    (n : OddNat) {i k : ℕ} (hi : i < k) :
+    (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
+      some (orbitWindowHeight n i + 1) := by
+  rw [orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n hi]
+  rw [orbitWindowFirstFailedPow2Depth_eq_height_add_one]
+
+/--
+The prefix of length `r` in the first-failed-depth profile has length `r` when
+`r` lies inside the window.
+-/
+theorem orbitWindowFirstFailedPow2DepthSeq_take_length
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    ((orbitWindowFirstFailedPow2DepthSeq n k).take r).length = r := by
+  simp [orbitWindowFirstFailedPow2DepthSeq_length, Nat.min_eq_left hr]
+
+/--
+Reading a prefix of the first-failed-depth profile recovers the same pointwise
+first-failed depth while the index remains inside the prefix.
+-/
+theorem orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
+    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
+    ((orbitWindowFirstFailedPow2DepthSeq n k).take r)[i]? =
+      some (orbitWindowFirstFailedPow2Depth n i) := by
+  rw [List.getElem?_take_of_lt hi]
+  exact orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n
+    (Nat.lt_of_lt_of_le hi hr)
+
+/--
+Reading a prefix of the first-failed-depth profile also recovers the observed
+height plus one.
+-/
+theorem orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one
+    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
+    ((orbitWindowFirstFailedPow2DepthSeq n k).take r)[i]? =
+      some (orbitWindowHeight n i + 1) := by
+  rw [orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some n hi hr]
+  rw [orbitWindowFirstFailedPow2Depth_eq_height_add_one]
+
+/--
+The three time-profile lists are aligned at every in-window index.
+
+This is a deliberately one-dimensional observation theorem.  It keeps the time
+axis `i` separate from the pressure-depth axis `j`; a later
+`ShapePressureGrid` should combine those axes explicitly rather than hiding
+that distinction in one index.
+-/
+theorem orbitWindow_threeProfiles_get?_eq_some
+    (n : OddNat) {i k : ℕ} (hi : i < k) :
+    (orbitWindowHeightSeq n k)[i]? = some (orbitWindowHeight n i) ∧
+      (orbitWindowResidualShapeSeq n k)[i]? =
+        some (orbitWindowResidualShape n i) ∧
+      (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
+        some (orbitWindowFirstFailedPow2Depth n i) := by
+  constructor
+  · exact orbitWindowHeightSeq_get?_eq_some n hi
+  constructor
+  · exact orbitWindowResidualShapeSeq_get?_eq_some n hi
+  · exact orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n hi
+
 /--
 The integer threshold lower bound also applies to prefixes.
 -/
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index ad33833a..4e4c5757 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -149,6 +149,10 @@ orbitWindowResidualShapeSeq_get?_eq_some
 orbitWindowResidualShapeSeq_take_get?_eq_some
 orbitWindowFirstFailedPow2Depth
 orbitWindowFirstFailedPow2DepthSeq
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
+orbitWindow_threeProfiles_get?_eq_some
 orbitWindowResidueCountPow2
 orbitWindowResidueCountPow2Tail
 sourcePow2Distribution_total
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-FirstFailedDepthSequence-129.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-FirstFailedDepthSequence-129.md
new file mode 100644
index 00000000..de9efd29
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-FirstFailedDepthSequence-129.md
@@ -0,0 +1,101 @@
+# Collatz First Failed Depth Sequence - Checkpoint 129
+
+Checkpoint 129 closes the small Route A list-API gap for the first-failed-depth
+profile.
+
+Checkpoint 128 introduced:
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq
+orbitWindowFirstFailedPow2DepthSeq_length
+orbitWindowFirstFailedPow2Depth_eq_height_add_one
+```
+
+Checkpoint 129 adds the same index and prefix API already available for the
+height and residual-shape profiles.
+
+## New Theorems
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
+orbitWindowFirstFailedPow2DepthSeq_take_length
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one
+orbitWindow_threeProfiles_get?_eq_some
+```
+
+The main operational reading is:
+
+```text
+failed_i = height_i + 1
+```
+
+and this can now be recovered through direct list indexing and prefix indexing.
+
+## Three Aligned Time Profiles
+
+The finite time window now has three aligned profiles:
+
+```text
+orbitWindowHeightSeq
+orbitWindowResidualShapeSeq
+orbitWindowFirstFailedPow2DepthSeq
+```
+
+The theorem
+
+```lean
+orbitWindow_threeProfiles_get?_eq_some
+```
+
+packages the simultaneous `get?` reading at an in-window time index.
+
+This is useful because later work can introduce a `ShapePressureGrid` without
+rebuilding the one-dimensional time-profile API.
+
+## Axis Warning
+
+The checkpoint still keeps two axes separate.
+
+```text
+time index i:
+  height_i
+  residual_i
+  first_failed_i
+
+pressure depth index j:
+  margin(j)
+  frontier(j)
+  local island(j)
+```
+
+The theorem surface intentionally does not collapse `i` and `j`.  A later
+two-dimensional structure should expose both axes explicitly.
+
+## Suggested Next Work
+
+Route A is now essentially closed for the current three time profiles.
+
+The next useful direction is Route B:
+
+```text
+pressure sign-pattern scan
+  positive depths
+  positive blocks
+  local islands
+  frontier depth
+  sign-change-up positions
+```
+
+The scan should also carry:
+
+```text
+height_seq
+residual_shape_seq
+first_failed_depth_seq
+residual_mod_8/16/32
+```
+
+so the next Lean predicates are based on observed time x depth correlations,
+not on a guessed one-dimensional collapse.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index f80ff0b1..145e8d86 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -155,6 +155,36 @@ orbitWindowResidualShapeSeq_take_length
 orbitWindowResidualShapeSeq_take_get?_eq_some
 ```

+### `orbitWindowFirstFailedPow2DepthSeq`
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq n k
+```
+
+This is the ordered list of first failed power-of-two alignment depths over the
+first `k` time positions.
+
+Checkpoint 129 adds the matching list helpers:
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
+orbitWindowFirstFailedPow2DepthSeq_take_length
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one
+orbitWindow_threeProfiles_get?_eq_some
+```
+
+The main reading is:
+
+```text
+first_failed_i = height_i + 1
+```
+
+The `orbitWindow_threeProfiles_get?_eq_some` theorem aligns the height,
+residual-shape, and first-failed-depth profiles at the same time index.  It is
+still a one-dimensional theorem: the pressure-depth index is a separate axis.
+
 ## Separation And Collision

 The bridge includes a finite split:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index aa748855..ce728208 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -174,6 +174,12 @@ orbitWindow_firstFailed_remainder_ne_zero
 orbitWindowFirstFailedPow2DepthSeq
 orbitWindowFirstFailedPow2DepthSeq_length
 orbitWindowFirstFailedPow2Depth_eq_height_add_one
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
+orbitWindowFirstFailedPow2DepthSeq_take_length
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one
+orbitWindow_threeProfiles_get?_eq_some
 ```

 The finite window now supports the reading:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md
index bd64f2b8..03616f5e 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md
@@ -126,6 +126,11 @@ orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
 orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels_take
 ```

+Checkpoint 129 implements the first-failed-depth list helpers and adds
+`orbitWindow_threeProfiles_get?_eq_some`, so the remaining residual-shape extra
+is only needed if a later proof specifically wants a prefix version of shifted
+labels.
+
 ### Route B: pressure sign-pattern statistics

 Use Python summary scans before adding heavier Lean names:
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-129.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-129.md
new file mode 100644
index 00000000..f74f8e46
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-129.md
@@ -0,0 +1,161 @@
+# Report Petal 129
+
+## Summary
+
+Checkpoint 129 completes the small Route A close-out requested by the previous
+report.
+
+The first-failed-depth profile now has the same basic list API as the height
+and residual-shape profiles:
+
+```text
+length
+get?
+take length
+take get?
+```
+
+It also has `height + 1` versions of the `get?` lemmas, which makes the
+boundary interpretation directly usable from list indexing.
+
+## Implemented Lean Surface
+
+Added:
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
+orbitWindowFirstFailedPow2DepthSeq_take_length
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one
+orbitWindow_threeProfiles_get?_eq_some
+```
+
+The main theorem reading is:
+
+```text
+first_failed_i = height_i + 1
+```
+
+and this can now be recovered both from the full sequence and from prefixes.
+
+## Three Time Profiles
+
+The following three ordered profiles now share the same basic interface:
+
+```lean
+orbitWindowHeightSeq
+orbitWindowResidualShapeSeq
+orbitWindowFirstFailedPow2DepthSeq
+```
+
+The added theorem
+
+```lean
+orbitWindow_threeProfiles_get?_eq_some
+```
+
+packages their aligned `get?` facts at a single in-window time index.
+
+This is intentionally a time-profile theorem.  It does not mix the time index
+`i` with the pressure-depth index `j`.
+
+## Added Inference
+
+Route A is now basically closed for the current one-dimensional time profiles.
+
+The next useful work is not another guessed theorem about pressure.  The better
+route is a pressure sign-pattern scan that carries the aligned time-profile
+data:
+
+```text
+height_seq
+residual_shape_seq
+first_failed_depth_seq
+residual_mod_8_seq
+residual_mod_16_seq
+residual_mod_32_seq
+positive_depths
+positive_blocks
+local_islands
+sign_change_up_positions
+first_frontier_depth
+frontier_margin
+margin_jump
+retention_drop
+continuation_drop
+```
+
+The target question is:
+
+```text
+Which time-profile features correlate with pressure-depth sign patterns?
+```
+
+This is the data route toward a later `ShapePressureGrid`.
+
+## Documentation Updates
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-FirstFailedDepthSequence-129.md
+```
+
+## Suggested Checkpoint 130
+
+Recommended route:
+
+```text
+Route B pressure scan
+```
+
+Use Python or a lightweight generated table first.  Do not add a large Lean
+predicate until the scan shows a stable sign-pattern feature.
+
+If a Lean-only checkpoint is needed before the scan, keep it very thin:
+
+```lean
+SourcePressurePositiveBlock
+```
+
+but the preferred next step is still numerical classification of pressure
+sign-patterns paired with the three time profiles.
+
+## Verification
+
+Commands:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean lean/dk_math/DkMath/Collatz/PetalBridge.lean
+git diff --check
+```
+
+Initial result:
+
+```text
+PetalBridge build: passed
+Collatz2K26 build: passed
+local Collatz sorry scan: passed, no hits in GnomonEvaluation/PetalBridge
+diff whitespace check: passed
+```
+
+The `Collatz2K26` build still reports the existing unrelated warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+No new Collatz-side `sorry` was introduced.
````
`````
