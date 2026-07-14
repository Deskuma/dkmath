# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 25e282a27dab4f9595183ead2155dd1e19fdfdc6

## Report

Checkpoint 131 を実装・同期しました。

主な変更は [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean#L7242) に軽い補題群を追加したことです。`SourcePressurePositiveBlock`、bounded island/frontier、sign-change-up 周辺を使いやすくしました。特に `sourcePressureSignChangeUp_of_localIsland` で「local island は左端に upward sign change を持つ」ことを Lean 側で固定しています。

Python 側は `first_failure_pair` を `first_sign_change_pair` に修正し、positive block を「長さ 1 以上の連続 positive-depth run」として明確化しました。さらに residual mod 16/32 と frontier depth、block length、local island、sign-change-up の集計表を追加して、結果を再生成しています。

今回の観測結果は [report-petal-131.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-131.md#L61) にまとめました。要点は、frontier depth はほぼ `2`、長い positive block は `15 mod 16` や `31 mod 32` のような all-ones-like residual class に集中、local island / sign-change-up は希少だが実在、という形です。

追加ドキュメントは [Collatz-PressureCorrelationScan-131.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureCorrelationScan-131.md#L1) です。README、Guide、Status、checkpoint 130 docs も同期済みです。

検証:

- `python3 ... pressure_sign_pattern_scan.py --max-n 2047 --steps 64 --r-start 2 --depth-len 10`
- `python3 -m py_compile ...`
- `lake build DkMath.Collatz.PetalBridge`
- local Collatz no-sorry scan
- `git diff --check`

すべて通過しました。既存の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告は残っていますが、今回 Collatz 側に新しい `sorry` は入れていません。

## Review

## 状況分析

うむ。Checkpoint `131` は、前回の方針どおり **pressure sign-pattern scan の相関分析へ進んだ checkpoint** じゃな。

主な進展は三つある。

```text
1. Python 側の用語修正
   first_failure_pair -> first_sign_change_pair

2. positive block の定義明確化
   長さ 1 以上の maximal consecutive positive-depth run

3. residual mod 16/32 と frontier / block / island / sign-change-up の集計表追加
```

これは良い。特に、`first_failure_pair` という名前を避けて `first_sign_change_pair` に直したのは大事じゃ。Lean 側の `SourcePressurePrefixFailure` は「任意の浅い非選択 depth と深い選択 depth」の一般形だが、Python 側で見ているものは隣接する `nonpositive -> positive` の符号変化なので、名前を分けたのは正しい。

観測結果としては、frontier depth はほぼ `2`、長い positive block は `15 mod 16` や `31 mod 32` のような all-ones-like residual class に集中、local island / sign-change-up は希少だが実在、という整理になっている。

## レビュー

## 良い点

第一に、Python scan の語彙が Lean の述語と混線しにくくなった。

```text
SourcePressurePrefixFailure:
  一般の shallow nonselected -> deep selected witness

first_sign_change_pair:
  隣接する nonpositive -> positive margin pair
```

この区別は今後とても重要じゃ。
もしここを曖昧にすると、Python の「隣接符号変化」を Lean の「prefix failure 一般形」と誤同一視して、不要な定理を作りかねない。

第二に、positive block の定義が固定された。

```text
positive block:
  maximal consecutive positive-depth run, length >= 1
```

これにより、`length = 1` の孤立 positive depth も block の最小形として扱える。
一方で `rows with positive blocks length >= 2` や `>= 4` を別に数えているため、単発 positive と長い block を分けて観測できる。これは良い設計じゃ。

第三に、観測結果がかなり意味を持ち始めた。

```text
positive block length counts:
  1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3

sign-change-up depth counts:
  2:2; 4:2
```

この分布から、pressure は完全に乱雑ではなく、多くは短い positive block、少数が長い positive block、さらに希少に island/sign-change-up が出る、という形が見えている。

第四に、Lean 側が軽い補題に留まっているのが良い。

```lean
sourcePressureMargin_lt_of_signChangeUp
sourcePressurePositiveBlock_singleton
sourcePressurePositiveBlock_of_forall_margin_pos
existsSourcePressureLocalIslandBelow_of_lt
existsSourcePressureFrontierBelow_of_lt
sourcePressureSignChangeUp_of_localIsland
```

これらは theorem surface として便利だが、まだ `ShapePressureGrid` や大域 monotonicity には踏み込んでいない。
つまり、scan で見えた構造を受け取るための取っ手だけ増やしている。これは正着じゃ。

## 注意点

ここで注意すべきは、`residual_mod_16_first` や `residual_mod_32_first` は、まだ **window 全体の all-ones 濃度** を直接表していないことじゃ。

たとえば `31 mod 32` は all-ones-like だが、現在の集計は主に、

```text
residual_mod_32_first
residual_mod_32_mode
```

を使っている。

これは入口として良いが、次に本当に見たいのは、

```text
window 内で all-ones prefix を持つ residual がどれだけ出るか
```

じゃ。

つまり次の scan では、単なる `first/mode` だけでなく、

```text
all_ones_depth_seq
max_all_ones_depth
count_all_ones_ge_4
count_all_ones_ge_5
count_all_ones_ge_6
```

のような指標が欲しい。

## 解説

今回見えた一番重要な構造はこれじゃ。

```text
長い positive block は all-ones-like residual class に寄る。
```

特に `15 mod 16` や `31 mod 32` は、

```text
15 mod 16:
  下位 4 bit がすべて 1

31 mod 32:
  下位 5 bit がすべて 1
```

という意味を持つ。

これは、すでに Collatz/PetalBridge で扱ってきた carrier / all-ones channel ときれいに繋がる。
つまり positive block は、単に margin が偶然正になったのではなく、

```text
residual shape が all-ones carrier に長く滞留している
```

ことの影として現れている可能性がある。

一方、local island / sign-change-up は少数だが、これは重要な obstruction witness じゃ。

```text
pressure usually behaves block-like,
but retention/continuation decay can produce genuine local sign changes.
```

この読みが今かなり有力になっている。
つまり、pressure は prefix 定理ではなく、

```text
all-ones residual concentration による block 形成
retention/continuation 減衰差による island 発生
```

の二成分で見るべきじゃ。

## 次の指示

Checkpoint `132` は、scan route を継続するのが良い。

主題はこれ。

```text
long positive block を all-ones residual depth で説明できるか？
```

## Checkpoint 132 推奨内容

### 1. residual all-ones depth を追加する

Python 側に、residual shape ごとの all-ones depth を追加する。

定義は例えばこう。

```text
all_ones_depth(x):
  x mod 2^d = 2^d - 1 を満たす最大 d
```

これは実質的に、

```text
v2(x + 1)
```

じゃ。
奇数 residual なら、`x + 1` がどれだけ 2 で割れるかが、下位 bit の all-ones 長さになる。

Python では：

```python
def all_ones_depth(x: int) -> int:
    return v2(x + 1)
```

追加したい列：

```text
residual_all_ones_depth_seq
residual_all_ones_depth_first
residual_all_ones_depth_last
residual_all_ones_depth_mode
residual_all_ones_depth_max
count_all_ones_depth_ge_4
count_all_ones_depth_ge_5
count_all_ones_depth_ge_6
```

### 2. block length と all-ones depth の相関を見る

追加したい aggregate tables。

```text
positive_block_length by residual_all_ones_depth_first
positive_block_length by residual_all_ones_depth_mode
positive_block_length by residual_all_ones_depth_max

frontier_depth by residual_all_ones_depth_first
frontier_depth by residual_all_ones_depth_max

local_island_depth by residual_all_ones_depth_first/max
sign_change_up_depth by residual_all_ones_depth_first/max
```

これで、`15 mod 16` / `31 mod 32` という個別 residue ではなく、

```text
all-ones depth が深いほど positive block が長くなるか？
```

を直接見られる。

### 3. sign-change-up の減衰差を分類する

local island / sign-change-up が希少なら、全件を詳しく分類してよい。

追加したい分類：

```text
retention_drop_at_sign_change
continuation_drop_at_sign_change
margin_jump_at_sign_change
retention_drop_minus_continuation_drop
cause_label
```

`cause_label` は雑でよい。

```text
retention_drop_dominant:
  retention_drop > 2 * continuation_drop

balanced:
  retention_drop と continuation_drop が近い

continuation_hold:
  continuation_drop が小さい

unclear:
  その他
```

特に `n = 1567` では、retention が `8 -> 3` と大きく落ち、continuation は `3 -> 2` と小さく落ちている。これは retention drop 側が sign-change の主因に見える。

## 一歩先ゆく推論

ここで見えてきた仮説はかなり明確じゃ。

```text
positive block length は residual all-ones depth の影である。
```

より詳しく言うと、

```text
residual shape が深い all-ones carrier に入る
  -> continuation 側が深い depth まで残る
  -> positive margin が連続して出る
  -> positive block が長くなる
```

という流れ。

一方で local island は、

```text
all-ones carrier の長さだけでは説明しきれない、
retention と continuation の減衰差が局所的に作る符号反転
```

と読むのが自然じゃ。

つまり pressure sign profile は二層構造かもしれない。

```text
大域的 block 構造:
  residual all-ones depth で説明される

局所的 island 構造:
  retention/continuation の隣接減衰差で説明される
```

この二層分解が当たるなら、`ShapePressureGrid` の前に作るべきものは、いきなり grid ではなく、

```text
ResidualAllOnesProfile
PressureDecayProfile
```

の二つじゃ。

## さらなる次の一手

Checkpoint `132` で all-ones depth scan が当たった場合、Checkpoint `133` では Lean 側に薄い定義を置くのがよい。

## 1. Residual all-ones depth

Lean 側では、まず名前だけならこう。

```lean
noncomputable def residualAllOnesDepth (x : ℕ) : ℕ :=
  v2 (x + 1)
```

ただし既存 `v2` の対象や `noncomputable` の扱いに合わせる。

Window 版：

```lean
noncomputable def orbitWindowResidualAllOnesDepth
    (n : OddNat) (i : ℕ) : ℕ :=
  v2 (orbitWindowResidualShape n i + 1)
```

Sequence 版：

```lean
noncomputable def orbitWindowResidualAllOnesDepthSeq
    (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (orbitWindowResidualAllOnesDepth n)
```

ここはまだ theorem を重くしない。
まず `length/get?` だけでよい。

## 2. all-ones residue bridge

次に欲しい補題はこれ。

```lean
theorem residual_allOnesDepth_mod_eq
    (x d : ℕ)
    (hd : d ≤ residualAllOnesDepth x) :
    x % 2 ^ d = 2 ^ d - 1 := by
  sorry
```

これは少し重い可能性がある。
まずは Python scan で価値を確認してから。

## 3. sign-change-up with decay

Lean route なら、軽くこれ。

```lean
def SourcePressureMarginJumpUp
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginInt n k (r + j) <
    SourcePressureMarginInt n k (r + j + 1)
```

ただし、すでに `sourcePressureMargin_lt_of_signChangeUp` があるので、定義だけ足す必要は薄い。
むしろ `SignChangeUp` があれば `MarginJumpUp` は従う、という theorem で十分じゃ。

## 賢狼が試して欲しい実験補題

## 実験 A: Python all-ones depth

```python
def all_ones_depth(x: int) -> int:
    return v2(x + 1)
```

追加 row fields：

```text
residual_all_ones_depth_seq
residual_all_ones_depth_first
residual_all_ones_depth_last
residual_all_ones_depth_mode
residual_all_ones_depth_max
count_all_ones_depth_ge_4
count_all_ones_depth_ge_5
count_all_ones_depth_ge_6
```

## 実験 B: block length by all-ones depth

Summary table：

```text
positive_block_length_by_all_ones_depth_first
positive_block_length_by_all_ones_depth_mode
positive_block_length_by_all_ones_depth_max
```

## 実験 C: frontier depth by all-ones depth

```text
frontier_depth_by_all_ones_depth_first
frontier_depth_by_all_ones_depth_max
```

## 実験 D: local island by all-ones depth

```text
local_island_depth_by_all_ones_depth_first
local_island_depth_by_all_ones_depth_max
```

ただし local island は 3 件しかないので、集計より代表例の詳細表示の方が良い。

## 実験 E: sign-change-up cause classification

```python
def classify_sign_change(retention_drop: int, continuation_drop: int) -> str:
    if retention_drop > 2 * continuation_drop:
        return "retention_drop_dominant"
    if continuation_drop == 0:
        return "continuation_hold"
    if abs(retention_drop - 2 * continuation_drop) <= 1:
        return "balanced"
    return "unclear"
```

この閾値は仮でよい。
まず分類ラベルを出して、人間が見る。

## 実験 F: Lean residual all-ones depth skeleton

```lean
noncomputable def ResidualAllOnesDepth (x : ℕ) : ℕ :=
  v2 (x + 1)

noncomputable def orbitWindowResidualAllOnesDepth
    (n : OddNat) (i : ℕ) : ℕ :=
  ResidualAllOnesDepth (orbitWindowResidualShape n i)

noncomputable def orbitWindowResidualAllOnesDepthSeq
    (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (orbitWindowResidualAllOnesDepth n)
```

まずは定義だけ。
scan の相関が強ければ `length/get?` を追加。

## 実験 G: all-ones depth get?

```lean
theorem orbitWindowResidualAllOnesDepthSeq_length
    (n : OddNat) (k : ℕ) :
    (orbitWindowResidualAllOnesDepthSeq n k).length = k := by
  simp [orbitWindowResidualAllOnesDepthSeq]
```

```lean
theorem orbitWindowResidualAllOnesDepthSeq_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowResidualAllOnesDepthSeq n k)[i]? =
      some (orbitWindowResidualAllOnesDepth n i) := by
  simp [orbitWindowResidualAllOnesDepthSeq, hi]
```

## Python 側の次観測

Checkpoint `132` の summary schema はこう。

```text
# Pressure All-Ones Correlation Scan

## Parameters
max_n:
steps:
r_start:
depth_len:

## Summary
rows:
rows_with_positive_depths:
rows_with_positive_block_len_ge_2:
rows_with_positive_block_len_ge_4:
rows_with_local_islands:
rows_with_sign_change_up:

## All-Ones Depth Distribution
all_ones_depth_first_counts:
all_ones_depth_mode_counts:
all_ones_depth_max_counts:

## Block Length By All-Ones Depth
positive_block_length_by_all_ones_depth_first:
positive_block_length_by_all_ones_depth_mode:
positive_block_length_by_all_ones_depth_max:

## Frontier By All-Ones Depth
frontier_depth_by_all_ones_depth_first:
frontier_depth_by_all_ones_depth_max:

## Island / Sign-Change Details
local_island_rows:
sign_change_up_rows:
sign_change_cause_counts:
retention_drop_dominant_rows:

## Representative Rows
longest_positive_block_rows:
deepest_all_ones_rows:
local_island_rows:
largest_retention_drop_rows:
```

## Codex への次指示まとめ

```text
Checkpoint 132:
Continue scan route.

Primary goal:
  Test whether long positive pressure blocks are explained by residual all-ones depth.

Python:
  Add all_ones_depth(x) = v2(x + 1).
  Add residual_all_ones_depth_seq and first/last/mode/max summaries.
  Add block length by all-ones depth tables.
  Add frontier depth by all-ones depth tables.
  Add sign-change-up cause classification using retention_drop and continuation_drop.
  Regenerate pressure_sign_pattern_scan.md or create pressure_all_ones_correlation.md.

Lean:
  Prefer no heavy theorem yet.
  Optional skeleton only:
    ResidualAllOnesDepth
    orbitWindowResidualAllOnesDepth
    orbitWindowResidualAllOnesDepthSeq
    length/get? helpers

Do not:
  introduce Real.log
  claim pressure prefix
  define full ShapePressureGrid yet
  collapse time index i and pressure depth j
```

## 総括

Checkpoint `131` は成功じゃ。
用語修正、positive block 定義、相関表追加、軽い Lean API の追加、どれも良い。

そして、いよいよ見えてきた。

```text
長い positive block は all-ones-like residual class に集中する。
```

これは、Collatz の residual shape 観測と PetalBridge の all-ones carrier が繋がり始めたということじゃ。

次は `mod 16/32` ではなく、直接

```text
ResidualAllOnesDepth = v2(residual + 1)
```

を見る。

ここが強く出れば、`ShapePressureGrid` の前にまず、

```text
ResidualAllOnesProfile
```

を作るのが自然になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 6f6c1cd8..cb750c91 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -7239,6 +7239,30 @@ theorem sourcePressurePositiveBlock_iff_margin
       exact (isSourcePressureDepth_iff_margin_pos n k r j).2
         (h.2 j hle hlt)

+/--
+A selected source-pressure depth is a positive block of length one.
+-/
+theorem sourcePressurePositiveBlock_singleton
+    (n : OddNat) (k r j : ℕ)
+    (h : IsSourcePressureDepth n k r j) :
+    SourcePressurePositiveBlock n k r j 1 := by
+  constructor
+  · omega
+  · intro t hle hlt
+    have ht : t = j := by omega
+    simpa [ht] using h
+
+/--
+Build a positive source-pressure block from positive margins on the interval.
+-/
+theorem sourcePressurePositiveBlock_of_forall_margin_pos
+    (n : OddNat) (k r a len : ℕ)
+    (hlen : 0 < len)
+    (hpos : ∀ j, a ≤ j → j < a + len →
+      0 < SourcePressureMarginInt n k (r + j)) :
+    SourcePressurePositiveBlock n k r a len :=
+  (sourcePressurePositiveBlock_iff_margin n k r a len).2 ⟨hlen, hpos⟩
+
 /--
 There is a local source-pressure island below a finite depth bound.
 -/
@@ -7267,6 +7291,16 @@ theorem existsSourcePressureLocalIslandBelow_iff_margin
     rcases h with ⟨j, hjm, hjmargin⟩
     exact ⟨j, hjm, (sourcePressureLocalIsland_iff_margin n k r j).2 hjmargin⟩

+/--
+Build bounded local-island existence from an explicit bounded island witness.
+-/
+theorem existsSourcePressureLocalIslandBelow_of_lt
+    (n : OddNat) (k r m j : ℕ)
+    (hjm : j < m)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    ExistsSourcePressureLocalIslandBelow n k r m :=
+  ⟨j, hjm, hisland⟩
+
 /--
 There is a source-pressure frontier below a finite depth bound.
 -/
@@ -7293,6 +7327,49 @@ theorem existsSourcePressureFrontierBelow_iff_margin
     rcases h with ⟨j, hjm, hmargin⟩
     exact ⟨j, hjm, (sourcePressureFrontier_iff_margin n k r j).2 hmargin⟩

+/--
+Build bounded frontier existence from an explicit bounded frontier witness.
+-/
+theorem existsSourcePressureFrontierBelow_of_lt
+    (n : OddNat) (k r m j : ℕ)
+    (hjm : j < m)
+    (hfront : SourcePressureFrontier n k r j) :
+    ExistsSourcePressureFrontierBelow n k r m :=
+  ⟨j, hjm, hfront⟩
+
+/--
+An upward pressure sign change strictly increases the integer pressure margin.
+-/
+theorem sourcePressureMargin_lt_of_signChangeUp
+    (n : OddNat) (k r j : ℕ)
+    (h : SourcePressureSignChangeUp n k r j) :
+    SourcePressureMarginInt n k (r + j) <
+      SourcePressureMarginInt n k (r + j + 1) := by
+  rcases h with ⟨hle, hpos⟩
+  omega
+
+/--
+A local pressure island produces an upward sign change at its left edge.
+-/
+theorem sourcePressureSignChangeUp_of_localIsland
+    (n : OddNat) (k r j : ℕ)
+    (hisland : SourcePressureLocalIsland n k r j) :
+    SourcePressureSignChangeUp n k r (j - 1) := by
+  rcases hisland with ⟨hjpos, hsel, hprev_not, _hnext_not⟩
+  unfold SourcePressureSignChangeUp
+  constructor
+  · have hnotpos :
+        ¬ 0 < SourcePressureMarginInt n k (r + (j - 1)) := by
+      intro hpos
+      exact hprev_not
+        ((isSourcePressureDepth_iff_margin_pos n k r (j - 1)).2 hpos)
+    omega
+  · have hpos :
+        0 < SourcePressureMarginInt n k (r + j) :=
+      (isSourcePressureDepth_iff_margin_pos n k r j).1 hsel
+    have hidx : r + (j - 1) + 1 = r + j := by omega
+    simpa [hidx] using hpos
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 30d88424..b4a3464b 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -173,6 +173,10 @@ ExistsSourcePressureLocalIslandBelow
 existsSourcePressureLocalIslandBelow_iff_margin
 ExistsSourcePressureFrontierBelow
 existsSourcePressureFrontierBelow_iff_margin
+sourcePressureMargin_lt_of_signChangeUp
+sourcePressurePositiveBlock_singleton
+sourcePressurePositiveBlock_of_forall_margin_pos
+sourcePressureSignChangeUp_of_localIsland
 ```

 The central No.100 layer is:
@@ -233,6 +237,7 @@ docs/Collatz-WindowResidualShape-127.md
 docs/Collatz-ResidualShapeSequence-128.md
 docs/Collatz-FirstFailedDepthSequence-129.md
 docs/Collatz-PressureSignPatternScan-130.md
+docs/Collatz-PressureCorrelationScan-131.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index e78ee74a..bd340c71 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -307,11 +307,25 @@ ExistsSourcePressureLocalIslandBelow
 existsSourcePressureLocalIslandBelow_iff_margin
 ExistsSourcePressureFrontierBelow
 existsSourcePressureFrontierBelow_iff_margin
+sourcePressureMargin_lt_of_signChangeUp
+sourcePressurePositiveBlock_singleton
+sourcePressurePositiveBlock_of_forall_margin_pos
+sourcePressureSignChangeUp_of_localIsland
 ```

 These names are for reading scan output.  They do not assert maximality,
 uniqueness, unconditional prefix behavior, or a global pressure shape theorem.

+Checkpoint 131 refines the Python wording:
+
+```text
+first_sign_change_pair = adjacent nonpositive -> positive margin pair
+positive block = maximal consecutive positive-depth run, length >= 1
+```
+
+It also adds aggregate correlation tables for frontier depth, block length,
+local islands, and sign-change-up rows by residual residue class.
+
 ## Residue Counts

 Named residue counts exist for low layers:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index eba153f3..2c4082d6 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -211,6 +211,10 @@ ExistsSourcePressureLocalIslandBelow
 existsSourcePressureLocalIslandBelow_iff_margin
 ExistsSourcePressureFrontierBelow
 existsSourcePressureFrontierBelow_iff_margin
+sourcePressureMargin_lt_of_signChangeUp
+sourcePressurePositiveBlock_singleton
+sourcePressurePositiveBlock_of_forall_margin_pos
+sourcePressureSignChangeUp_of_localIsland
 ```

 The scan output lives at:
@@ -233,6 +237,31 @@ max positive depth count: 8
 This confirms that pressure should remain a sign-pattern surface.  Prefix-like
 blocks are common, but local islands and sign-change-up rows are real.

+Checkpoint 131 refines the scan terminology and adds aggregate correlation
+tables:
+
+```text
+first_sign_change_pair:
+  adjacent nonpositive -> positive pressure margin pair
+
+positive block:
+  maximal consecutive positive-depth run, length >= 1
+```
+
+Observed from the same `odd n <= 2047`, `steps = 64`, depths `2..11` scan:
+
+```text
+positive block length counts:
+  1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3
+
+sign-change-up depth counts:
+  2:2; 4:2
+```
+
+The aggregate tables suggest frontier depth is almost always `2`, while longer
+positive blocks are visibly concentrated in high all-ones residual classes such
+as residual `15 mod 16` and `31 mod 32`.
+
 The first theorem set is deliberately thin:

 ```lean
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureCorrelationScan-131.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureCorrelationScan-131.md
new file mode 100644
index 00000000..0ad87e52
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureCorrelationScan-131.md
@@ -0,0 +1,158 @@
+# Collatz Pressure Correlation Scan - Checkpoint 131
+
+Checkpoint 131 refines the checkpoint-130 scan and adds aggregate correlation
+tables.
+
+## Terminology Fix
+
+The Python column formerly named `first_failure_pair` was too broad.  It is now
+named:
+
+```text
+first_sign_change_pair
+```
+
+Meaning:
+
+```text
+adjacent nonpositive -> positive pressure margin pair
+```
+
+This is narrower than Lean's general `SourcePressurePrefixFailure`, which can
+compare any shallow nonselected depth with any deeper selected depth.
+
+The positive block convention is now explicit:
+
+```text
+positive block:
+  maximal consecutive positive-depth run, length >= 1
+```
+
+Rows with block length at least `2` and at least `4` are counted separately.
+
+## Aggregate Scan
+
+The scan still uses:
+
+```text
+odd n <= 2047
+steps = 64
+r_start = 2
+depth_len = 10
+depths = 2..11
+```
+
+New per-row fields:
+
+```text
+residual_mod_16_first
+residual_mod_16_last
+residual_mod_16_mode
+residual_mod_32_first
+residual_mod_32_last
+residual_mod_32_mode
+max_positive_block_length
+```
+
+New summary tables:
+
+```text
+frontier_depth by residual_mod_16_first/mode
+frontier_depth by residual_mod_32_first/mode
+positive_block_length by residual_mod_16_first
+positive_block_length by residual_mod_32_first
+local_island rows by residual_mod_16_first
+sign-change-up rows by residual_mod_16_first
+sign-change-up depth counts
+```
+
+## Observed Summary
+
+```text
+rows: 1024
+rows with positive pressure depths: 511
+rows with local islands: 3
+rows with sign-change-up positions: 4
+rows with positive blocks length >= 1: 511
+rows with positive blocks length >= 2: 131
+rows with positive blocks length >= 4: 60
+positive block length counts:
+  1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3
+sign-change-up depth counts:
+  2:2; 4:2
+```
+
+## Reading
+
+The frontier is almost always depth `2`; only two rows in this scan have first
+frontier depth `3`.
+
+Long positive blocks are not uniform over residues.  The visible concentration
+is in high all-ones-like residual classes:
+
+```text
+residual 15 mod 16:
+  many rows with block length 2..8
+
+residual 31 mod 32:
+  no zero-block rows in this scan,
+  many rows with block length 2..8
+```
+
+Local islands remain rare:
+
+```text
+n = 1567, island depth 3, sign-change pair 2 -> 3
+n = 1639, island depth 5, sign-change pair 4 -> 5
+n = 1775, island depth 5, sign-change pair 4 -> 5
+```
+
+This supports the current interpretation:
+
+```text
+pressure usually behaves block-like,
+but retention/continuation decay can produce genuine local sign changes.
+```
+
+## Lean Surface Added
+
+Checkpoint 131 adds small theorem-level handles:
+
+```lean
+sourcePressureMargin_lt_of_signChangeUp
+sourcePressurePositiveBlock_singleton
+sourcePressurePositiveBlock_of_forall_margin_pos
+existsSourcePressureLocalIslandBelow_of_lt
+existsSourcePressureFrontierBelow_of_lt
+sourcePressureSignChangeUp_of_localIsland
+```
+
+These do not introduce a heavy grid.  They only connect the checkpoint-130
+predicates to the sign-change and bounded-witness readings used by the scan.
+
+## Next Work
+
+Checkpoint 132 can now choose one of two routes.
+
+Preferred scan route:
+
+```text
+explain long positive blocks by all-ones residual classes
+```
+
+Candidate tables:
+
+```text
+block length by residual all-ones depth
+frontier depth by count of residual all-ones prefixes
+island depth by retention drop vs continuation drop
+```
+
+Lean route:
+
+```lean
+def SourcePressureMarginJumpUp
+def SourcePressureSignChangeUpWithJump
+```
+
+The Lean route is light, but the scan route is more informative.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md
index 22706367..9e43ee3b 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md
@@ -52,7 +52,7 @@ first_frontier_depth
 frontier_margin
 local_islands
 sign_change_up_positions
-first_failure_pair
+first_sign_change_pair
 margin_jump
 retention_drop
 continuation_drop
@@ -65,7 +65,9 @@ rows: 1024
 rows with positive pressure depths: 511
 rows with local islands: 3
 rows with sign-change-up positions: 4
-rows with positive blocks: 132
+rows with positive blocks length >= 1: 511
+rows with positive blocks length >= 2: 131
+rows with positive blocks length >= 4: 60
 max positive depth count: 8
 max local island count: 1
 max sign-change-up count: 1
@@ -83,6 +85,31 @@ These rows are the important obstruction witnesses.  They show again that
 pressure is not simply carrier nesting and does not support an unconditional
 prefix theorem.

+Checkpoint 131 refines this scan:
+
+```text
+first_sign_change_pair:
+  adjacent nonpositive -> positive pressure margin pair
+
+positive block:
+  maximal consecutive positive-depth run, length >= 1
+```
+
+It also adds aggregate tables by residual residue class.  The strongest visible
+pattern in the current scan is:
+
+```text
+frontier depth:
+  almost always depth 2
+
+long positive blocks:
+  concentrated in high all-ones-like residual classes,
+  especially residual 15 mod 16 and 31 mod 32
+
+sign-change-up:
+  rare, observed at depths 2 and 4
+```
+
 ## Lean Surface Added

 Checkpoint 130 adds only thin predicates and margin bridges:
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-131.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-131.md
new file mode 100644
index 00000000..b4d69e92
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-131.md
@@ -0,0 +1,202 @@
+# Report Petal 131
+
+## Summary
+
+Checkpoint 131 refines the pressure sign-pattern scan from checkpoint 130.
+
+Main changes:
+
+```text
+first_failure_pair -> first_sign_change_pair
+positive block definition fixed as length >= 1 consecutive positive-depth run
+aggregate correlation tables added
+island/sign-change rows clarified as adjacent sign-change witnesses
+```
+
+The scan now reports frontier depth and block length by residual residue class.
+The most visible pattern is that long positive blocks concentrate near
+all-ones-like residual classes such as `15 mod 16` and `31 mod 32`, while
+sign-change-up rows remain rare.
+
+## Python Scan Changes
+
+Updated:
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+```
+
+Regenerated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
+```
+
+New row fields:
+
+```text
+first_sign_change_pair
+residual_mod_16_first
+residual_mod_16_last
+residual_mod_16_mode
+residual_mod_32_first
+residual_mod_32_last
+residual_mod_32_mode
+max_positive_block_length
+```
+
+New aggregate tables:
+
+```text
+frontier_depth by residual_mod_16_first/mode
+frontier_depth by residual_mod_32_first/mode
+positive_block_length by residual_mod_16_first
+positive_block_length by residual_mod_32_first
+local_island rows by residual_mod_16_first
+sign-change-up rows by residual_mod_16_first
+sign-change-up depth counts
+```
+
+## Observed Results
+
+Run:
+
+```text
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
+  --max-n 2047 --steps 64 --r-start 2 --depth-len 10
+```
+
+Summary:
+
+```text
+rows: 1024
+rows with positive pressure depths: 511
+rows with local islands: 3
+rows with sign-change-up positions: 4
+rows with positive blocks length >= 1: 511
+rows with positive blocks length >= 2: 131
+rows with positive blocks length >= 4: 60
+positive block length counts:
+  1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3
+sign-change-up depth counts:
+  2:2; 4:2
+```
+
+Important reading:
+
+```text
+frontier depth:
+  almost always depth 2
+
+long positive blocks:
+  concentrated around high all-ones-like residual classes
+
+local islands:
+  rare but real
+```
+
+## Lean Surface
+
+Added:
+
+```lean
+sourcePressureMargin_lt_of_signChangeUp
+sourcePressurePositiveBlock_singleton
+sourcePressurePositiveBlock_of_forall_margin_pos
+existsSourcePressureLocalIslandBelow_of_lt
+existsSourcePressureFrontierBelow_of_lt
+sourcePressureSignChangeUp_of_localIsland
+```
+
+These are small API helpers for the checkpoint-130 predicates.  They do not
+introduce a global grid or monotonicity theorem.
+
+## Documentation Updates
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-PressureCorrelationScan-131.md
+```
+
+## Added Inference
+
+The scan suggests a more specific hypothesis:
+
+```text
+long positive pressure blocks track all-ones-like residual classes.
+```
+
+This is more promising than a generic pressure-prefix theorem.  The frontier is
+usually shallow, while the block length appears to encode deeper residue
+structure.
+
+The local-island rows still matter because they show the obstruction mechanism:
+
+```text
+retention can drop faster than continuation,
+causing an adjacent nonpositive -> positive margin sign change.
+```
+
+## Suggested Checkpoint 132
+
+Preferred next scan:
+
+```text
+block length by residual all-ones depth
+frontier depth by count of residual all-ones prefixes
+island depth by retention drop vs continuation drop
+```
+
+Lean-only fallback:
+
+```lean
+def SourcePressureMarginJumpUp
+def SourcePressureSignChangeUpWithJump
+```
+
+The scan route is stronger because it can identify which residue-depth feature
+should become a Lean predicate.
+
+## Verification
+
+Commands:
+
+```text
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 2047 --steps 64 --r-start 2 --depth-len 10
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean lean/dk_math/DkMath/Collatz/PetalBridge.lean
+git diff --check
+```
+
+Initial result:
+
+```text
+Python scan: passed
+PetalBridge build: passed
+Collatz2K26 build: passed
+Python py_compile: passed
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
diff --git a/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py b/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
index 49d7395d..b59bb81d 100644
--- a/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+++ b/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
@@ -18,6 +18,7 @@ from __future__ import annotations
 import argparse
 import csv
 from dataclasses import dataclass
+from collections import Counter, defaultdict
 from pathlib import Path


@@ -42,7 +43,14 @@ class PressureSignPatternRow:
     local_island_count: int
     sign_change_up_positions: str
     sign_change_up_count: int
-    first_failure_pair: str
+    first_sign_change_pair: str
+    residual_mod_16_first: int
+    residual_mod_16_last: int
+    residual_mod_16_mode: int
+    residual_mod_32_first: int
+    residual_mod_32_last: int
+    residual_mod_32_mode: int
+    max_positive_block_length: int
     max_margin_jump: int
     max_retention_drop: int
     max_continuation_drop: int
@@ -60,7 +68,19 @@ def join_pairs(values: list[tuple[int, int]]) -> str:


 def join_blocks(blocks: list[tuple[int, int]]) -> str:
-    return ";".join(f"{start}-{end}" if start != end else str(start) for start, end in blocks)
+    return ";".join(
+        f"{start}-{end}" if start != end else str(start) for start, end in blocks
+    )
+
+
+def mode_int(values: list[int]) -> int:
+    if not values:
+        return -1
+    counts = Counter(values)
+    return min(
+        counts,
+        key=lambda value: (-counts[value], value),
+    )


 def v2(n: int) -> int:
@@ -123,7 +143,7 @@ def consecutive_blocks(depths: list[int]) -> list[tuple[int, int]]:
     return blocks


-def first_failure_pair(depths: list[int], r_start: int) -> tuple[int, int] | None:
+def first_sign_change_pair(depths: list[int], r_start: int) -> tuple[int, int] | None:
     selected = set(depths)
     if not depths:
         return None
@@ -148,6 +168,9 @@ def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPat
     height_seq = heights_all[:steps]
     residual_shape_seq = labels[1 : steps + 1]
     first_failed_depth_seq = [height + 1 for height in height_seq]
+    residual_mod_8_seq = [value % 8 for value in residual_shape_seq]
+    residual_mod_16_seq = [value % 16 for value in residual_shape_seq]
+    residual_mod_32_seq = [value % 32 for value in residual_shape_seq]

     depths = list(range(r_start, r_start + depth_len))
     extended_depths = list(range(r_start, r_start + depth_len + 1))
@@ -172,7 +195,8 @@ def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPat
         for depth in depths
         if margins[depth] <= 0 and margins[depth + 1] > 0
     ]
-    failure_pair = first_failure_pair(positive_depths, r_start)
+    sign_change_pair = first_sign_change_pair(positive_depths, r_start)
+    block_lengths = [end - start + 1 for start, end in blocks]

     return PressureSignPatternRow(
         n=n,
@@ -182,9 +206,9 @@ def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPat
         height_seq=join_ints(height_seq),
         residual_shape_seq=join_ints(residual_shape_seq),
         first_failed_depth_seq=join_ints(first_failed_depth_seq),
-        residual_mod_8_seq=join_ints([value % 8 for value in residual_shape_seq]),
-        residual_mod_16_seq=join_ints([value % 16 for value in residual_shape_seq]),
-        residual_mod_32_seq=join_ints([value % 32 for value in residual_shape_seq]),
+        residual_mod_8_seq=join_ints(residual_mod_8_seq),
+        residual_mod_16_seq=join_ints(residual_mod_16_seq),
+        residual_mod_32_seq=join_ints(residual_mod_32_seq),
         positive_depths=join_ints(positive_depths),
         positive_blocks=join_blocks(blocks),
         positive_depth_count=len(positive_depths),
@@ -194,9 +218,16 @@ def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPat
         local_island_count=len(local_islands),
         sign_change_up_positions=join_ints(sign_change_up),
         sign_change_up_count=len(sign_change_up),
-        first_failure_pair=(
-            "" if failure_pair is None else f"{failure_pair[0]}->{failure_pair[1]}"
+        first_sign_change_pair=(
+            "" if sign_change_pair is None else f"{sign_change_pair[0]}->{sign_change_pair[1]}"
         ),
+        residual_mod_16_first=residual_mod_16_seq[0] if residual_mod_16_seq else -1,
+        residual_mod_16_last=residual_mod_16_seq[-1] if residual_mod_16_seq else -1,
+        residual_mod_16_mode=mode_int(residual_mod_16_seq),
+        residual_mod_32_first=residual_mod_32_seq[0] if residual_mod_32_seq else -1,
+        residual_mod_32_last=residual_mod_32_seq[-1] if residual_mod_32_seq else -1,
+        residual_mod_32_mode=mode_int(residual_mod_32_seq),
+        max_positive_block_length=max(block_lengths, default=0),
         max_margin_jump=max_adjacent_jump(margins, depths),
         max_retention_drop=max_adjacent_drop(retentions, depths),
         max_continuation_drop=max_adjacent_drop(continuations, depths),
@@ -225,12 +256,70 @@ def write_csv(rows: list[PressureSignPatternRow], path: Path) -> None:
             writer.writerow(row.__dict__)


+def table_count_by(
+    rows: list[PressureSignPatternRow],
+    key_name: str,
+    value_name: str,
+    only_positive: bool = False,
+) -> list[tuple[int, str]]:
+    bucket: dict[int, Counter[int]] = defaultdict(Counter)
+    for row in rows:
+        if only_positive and row.positive_depth_count == 0:
+            continue
+        key = getattr(row, key_name)
+        value = getattr(row, value_name)
+        if value >= 0:
+            bucket[key][value] += 1
+    return [
+        (key, ";".join(f"{value}:{count}" for value, count in sorted(counter.items())))
+        for key, counter in sorted(bucket.items())
+    ]
+
+
+def count_list_field(rows: list[PressureSignPatternRow], field_name: str) -> Counter[int]:
+    counter: Counter[int] = Counter()
+    for row in rows:
+        raw = getattr(row, field_name)
+        if not raw:
+            continue
+        for value in raw.split(";"):
+            if value:
+                counter[int(value)] += 1
+    return counter
+
+
+def markdown_kv_counter(counter: Counter[int]) -> str:
+    return "; ".join(f"{key}:{counter[key]}" for key in sorted(counter))
+
+
+def append_distribution_table(
+    lines: list[str],
+    title: str,
+    rows: list[tuple[int, str]],
+    key_label: str,
+    value_label: str,
+) -> None:
+    lines.extend(["", f"## {title}", "", f"| {key_label} | {value_label} |", "|---:|---|"])
+    if rows:
+        for key, value in rows:
+            lines.append(f"| {key} | {value} |")
+    else:
+        lines.append("| - | none |")
+
+
 def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
     path.parent.mkdir(parents=True, exist_ok=True)
     nonempty = [row for row in rows if row.positive_depth_count > 0]
     with_island = [row for row in rows if row.local_island_count > 0]
     with_sign_change = [row for row in rows if row.sign_change_up_count > 0]
-    block_rows = [row for row in rows if ";" in row.positive_blocks or "-" in row.positive_blocks]
+    block_rows_len_ge_1 = [row for row in rows if row.max_positive_block_length >= 1]
+    block_rows_len_ge_2 = [row for row in rows if row.max_positive_block_length >= 2]
+    block_rows_len_ge_4 = [row for row in rows if row.max_positive_block_length >= 4]
+    block_length_counts = Counter(
+        row.max_positive_block_length
+        for row in rows
+        if row.max_positive_block_length > 0
+    )
     max_positive = max((row.positive_depth_count for row in rows), default=0)
     max_islands = max((row.local_island_count for row in rows), default=0)
     max_sign_changes = max((row.sign_change_up_count for row in rows), default=0)
@@ -254,10 +343,14 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
         f"- rows with positive pressure depths: `{len(nonempty)}`",
         f"- rows with local islands: `{len(with_island)}`",
         f"- rows with sign-change-up positions: `{len(with_sign_change)}`",
-        f"- rows with positive blocks: `{len(block_rows)}`",
+        "- positive block definition: `maximal consecutive positive-depth run, length >= 1`",
+        f"- rows with positive blocks length >= 1: `{len(block_rows_len_ge_1)}`",
+        f"- rows with positive blocks length >= 2: `{len(block_rows_len_ge_2)}`",
+        f"- rows with positive blocks length >= 4: `{len(block_rows_len_ge_4)}`",
         f"- max positive depth count: `{max_positive}`",
         f"- max local island count: `{max_islands}`",
         f"- max sign-change-up count: `{max_sign_changes}`",
+        f"- positive block length counts: `{markdown_kv_counter(block_length_counts)}`",
         "",
         "## Top Positive-Depth Samples",
         "",
@@ -278,7 +371,7 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
             "",
             "## Local-Island Samples",
             "",
-            "| n | islands | first failure pair | sign-up | height seq | first-failed seq | residual mod 16 |",
+            "| n | islands | first sign-change pair | sign-up | height seq | first-failed seq | residual mod 16 |",
             "|---:|---|---|---|---|---|---|",
         ]
     )
@@ -286,7 +379,7 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
         for row in top_islands:
             lines.append(
                 "| "
-                f"{row.n} | {row.local_islands} | {row.first_failure_pair} | "
+                f"{row.n} | {row.local_islands} | {row.first_sign_change_pair} | "
                 f"{row.sign_change_up_positions} | {row.height_seq} | "
                 f"{row.first_failed_depth_seq} | {row.residual_mod_16_seq} |"
             )
@@ -330,6 +423,71 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
             "",
         ]
     )
+    append_distribution_table(
+        lines,
+        "Frontier Depth By Residual Mod 16 First",
+        table_count_by(rows, "residual_mod_16_first", "first_frontier_depth", True),
+        "residual mod 16 first",
+        "frontier depth counts",
+    )
+    append_distribution_table(
+        lines,
+        "Frontier Depth By Residual Mod 16 Mode",
+        table_count_by(rows, "residual_mod_16_mode", "first_frontier_depth", True),
+        "residual mod 16 mode",
+        "frontier depth counts",
+    )
+    append_distribution_table(
+        lines,
+        "Frontier Depth By Residual Mod 32 First",
+        table_count_by(rows, "residual_mod_32_first", "first_frontier_depth", True),
+        "residual mod 32 first",
+        "frontier depth counts",
+    )
+    append_distribution_table(
+        lines,
+        "Frontier Depth By Residual Mod 32 Mode",
+        table_count_by(rows, "residual_mod_32_mode", "first_frontier_depth", True),
+        "residual mod 32 mode",
+        "frontier depth counts",
+    )
+    append_distribution_table(
+        lines,
+        "Positive Block Length By Residual Mod 16 First",
+        table_count_by(rows, "residual_mod_16_first", "max_positive_block_length"),
+        "residual mod 16 first",
+        "max block length counts",
+    )
+    append_distribution_table(
+        lines,
+        "Positive Block Length By Residual Mod 32 First",
+        table_count_by(rows, "residual_mod_32_first", "max_positive_block_length"),
+        "residual mod 32 first",
+        "max block length counts",
+    )
+    append_distribution_table(
+        lines,
+        "Local Island Rows By Residual Mod 16 First",
+        table_count_by(with_island, "residual_mod_16_first", "local_island_count"),
+        "residual mod 16 first",
+        "local island count rows",
+    )
+    append_distribution_table(
+        lines,
+        "Sign-Change-Up Rows By Residual Mod 16 First",
+        table_count_by(with_sign_change, "residual_mod_16_first", "sign_change_up_count"),
+        "residual mod 16 first",
+        "sign-change-up count rows",
+    )
+    lines.extend(
+        [
+            "",
+            "## Sign-Change-Up Depth Counts",
+            "",
+            f"- depth counts: `{markdown_kv_counter(count_list_field(rows, 'sign_change_up_positions'))}`",
+            "",
+        ]
+    )
     path.write_text("\n".join(lines), encoding="utf-8")


diff --git a/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md b/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
index fde15131..0aca5765 100644
--- a/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
+++ b/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
@@ -4,10 +4,14 @@
 - rows with positive pressure depths: `511`
 - rows with local islands: `3`
 - rows with sign-change-up positions: `4`
-- rows with positive blocks: `132`
+- positive block definition: `maximal consecutive positive-depth run, length >= 1`
+- rows with positive blocks length >= 1: `511`
+- rows with positive blocks length >= 2: `131`
+- rows with positive blocks length >= 4: `60`
 - max positive depth count: `8`
 - max local island count: `1`
 - max sign-change-up count: `1`
+- positive block length counts: `1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3`

 ## Top Positive-Depth Samples

@@ -28,7 +32,7 @@

 ## Local-Island Samples

-| n | islands | first failure pair | sign-up | height seq | first-failed seq | residual mod 16 |
+| n | islands | first sign-change pair | sign-up | height seq | first-failed seq | residual mod 16 |
 |---:|---|---|---|---|---|---|
 | 1567 | 3 | 2->3 | 2 | 1;1;1;1;2;2;2;6;3;1;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;2;3;3;3;7;4;2;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 15;7;11;1;1;1;5;13;11;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
 | 1639 | 5 | 4->5 | 4 | 1;1;2;1;1;1;3;1;1;1;2;4;1;1;1;1;1;1;2;1;1;2;5;2;1;1;7;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;3;2;2;2;4;2;2;2;3;5;2;2;2;2;2;2;3;2;2;3;6;3;2;2;8;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 11;9;15;7;3;13;15;7;11;1;5;15;15;15;15;7;11;9;7;11;1;5;9;7;3;5;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
@@ -53,3 +57,113 @@ predicate.
 This is not evidence for an unconditional pressure-prefix theorem.  The
 presence of local islands and sign-change-up rows means pressure is a
 margin sign profile, not just carrier nesting.
+
+
+## Frontier Depth By Residual Mod 16 First
+
+| residual mod 16 first | frontier depth counts |
+|---:|---|
+| 1 | 2:57;3:1 |
+| 3 | 2:45 |
+| 5 | 2:39 |
+| 7 | 2:77 |
+| 9 | 2:62 |
+| 11 | 2:64 |
+| 13 | 2:53 |
+| 15 | 2:112;3:1 |
+
+## Frontier Depth By Residual Mod 16 Mode
+
+| residual mod 16 mode | frontier depth counts |
+|---:|---|
+| 1 | 2:493;3:2 |
+| 7 | 2:3 |
+| 15 | 2:13 |
+
+## Frontier Depth By Residual Mod 32 First
+
+| residual mod 32 first | frontier depth counts |
+|---:|---|
+| 1 | 2:32;3:1 |
+| 3 | 2:23 |
+| 5 | 2:23 |
+| 7 | 2:43 |
+| 9 | 2:42 |
+| 11 | 2:30 |
+| 13 | 2:20 |
+| 15 | 2:49;3:1 |
+| 17 | 2:25 |
+| 19 | 2:22 |
+| 21 | 2:16 |
+| 23 | 2:34 |
+| 25 | 2:20 |
+| 27 | 2:34 |
+| 29 | 2:33 |
+| 31 | 2:63 |
+
+## Frontier Depth By Residual Mod 32 Mode
+
+| residual mod 32 mode | frontier depth counts |
+|---:|---|
+| 1 | 2:493;3:2 |
+| 5 | 2:2 |
+| 7 | 2:4 |
+| 9 | 2:2 |
+| 15 | 2:2 |
+| 27 | 2:2 |
+| 31 | 2:4 |
+
+## Positive Block Length By Residual Mod 16 First
+
+| residual mod 16 first | max block length counts |
+|---:|---|
+| 1 | 0:72;1:50;2:3;3:1;4:4 |
+| 3 | 0:83;1:39;2:2;4:3;5:1 |
+| 5 | 0:89;1:34;2:1;4:4 |
+| 7 | 0:51;1:68;2:5;3:1;4:1;5:2 |
+| 9 | 0:65;1:45;2:6;3:2;4:3;5:4;8:2 |
+| 11 | 0:64;1:52;2:3;3:4;4:2;5:3 |
+| 13 | 0:75;1:43;2:4;3:3;4:2;5:1 |
+| 15 | 0:14;1:49;2:24;3:12;4:14;5:9;6:3;7:1;8:1 |
+
+## Positive Block Length By Residual Mod 32 First
+
+| residual mod 32 first | max block length counts |
+|---:|---|
+| 1 | 0:33;1:27;2:3;3:1;4:2 |
+| 3 | 0:41;1:21;4:2 |
+| 5 | 0:42;1:18;2:1;4:4 |
+| 7 | 0:21;1:38;2:3;3:1;5:1 |
+| 9 | 0:22;1:32;2:3;3:2;4:2;5:2;8:1 |
+| 11 | 0:35;1:28;4:2 |
+| 13 | 0:44;1:16;2:2;3:1;4:1 |
+| 15 | 0:14;1:36;2:10;3:1;4:1;5:2 |
+| 17 | 0:39;1:23;4:2 |
+| 19 | 0:42;1:18;2:2;4:1;5:1 |
+| 21 | 0:47;1:16 |
+| 23 | 0:30;1:30;2:2;4:1;5:1 |
+| 25 | 0:43;1:13;2:3;4:1;5:2;8:1 |
+| 27 | 0:29;1:24;2:3;3:4;5:3 |
+| 29 | 0:31;1:27;2:2;3:2;4:1;5:1 |
+| 31 | 1:13;2:14;3:11;4:13;5:7;6:3;7:1;8:1 |
+
+## Local Island Rows By Residual Mod 16 First
+
+| residual mod 16 first | local island count rows |
+|---:|---|
+| 7 | 1:1 |
+| 11 | 1:1 |
+| 15 | 1:1 |
+
+## Sign-Change-Up Rows By Residual Mod 16 First
+
+| residual mod 16 first | sign-change-up count rows |
+|---:|---|
+| 1 | 1:1 |
+| 7 | 1:1 |
+| 11 | 1:1 |
+| 15 | 1:1 |
+
+## Sign-Change-Up Depth Counts
+
+- depth counts: `2:2; 4:2`
````
`````
