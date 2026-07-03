# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 17ec543408a393b7570185150c19afa659d69798

## Report

Checkpoint 132 を実装しました。

Python scan に `all_ones_depth(x) = v2(x + 1)` を追加し、`residual_all_ones_depth_seq`、first/last/mode/max、`ge_4/ge_5/ge_6` counts、sign-change-up の原因分類を出すようにしました。生成結果も再作成済みです。

Lean 側には [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean#L158) で `ResidualAllOnesDepth`、`orbitWindowResidualAllOnesDepth`、`orbitWindowResidualAllOnesDepthSeq` を追加し、[length/get? 補題](/lean/dk_math/DkMath/Collatz/PetalBridge.lean#L941) まで通しました。重い `d ≤ depth -> x % 2^d = 2^d - 1` はまだ置いていません。

観測結果は [report-petal-132.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-132.md#L1) と [Collatz-PressureAllOnesCorrelationScan-132.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureAllOnesCorrelationScan-132.md#L1) に整理しました。要点は、`mode` は全行で浅い `1` なのに、`max all-ones depth` が positive block 長と強く連動していることです。つまり「窓全体が all-ones 的」ではなく、「窓内に深い all-ones excursion が出る」ことが圧力 block の主信号に見えます。

検証:

- `python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 2047 --steps 64 --r-start 2 --depth-len 10`
- `python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py`
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath.Collatz.Collatz2K26`
- Collatz 対象 no-sorry scan
- `git diff --check`

すべて通過。既存の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告は引き続き出ますが、今回 Collatz 側に新しい `sorry` は入れていません。

## Review

## 状況分析

Checkpoint `132` は、かなり重要な観測 checkpoint になっている。

前回までの `residual_mod_16 / residual_mod_32` は、あくまで「all-ones-like residue class」の代理指標だった。今回、Python scan に直接

```text
all_ones_depth(x) = v2(x + 1)
```

を導入し、Lean 側にも `ResidualAllOnesDepth`、`orbitWindowResidualAllOnesDepth`、`orbitWindowResidualAllOnesDepthSeq` と、その `length/get?/take` API まで入った。重い modulo bridge はまだ入れず、観測 profile だけに留めているのも良い判断じゃ。

今回の最大の発見はこれ。

```text
mode は全行で浅い 1。
しかし max all-ones depth は positive block length と強く連動する。
```

つまり、pressure block は「窓全体が all-ones 的」だから出るのではない。
**窓の中に深い all-ones excursion が一度でも現れる**ことが、長い positive block の主信号に見える。

これはかなり大きい。

## レビュー

## 良い点

第一に、`ResidualAllOnesDepth` を Lean 側に入れたのが良い。

```lean
def ResidualAllOnesDepth (x : ℕ) : ℕ :=
  v2 (x + 1)
```

これにより、Python の観測量と Lean の theorem surface が同じ名前で対応するようになった。`15 mod 16` や `31 mod 32` を個別に追うより、低位 bit が何段 all-ones に乗っているかを直接見る方が、今後の一般化に向いている。

第二に、`orbitWindowResidualAllOnesDepthSeq` を profile として置いた点が良い。

これはまだ `ShapePressureGrid` ではない。
あくまで time axis \(i\) 上の residual profile じゃ。

```text
time index i:
  residual_i
  all_ones_depth(residual_i)
```

pressure depth \(j\) とはまだ混ぜていない。
この慎重さは正しい。

第三に、scan 結果が非常に示唆的じゃ。

```text
all-ones depth mode counts:
  1:1024
```

これは、窓の典型状態は浅いということを示している。
それなのに、

```text
max all-ones depth 10/11:
  block length 8
```

のように、最大値は block length と結びついている。

つまり、平均・mode ではなく、**最大 excursion** が効いている。

第四に、sign-change-up の原因分類で `retention_drop_dominant:4` が出たのも良い。

これで local island / sign-change-up は、

```text
深い continuation が突然増える

ではなく、

浅い retention が急に落ちることで相対的に continuation が勝つ
```

という読みが強まった。

## 注意点

次の注意点は、`max all-ones depth` が強いからといって、まだ

```text
max all-ones depth >= d -> positive block length >= f(d)
```

のような定理へ飛ばないことじゃ。

今の scan 範囲は、

```text
odd n <= 2047
steps = 64
depths = 2..11
```

なので、まずは範囲を広げたときも同じ傾向が保たれるかを見るべきじゃ。

特に注意すべきは、最大値指標は外れ値に敏感なこと。
`max` が効いているのは本当に構造なのか、それとも短い窓でたまたま目立っているだけなのかを、次 checkpoint で確認したい。

そのため次は、

```text
max_n を増やす
steps を変える
depth range を変える
threshold count を見る
```

が必要になる。

## 解説

ここまでの流れを数式的に言うと、residual shape \(q_i\) に対して

```text
ResidualAllOnesDepth(q_i) = v2(q_i + 1)
```

を見ている。

これは、

```text
q_i ≡ 2^d - 1 mod 2^d
```

がどこまで続くかを測る量じゃ。

例えば、

```text
q_i = 15:
  15 + 1 = 16
  v2(16) = 4

q_i = 31:
  31 + 1 = 32
  v2(32) = 5
```

だから `ResidualAllOnesDepth` は、PetalBridge で見ている all-ones carrier の深さと直結する。

今回の発見は、

```text
窓内に深い all-ones residual が出る
  -> deep continuation channel が残りやすい
  -> pressure margin が連続して正になりやすい
  -> positive block が長くなる
```

という流れじゃ。

一方、local island は別の現象に見える。

```text
positive block:
  deep all-ones excursion による大域的構造

local island:
  retention / continuation の隣接減衰差による局所的構造
```

つまり、pressure sign profile は一枚岩ではない。
ここで二つに割るのがよい。

```text
ResidualAllOnesProfile
PressureDecayProfile
```

これは `ShapePressureGrid` の前段としてかなり自然じゃ。

## 次の指示

Checkpoint `133` は、いきなり full grid ではなく、次の二本を薄く進めるのが良い。

```text
Route A:
  ResidualAllOnesProfile を profile-level predicate へ育てる

Route B:
  PressureDecayProfile を sign-change-up / island の原因分析へ育てる
```

## Checkpoint 133 推奨内容

## 1. Python scan の頑健性確認

まず scan 範囲を広げる。

候補：

```text
--max-n 8191 --steps 64 --r-start 2 --depth-len 10
--max-n 8191 --steps 128 --r-start 2 --depth-len 10
--max-n 16383 --steps 64 --r-start 2 --depth-len 12
```

見たいもの：

```text
max all-ones depth と max positive block length の関係が保たれるか

mode が依然として 1 に偏るか

sign-change-up は依然として retention_drop_dominant か

local island の件数はどう増えるか

positive block length 8 以上が出るか
```

## 2. threshold count を使う

`max` だけでなく、threshold count も見る。

すでに、

```text
count_all_ones_depth_ge_4
count_all_ones_depth_ge_5
count_all_ones_depth_ge_6
```

がある。次はこれを block length と集計する。

追加 table：

```text
positive_block_length by count_all_ones_depth_ge_4
positive_block_length by count_all_ones_depth_ge_5
positive_block_length by count_all_ones_depth_ge_6

frontier_depth by count_all_ones_depth_ge_4
local_island_count by count_all_ones_depth_ge_4
sign_change_up_count by count_all_ones_depth_ge_4
```

これで、

```text
一度だけ深い excursion があれば十分なのか
深い excursion の回数が効くのか
```

が見える。

## 3. Lean 側に profile-level predicate を置く

重い modulo bridge ではなく、まず薄い predicate がよい。

```lean
def WindowHasResidualAllOnesDepthAtLeast
    (n : OddNat) (k d : ℕ) : Prop :=
  ∃ i, i < k ∧ d ≤ orbitWindowResidualAllOnesDepth n i
```

さらに bounded / count はまだ後でよい。
まず存在述語。

対応する constructor：

```lean
theorem windowHasResidualAllOnesDepthAtLeast_of_lt
    (n : OddNat) (k d i : ℕ)
    (hi : i < k)
    (hdepth : d ≤ orbitWindowResidualAllOnesDepth n i) :
    WindowHasResidualAllOnesDepthAtLeast n k d := by
  exact ⟨i, hi, hdepth⟩
```

## 4. residual all-ones depth と shifted label の bridge

すでに

```text
orbitWindowResidualShape n i = oddOrbitLabel n (i + 1)
```

がある。
だから all-ones depth でも次の補題が欲しい。

```lean
theorem orbitWindowResidualAllOnesDepth_eq_nextLabel
    (n : OddNat) (i : ℕ) :
    orbitWindowResidualAllOnesDepth n i =
      ResidualAllOnesDepth (oddOrbitLabel n (i + 1)) := by
  unfold orbitWindowResidualAllOnesDepth
  rw [orbitWindowResidualShape_eq_oddOrbitLabel_succ]
```

これは軽くて強い。
「residual all-ones depth は次ラベルの all-ones depth」と読める。

## 5. PressureDecayProfile の薄い定義

Python で出した retention / continuation drop を Lean 側にも薄く置くなら、まず margin だけでなく mass drop の定義が欲しい。

実際の既存名に合わせる必要があるが、仮に `sourceRetentionMass` / `sourceContinuationMass` 相当があるなら：

```lean
def SourcePressureRetentionDrop
    (n : OddNat) (k r j : ℕ) : ℤ :=
  SourceRetentionMassInt n k (r + j) -
    SourceRetentionMassInt n k (r + j + 1)
```

```lean
def SourcePressureContinuationDrop
    (n : OddNat) (k r j : ℕ) : ℤ :=
  SourceContinuationMassInt n k (r + j) -
    SourceContinuationMassInt n k (r + j + 1)
```

ただし、mass が ℕ なら subtraction が面倒なので、最初は Prop の方が安全。

```lean
def SourcePressureRetentionDropDominant
    (n : OddNat) (k r j : ℕ) : Prop :=
  2 * SourcePressureContinuationDropNat n k r j <
    SourcePressureRetentionDropNat n k r j
```

これは既存 API を調べてからでよい。
Lean 側で急がないなら、Python の分類だけで十分。

## 一歩先ゆく推論

いま見えている最重要仮説はこれじゃ。

```text
positive block length は、window 内の max residual all-ones depth の関数に近い。
```

ただし、完全な関数ではなく、おそらく下限・上限関係じゃ。

直感的には、

```text
max all-ones depth が浅い:
  positive block は出にくい

max all-ones depth が深い:
  positive block は長くなりやすい
```

であって、

```text
max depth = d なら block length = d - c
```

のような厳密等式ではないだろう。

なぜなら pressure margin には retention 側も入るからじゃ。

```text
margin = 2 * continuation - retention
```

deep all-ones は continuation を支える。
しかし retention がどれだけ残るかで、positive depth の長さは変わる。

だから次の二成分モデルになる。

```text
positive block length
  ≈ continuation support from max all-ones excursion
    minus retention obstruction
```

これはかなり DkMath らしい。

```text
Big:
  all-ones excursion / continuation supply

Gap:
  retention obstruction

Observed pressure:
  Big - Gap
```

という形じゃな。

## さらなる次の一手

Checkpoint `133` で頑健性確認が通ったら、Checkpoint `134` では次が候補になる。

## 1. `ResidualAllOnesProfile` モジュール的区画

`PetalBridge` が肥大化しているなら、そろそろ section を明確に分ける。

```text
-- Residual all-ones profile
-- Pressure decay profile
-- Future shape-pressure grid handles
```

まだ別ファイルに切るほどではないが、section 整理は有効。

## 2. `WindowHasResidualAllOnesDepthAtLeast` と positive block の関係を観測定理へ

まだ証明ではなく、interface のみ。

```lean
def WindowHasDeepResidualAllOnesExcursion
    (n : OddNat) (k d : ℕ) : Prop :=
  WindowHasResidualAllOnesDepthAtLeast n k d
```

将来の theorem 形はこうなるかもしれない。

```lean
theorem positiveBlock_of_deepResidualAllOnes_and_lowRetention
    ...
```

ただしこれはまだ早い。
まずは predicate 名だけで良い。

## 3. sign-change-up を decay imbalance として読む

すでに `sourcePressureSignChangeUp_of_localIsland` がある。
次は、その sign-change-up に「strict margin jump」が付くことは閉じている。
その先は、drop 分解じゃ。

Python で retention_drop_dominant が続くなら、Lean 側に、

```lean
def SourcePressureRetentionDropDominantAtSignChange
```

を置く価値が出る。

## 賢狼が試して欲しい実験補題

## 実験 A: residual all-ones depth equals next label depth

```lean
theorem orbitWindowResidualAllOnesDepth_eq_nextLabel
    (n : OddNat) (i : ℕ) :
    orbitWindowResidualAllOnesDepth n i =
      ResidualAllOnesDepth (oddOrbitLabel n (i + 1)) := by
  unfold orbitWindowResidualAllOnesDepth
  rw [orbitWindowResidualShape_eq_oddOrbitLabel_succ]
```

## 実験 B: residual all-ones depth seq get? shifted label

```lean
theorem orbitWindowResidualAllOnesDepthSeq_get?_eq_some_nextLabel
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowResidualAllOnesDepthSeq n k)[i]? =
      some (ResidualAllOnesDepth (oddOrbitLabel n (i + 1))) := by
  rw [orbitWindowResidualAllOnesDepthSeq_get?_eq_some n hi]
  rw [orbitWindowResidualAllOnesDepth_eq_nextLabel]
```

## 実験 C: window has all-ones depth at least

```lean
def WindowHasResidualAllOnesDepthAtLeast
    (n : OddNat) (k d : ℕ) : Prop :=
  ∃ i, i < k ∧ d ≤ orbitWindowResidualAllOnesDepth n i
```

## 実験 D: constructor

```lean
theorem windowHasResidualAllOnesDepthAtLeast_of_lt
    (n : OddNat) (k d i : ℕ)
    (hi : i < k)
    (hdepth : d ≤ orbitWindowResidualAllOnesDepth n i) :
    WindowHasResidualAllOnesDepthAtLeast n k d := by
  exact ⟨i, hi, hdepth⟩
```

## 実験 E: monotonicity in threshold

```lean
theorem windowHasResidualAllOnesDepthAtLeast_of_le
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e)
    (h : WindowHasResidualAllOnesDepthAtLeast n k e) :
    WindowHasResidualAllOnesDepthAtLeast n k d := by
  rcases h with ⟨i, hi, he⟩
  exact ⟨i, hi, le_trans hde he⟩
```

これはかなり軽くて、threshold predicate として便利じゃ。

## 実験 F: sign-change-up with local island left edge already implies strict jump

既に `sourcePressureMargin_lt_of_signChangeUp` があるので、local island から直接版。

```lean
theorem sourcePressureMargin_lt_of_localIsland_left
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureMarginInt n k (r + (j - 1)) <
      SourcePressureMarginInt n k (r + (j - 1) + 1) := by
  exact sourcePressureMargin_lt_of_signChangeUp n k r (j - 1)
    (sourcePressureSignChangeUp_of_localIsland n k r j hisland)
```

## 実験 G: Python robustness runs

```text
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 8191 --steps 64 --r-start 2 --depth-len 10

python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 8191 --steps 128 --r-start 2 --depth-len 10

python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 16383 --steps 64 --r-start 2 --depth-len 12
```

出力は別名にするのがよい。

```text
pressure_sign_pattern_scan_8191_k64.md
pressure_sign_pattern_scan_8191_k128.md
pressure_sign_pattern_scan_16383_k64_d12.md
```

## Python 側の次観測

Checkpoint `133` の summary schema。

```text
# Pressure All-Ones Robustness Scan

## Parameters
max_n:
steps:
r_start:
depth_len:

## Summary
rows:
rows_with_positive_depths:
rows_with_block_len_ge_2:
rows_with_block_len_ge_4:
rows_with_block_len_ge_8:
rows_with_local_islands:
rows_with_sign_change_up:

## All-Ones Excursion Signal
max_all_ones_depth_counts:
positive_block_length_by_max_all_ones_depth:
positive_block_length_by_count_ge4:
positive_block_length_by_count_ge5:
positive_block_length_by_count_ge6:

## Robustness Comparison
compare_to_2047_k64:
  same mode shallow?
  same retention_drop_dominant?
  same block-depth relation?

## Sign-Change Cause
cause_counts:
retention_drop_dominant_examples:
continuation_hold_examples:
balanced_examples:
unclear_examples:

## Representative Rows
longest_positive_block_rows:
deepest_all_ones_excursion_rows:
local_island_rows:
largest_retention_drop_rows:
```

## Codex への次指示まとめ

```text
Checkpoint 133:
Do not build full ShapePressureGrid yet.

Primary goal:
  Validate the checkpoint-132 hypothesis on larger scans:
    long positive pressure blocks track max residual all-ones depth,
    while sign-change-up rows are retention-drop dominated.

Python:
  Run robustness scans:
    max_n 8191, steps 64
    max_n 8191, steps 128
    max_n 16383, steps 64, depth_len 12
  Add aggregate tables:
    positive_block_length by residual_all_ones_depth_max
    positive_block_length by count_all_ones_depth_ge_4/ge_5/ge_6
    sign_change cause counts
    local island rows by all-ones max

Lean:
  Add only thin profile predicates:
    WindowHasResidualAllOnesDepthAtLeast
    windowHasResidualAllOnesDepthAtLeast_of_lt
    windowHasResidualAllOnesDepthAtLeast_of_le
    orbitWindowResidualAllOnesDepth_eq_nextLabel
    orbitWindowResidualAllOnesDepthSeq_get?_eq_some_nextLabel

Optional:
    sourcePressureMargin_lt_of_localIsland_left

Do not:
  introduce Real.log
  claim pressure prefix
  define full ShapePressureGrid
  collapse time index i and pressure depth j
```

## 総括

Checkpoint `132` は成功じゃ。

いま見えたことは、かなりはっきりしている。

```text
positive block は、窓内の deep all-ones excursion に反応する。
mode は浅いので、窓全体の平均状態ではない。
sign-change-up は、この scan では retention_drop_dominant。
```

つまり、次に作るべき大きな構造は `ShapePressureGrid` ではなく、その一歩手前の二枚じゃ。

```text
ResidualAllOnesProfile:
  time axis 上の deep all-ones excursion

PressureDecayProfile:
  depth axis 上の retention/continuation decay imbalance
```

この二枚を別々に固めてから、初めて grid に重ねる。
これが次の正着じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index cb750c91..1c8fb374 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -143,6 +143,42 @@ extractions.
 noncomputable def orbitWindowResidualShapeSeq (n : OddNat) (k : ℕ) : List ℕ :=
   (List.range k).map (orbitWindowResidualShape n)

+/--
+Low-bit all-ones depth of a natural residual shape.
+
+This is the direct Lean counterpart of the checkpoint-132 scan observable:
+
+```text
+all_ones_depth x = v2 (x + 1)
+```
+
+It measures how long the low-bit suffix of `x` stays in the all-ones channel:
+`1`, `3`, `7`, `15`, `31`, ...
+-/
+def ResidualAllOnesDepth (x : ℕ) : ℕ :=
+  v2 (x + 1)
+
+/--
+All-ones depth of the residual shape at a window index.
+
+This keeps the time index `i` separate from pressure depth `j`.  It is an
+observable profile, not a pressure-prefix theorem.
+-/
+noncomputable def orbitWindowResidualAllOnesDepth
+    (n : OddNat) (i : ℕ) : ℕ :=
+  ResidualAllOnesDepth (orbitWindowResidualShape n i)
+
+/--
+Ordered all-ones-depth profile of the residual shapes in a finite orbit window.
+
+Checkpoint 132 adds this thin profile before introducing any heavier grid:
+the current experiment asks whether positive pressure blocks are explained by
+concentration in deep all-ones residual channels.
+-/
+noncomputable def orbitWindowResidualAllOnesDepthSeq
+    (n : OddNat) (k : ℕ) : List ℕ :=
+  (List.range k).map (orbitWindowResidualAllOnesDepth n)
+
 /--
 First failed power-of-two alignment depth at the `i`-th observed odd label.

@@ -898,6 +934,46 @@ theorem orbitWindowResidualShapeSeq_take_get?_eq_some
   rw [List.getElem?_take_of_lt hi]
   exact orbitWindowResidualShapeSeq_get?_eq_some n (Nat.lt_of_lt_of_le hi hr)

+/--
+The ordered all-ones-depth residual profile has length equal to the window
+size.
+-/
+theorem orbitWindowResidualAllOnesDepthSeq_length
+    (n : OddNat) (k : ℕ) :
+    (orbitWindowResidualAllOnesDepthSeq n k).length = k := by
+  simp [orbitWindowResidualAllOnesDepthSeq]
+
+/--
+Reading the all-ones-depth residual profile at an in-window time recovers the
+pointwise all-ones-depth observation.
+-/
+theorem orbitWindowResidualAllOnesDepthSeq_get?_eq_some
+    (n : OddNat) {i k : ℕ} (hi : i < k) :
+    (orbitWindowResidualAllOnesDepthSeq n k)[i]? =
+      some (orbitWindowResidualAllOnesDepth n i) := by
+  simp [orbitWindowResidualAllOnesDepthSeq, hi]
+
+/--
+The prefix of the all-ones-depth residual profile has length `r` when `r` lies
+inside the window.
+-/
+theorem orbitWindowResidualAllOnesDepthSeq_take_length
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    ((orbitWindowResidualAllOnesDepthSeq n k).take r).length = r := by
+  simp [orbitWindowResidualAllOnesDepthSeq_length, Nat.min_eq_left hr]
+
+/--
+Reading a prefix of the all-ones-depth residual profile recovers the same
+pointwise observation while the index remains inside the prefix.
+-/
+theorem orbitWindowResidualAllOnesDepthSeq_take_get?_eq_some
+    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
+    ((orbitWindowResidualAllOnesDepthSeq n k).take r)[i]? =
+      some (orbitWindowResidualAllOnesDepth n i) := by
+  rw [List.getElem?_take_of_lt hi]
+  exact orbitWindowResidualAllOnesDepthSeq_get?_eq_some n
+    (Nat.lt_of_lt_of_le hi hr)
+
 /--
 First-failed-depth profile over the first `k` observed odd labels.
 -/
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index b4a3464b..40689efe 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -173,6 +173,10 @@ ExistsSourcePressureLocalIslandBelow
 existsSourcePressureLocalIslandBelow_iff_margin
 ExistsSourcePressureFrontierBelow
 existsSourcePressureFrontierBelow_iff_margin
+ResidualAllOnesDepth
+orbitWindowResidualAllOnesDepth
+orbitWindowResidualAllOnesDepthSeq
+orbitWindowResidualAllOnesDepthSeq_get?_eq_some
 sourcePressureMargin_lt_of_signChangeUp
 sourcePressurePositiveBlock_singleton
 sourcePressurePositiveBlock_of_forall_margin_pos
@@ -238,6 +242,7 @@ docs/Collatz-ResidualShapeSequence-128.md
 docs/Collatz-FirstFailedDepthSequence-129.md
 docs/Collatz-PressureSignPatternScan-130.md
 docs/Collatz-PressureCorrelationScan-131.md
+docs/Collatz-PressureAllOnesCorrelationScan-132.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index bd340c71..043bda6f 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -326,6 +326,31 @@ positive block = maximal consecutive positive-depth run, length >= 1
 It also adds aggregate correlation tables for frontier depth, block length,
 local islands, and sign-change-up rows by residual residue class.

+Checkpoint 132 replaces the residue-class proxy with a direct all-ones-depth
+profile:
+
+```lean
+ResidualAllOnesDepth
+orbitWindowResidualAllOnesDepth
+orbitWindowResidualAllOnesDepthSeq
+orbitWindowResidualAllOnesDepthSeq_length
+orbitWindowResidualAllOnesDepthSeq_get?_eq_some
+orbitWindowResidualAllOnesDepthSeq_take_length
+orbitWindowResidualAllOnesDepthSeq_take_get?_eq_some
+```
+
+The corresponding Python observable is:
+
+```text
+all_ones_depth residual = v2 (residual + 1)
+```
+
+This is intentionally a profile, not a grid.  The time index `i` remains the
+index of a residual shape in the orbit window, while pressure depth `j` remains
+the index of a margin comparison.  The checkpoint-132 data says that long
+positive blocks are better explained by the maximum all-ones depth seen inside
+the window than by the first or modal residue alone.
+
 ## Residue Counts

 Named residue counts exist for low layers:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 2c4082d6..4b5e6fd5 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -262,6 +262,49 @@ The aggregate tables suggest frontier depth is almost always `2`, while longer
 positive blocks are visibly concentrated in high all-ones residual classes such
 as residual `15 mod 16` and `31 mod 32`.

+Checkpoint 132 replaces the proxy residue-class question with the direct
+all-ones-depth observable:
+
+```text
+ResidualAllOnesDepth x = v2 (x + 1)
+orbitWindowResidualAllOnesDepth n i
+orbitWindowResidualAllOnesDepthSeq n k
+```
+
+The Python scan now records `residual_all_ones_depth_seq` plus
+first/last/mode/max summaries and all-ones-depth threshold counts.
+
+Observed from the same `odd n <= 2047`, `steps = 64`, depths `2..11` scan:
+
+```text
+all-ones depth first counts:
+  1:513; 2:256; 3:128; 4:64; 5:32; 6:16; 7:8; 8:4; 9:2; 10:1
+
+all-ones depth mode counts:
+  1:1024
+
+all-ones depth max counts:
+  1:54; 2:156; 3:240; 4:83; 5:36; 6:391; 7:34; 8:25; 9:2; 10:1; 11:2
+
+sign-change cause counts:
+  retention_drop_dominant:4
+```
+
+The main reading is now sharper:
+
+```text
+long positive pressure blocks track deep max all-ones depth
+the mode is always shallow, so first/mode alone misses the window concentration
+local sign-change-up rows are retention-drop dominated in this scan
+```
+
+This supports a two-profile route before any full `ShapePressureGrid`:
+
+```text
+ResidualAllOnesProfile
+PressureDecayProfile
+```
+
 The first theorem set is deliberately thin:

 ```lean
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureAllOnesCorrelationScan-132.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureAllOnesCorrelationScan-132.md
new file mode 100644
index 00000000..fa467f42
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureAllOnesCorrelationScan-132.md
@@ -0,0 +1,204 @@
+# Collatz Pressure All-Ones Correlation Scan - Checkpoint 132
+
+Checkpoint 132 tests the hypothesis left by checkpoint 131:
+
+```text
+long positive pressure blocks are explained by residual all-ones depth
+```
+
+Checkpoint 131 only used proxy residue features such as `15 mod 16` and
+`31 mod 32`.  Checkpoint 132 measures the feature directly.
+
+## Observable
+
+The Python scan now records:
+
+```text
+all_ones_depth(x) = v2 (x + 1)
+```
+
+This is the low-bit all-ones suffix length:
+
+```text
+1  -> 1 mod 2
+3  -> 2
+7  -> 3
+15 -> 4
+31 -> 5
+```
+
+New row fields:
+
+```text
+residual_all_ones_depth_seq
+residual_all_ones_depth_first
+residual_all_ones_depth_last
+residual_all_ones_depth_mode
+residual_all_ones_depth_max
+count_all_ones_depth_ge_4
+count_all_ones_depth_ge_5
+count_all_ones_depth_ge_6
+sign_change_cause_labels
+sign_change_drop_details
+```
+
+## Scan
+
+Command:
+
+```text
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
+  --max-n 2047 --steps 64 --r-start 2 --depth-len 10
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
+```
+
+## Summary
+
+The global counts remain stable:
+
+```text
+rows: 1024
+rows with positive pressure depths: 511
+rows with local islands: 3
+rows with sign-change-up positions: 4
+positive block length counts:
+  1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3
+sign-change-up depth counts:
+  2:2; 4:2
+```
+
+The new all-ones-depth counts are:
+
+```text
+all-ones depth first counts:
+  1:513; 2:256; 3:128; 4:64; 5:32; 6:16; 7:8; 8:4; 9:2; 10:1
+
+all-ones depth mode counts:
+  1:1024
+
+all-ones depth max counts:
+  1:54; 2:156; 3:240; 4:83; 5:36; 6:391; 7:34; 8:25; 9:2; 10:1; 11:2
+```
+
+## Main Pattern
+
+The strongest table is `positive_block_length by residual_all_ones_depth_max`:
+
+```text
+max depth 1:
+  block length 0 only
+
+max depth 2:
+  block length 0 only
+
+max depth 3:
+  almost all block length 0, only a few length 1
+
+max depth 6:
+  mostly length 1, with some length 2-4
+
+max depth 8:
+  block length 4-6
+
+max depth 10/11:
+  block length 8
+```
+
+So the checkpoint-131 residue observation was not accidental.  The direct
+feature is:
+
+```text
+deep max all-ones residual depth in the window
+```
+
+not merely the first residue or modal residue.
+
+The mode is actually always shallow in this scan:
+
+```text
+all-ones depth mode counts:
+  1:1024
+```
+
+This means the important signal is not the common state of the whole window.
+It is the existence of a deep all-ones excursion inside the window.
+
+## Sign-Change Cause
+
+The scan also classifies upward pressure sign changes using adjacent retention
+and continuation drops.
+
+Observed:
+
+```text
+sign-change cause counts:
+  retention_drop_dominant:4
+```
+
+This supports the two-component reading:
+
+```text
+global block behavior:
+  explained by residual all-ones concentration
+
+local island behavior:
+  explained by retention/continuation adjacent decay imbalance
+```
+
+This is still observational.  It is not a global monotonicity theorem.
+
+## Lean Surface
+
+Checkpoint 132 adds only the thin profile skeleton:
+
+```lean
+ResidualAllOnesDepth
+orbitWindowResidualAllOnesDepth
+orbitWindowResidualAllOnesDepthSeq
+orbitWindowResidualAllOnesDepthSeq_length
+orbitWindowResidualAllOnesDepthSeq_get?_eq_some
+orbitWindowResidualAllOnesDepthSeq_take_length
+orbitWindowResidualAllOnesDepthSeq_take_get?_eq_some
+```
+
+The heavy bridge
+
+```text
+d <= ResidualAllOnesDepth x
+  -> x % 2^d = 2^d - 1
+```
+
+is deliberately postponed.  The current checkpoint only fixes the observable
+profile needed to read the scan data.
+
+## Next Work
+
+Checkpoint 133 should avoid a full `ShapePressureGrid` for now.
+
+The next useful thin layers are:
+
+```text
+ResidualAllOnesProfile:
+  profile-level predicates around max all-ones depth and threshold counts
+
+PressureDecayProfile:
+  adjacent retention/continuation drop predicates around sign-change-up rows
+```
+
+Candidate Lean names:
+
+```lean
+def WindowHasResidualAllOnesDepthAtLeast
+def SourcePressureRetentionDrop
+def SourcePressureContinuationDrop
+def SourcePressureSignChangeUpWithDrop
+```
+
+The scan route suggests that positive pressure blocks and local pressure
+islands should be treated as two related but distinct phenomena.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-132.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-132.md
new file mode 100644
index 00000000..67566f94
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-132.md
@@ -0,0 +1,226 @@
+# Report Petal 132
+
+## Summary
+
+Checkpoint 132 continues the scan route from checkpoint 131.
+
+Primary question:
+
+```text
+Can long positive pressure blocks be explained by residual all-ones depth?
+```
+
+Result:
+
+```text
+Yes, observationally.
+```
+
+The prior `15 mod 16` / `31 mod 32` signal was a proxy.  The clearer feature is
+the maximum all-ones depth seen inside the residual-shape window:
+
+```text
+all_ones_depth(residual) = v2(residual + 1)
+```
+
+## Python Changes
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
+residual_all_ones_depth_seq
+residual_all_ones_depth_first
+residual_all_ones_depth_last
+residual_all_ones_depth_mode
+residual_all_ones_depth_max
+count_all_ones_depth_ge_4
+count_all_ones_depth_ge_5
+count_all_ones_depth_ge_6
+sign_change_cause_labels
+sign_change_drop_details
+```
+
+The scan also classifies upward pressure sign changes using adjacent retention
+and continuation drops.
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
+positive block length counts:
+  1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3
+sign-change-up depth counts:
+  2:2; 4:2
+```
+
+All-ones-depth counts:
+
+```text
+all-ones depth first counts:
+  1:513; 2:256; 3:128; 4:64; 5:32; 6:16; 7:8; 8:4; 9:2; 10:1
+
+all-ones depth mode counts:
+  1:1024
+
+all-ones depth max counts:
+  1:54; 2:156; 3:240; 4:83; 5:36; 6:391; 7:34; 8:25; 9:2; 10:1; 11:2
+```
+
+Sign-change cause counts:
+
+```text
+retention_drop_dominant:4
+```
+
+## Main Inference
+
+The useful feature is not the first residual and not the modal residual.
+
+The mode is always shallow:
+
+```text
+all-ones depth mode = 1 for all 1024 rows
+```
+
+But the maximum all-ones depth strongly tracks positive block length:
+
+```text
+max all-ones depth 1-2:
+  block length 0 only
+
+max all-ones depth 3:
+  almost all block length 0
+
+max all-ones depth 8:
+  block length 4-6
+
+max all-ones depth 10/11:
+  block length 8
+```
+
+So the pressure block signal is an excursion signal:
+
+```text
+the window contains a deep all-ones residual carrier
+```
+
+not:
+
+```text
+the whole window is all-ones-like
+```
+
+This is an important correction before building a larger grid.
+
+## Lean Surface
+
+Added to `DkMath.Collatz.PetalBridge`:
+
+```lean
+ResidualAllOnesDepth
+orbitWindowResidualAllOnesDepth
+orbitWindowResidualAllOnesDepthSeq
+orbitWindowResidualAllOnesDepthSeq_length
+orbitWindowResidualAllOnesDepthSeq_get?_eq_some
+orbitWindowResidualAllOnesDepthSeq_take_length
+orbitWindowResidualAllOnesDepthSeq_take_get?_eq_some
+```
+
+This is intentionally only a skeleton.  It fixes the observation profile used
+by the Python scan without proving the heavier all-ones modulo bridge yet.
+
+## Documentation Updates
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-PressureAllOnesCorrelationScan-132.md
+```
+
+## Suggested Checkpoint 133
+
+Do not jump directly to a full `ShapePressureGrid`.
+
+The cleaner next split is:
+
+```text
+ResidualAllOnesProfile
+PressureDecayProfile
+```
+
+Candidate Lean work:
+
+```lean
+def WindowHasResidualAllOnesDepthAtLeast
+def SourcePressureRetentionDrop
+def SourcePressureContinuationDrop
+def SourcePressureSignChangeUpWithDrop
+```
+
+Candidate Python work:
+
+```text
+compare max all-ones depth with max positive block length at larger max_n
+separate rows by max-depth threshold counts ge4/ge5/ge6
+classify sign-change-up rows by exact retention/continuation drop pair
+```
+
+## Verification
+
+Commands:
+
+```text
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 2047 --steps 64 --r-start 2 --depth-len 10
+python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+lake build DkMath.Collatz.PetalBridge
+```
+
+Result:
+
+```text
+Python scan: passed
+Python py_compile: passed
+PetalBridge build: passed
+```
+
+The build still reports the existing unrelated warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+No new Collatz-side `sorry` was introduced.
diff --git a/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py b/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
index b59bb81d..ea32f803 100644
--- a/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+++ b/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
@@ -34,6 +34,14 @@ class PressureSignPatternRow:
     residual_mod_8_seq: str
     residual_mod_16_seq: str
     residual_mod_32_seq: str
+    residual_all_ones_depth_seq: str
+    residual_all_ones_depth_first: int
+    residual_all_ones_depth_last: int
+    residual_all_ones_depth_mode: int
+    residual_all_ones_depth_max: int
+    count_all_ones_depth_ge_4: int
+    count_all_ones_depth_ge_5: int
+    count_all_ones_depth_ge_6: int
     positive_depths: str
     positive_blocks: str
     positive_depth_count: int
@@ -54,6 +62,8 @@ class PressureSignPatternRow:
     max_margin_jump: int
     max_retention_drop: int
     max_continuation_drop: int
+    sign_change_cause_labels: str
+    sign_change_drop_details: str
     margin_profile: str
     retention_profile: str
     continuation_profile: str
@@ -93,6 +103,11 @@ def v2(n: int) -> int:
     return count


+def all_ones_depth(x: int) -> int:
+    """Length of the low-bit all-ones suffix of x."""
+    return v2(x + 1)
+
+
 def accelerated_step(n: int) -> tuple[int, int]:
     value = 3 * n + 1
     height = v2(value)
@@ -163,6 +178,16 @@ def max_adjacent_jump(values: dict[int, int], depths: list[int]) -> int:
     return max(jumps, default=0)


+def classify_sign_change(retention_drop: int, continuation_drop: int) -> str:
+    if retention_drop > 2 * continuation_drop:
+        return "retention_drop_dominant"
+    if continuation_drop == 0:
+        return "continuation_hold"
+    if abs(retention_drop - 2 * continuation_drop) <= 1:
+        return "balanced"
+    return "unclear"
+
+
 def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPatternRow:
     labels, heights_all = orbit_labels_and_heights(n, steps)
     height_seq = heights_all[:steps]
@@ -171,6 +196,9 @@ def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPat
     residual_mod_8_seq = [value % 8 for value in residual_shape_seq]
     residual_mod_16_seq = [value % 16 for value in residual_shape_seq]
     residual_mod_32_seq = [value % 32 for value in residual_shape_seq]
+    residual_all_ones_depth_seq = [
+        all_ones_depth(value) for value in residual_shape_seq
+    ]

     depths = list(range(r_start, r_start + depth_len))
     extended_depths = list(range(r_start, r_start + depth_len + 1))
@@ -195,6 +223,17 @@ def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPat
         for depth in depths
         if margins[depth] <= 0 and margins[depth + 1] > 0
     ]
+    sign_change_details: list[str] = []
+    sign_change_labels: list[str] = []
+    for depth in sign_change_up:
+        retention_drop = retentions[depth] - retentions[depth + 1]
+        continuation_drop = continuations[depth] - continuations[depth + 1]
+        margin_jump = margins[depth + 1] - margins[depth]
+        label = classify_sign_change(retention_drop, continuation_drop)
+        sign_change_labels.append(label)
+        sign_change_details.append(
+            f"{depth}:ret={retention_drop},cont={continuation_drop},jump={margin_jump},cause={label}"
+        )
     sign_change_pair = first_sign_change_pair(positive_depths, r_start)
     block_lengths = [end - start + 1 for start, end in blocks]

@@ -209,6 +248,24 @@ def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPat
         residual_mod_8_seq=join_ints(residual_mod_8_seq),
         residual_mod_16_seq=join_ints(residual_mod_16_seq),
         residual_mod_32_seq=join_ints(residual_mod_32_seq),
+        residual_all_ones_depth_seq=join_ints(residual_all_ones_depth_seq),
+        residual_all_ones_depth_first=(
+            residual_all_ones_depth_seq[0] if residual_all_ones_depth_seq else -1
+        ),
+        residual_all_ones_depth_last=(
+            residual_all_ones_depth_seq[-1] if residual_all_ones_depth_seq else -1
+        ),
+        residual_all_ones_depth_mode=mode_int(residual_all_ones_depth_seq),
+        residual_all_ones_depth_max=max(residual_all_ones_depth_seq, default=-1),
+        count_all_ones_depth_ge_4=sum(
+            1 for value in residual_all_ones_depth_seq if value >= 4
+        ),
+        count_all_ones_depth_ge_5=sum(
+            1 for value in residual_all_ones_depth_seq if value >= 5
+        ),
+        count_all_ones_depth_ge_6=sum(
+            1 for value in residual_all_ones_depth_seq if value >= 6
+        ),
         positive_depths=join_ints(positive_depths),
         positive_blocks=join_blocks(blocks),
         positive_depth_count=len(positive_depths),
@@ -231,6 +288,8 @@ def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPat
         max_margin_jump=max_adjacent_jump(margins, depths),
         max_retention_drop=max_adjacent_drop(retentions, depths),
         max_continuation_drop=max_adjacent_drop(continuations, depths),
+        sign_change_cause_labels=";".join(sign_change_labels),
+        sign_change_drop_details=";".join(sign_change_details),
         margin_profile=join_pairs([(depth, margins[depth]) for depth in depths]),
         retention_profile=join_pairs([(depth, retentions[depth]) for depth in depths]),
         continuation_profile=join_pairs(
@@ -288,10 +347,26 @@ def count_list_field(rows: list[PressureSignPatternRow], field_name: str) -> Cou
     return counter


+def count_label_field(rows: list[PressureSignPatternRow], field_name: str) -> Counter[str]:
+    counter: Counter[str] = Counter()
+    for row in rows:
+        raw = getattr(row, field_name)
+        if not raw:
+            continue
+        for value in raw.split(";"):
+            if value:
+                counter[value] += 1
+    return counter
+
+
 def markdown_kv_counter(counter: Counter[int]) -> str:
     return "; ".join(f"{key}:{counter[key]}" for key in sorted(counter))


+def markdown_label_counter(counter: Counter[str]) -> str:
+    return "; ".join(f"{key}:{counter[key]}" for key in sorted(counter))
+
+
 def append_distribution_table(
     lines: list[str],
     title: str,
@@ -323,10 +398,34 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
     max_positive = max((row.positive_depth_count for row in rows), default=0)
     max_islands = max((row.local_island_count for row in rows), default=0)
     max_sign_changes = max((row.sign_change_up_count for row in rows), default=0)
+    all_ones_first_counts = Counter(
+        row.residual_all_ones_depth_first
+        for row in rows
+        if row.residual_all_ones_depth_first >= 0
+    )
+    all_ones_mode_counts = Counter(
+        row.residual_all_ones_depth_mode
+        for row in rows
+        if row.residual_all_ones_depth_mode >= 0
+    )
+    all_ones_max_counts = Counter(
+        row.residual_all_ones_depth_max
+        for row in rows
+        if row.residual_all_ones_depth_max >= 0
+    )
+    cause_counts = count_label_field(rows, "sign_change_cause_labels")
     top_pressure = sorted(
         nonempty,
         key=lambda row: (-row.positive_depth_count, -row.frontier_margin, row.n),
     )[:12]
+    top_all_ones = sorted(
+        rows,
+        key=lambda row: (
+            -row.residual_all_ones_depth_max,
+            -row.max_positive_block_length,
+            row.n,
+        ),
+    )[:12]
     top_islands = sorted(
         with_island,
         key=lambda row: (-row.local_island_count, -row.sign_change_up_count, row.n),
@@ -335,9 +434,13 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
         with_sign_change,
         key=lambda row: (-row.sign_change_up_count, -row.max_margin_jump, row.n),
     )[:12]
+    retention_drop_samples = sorted(
+        with_sign_change,
+        key=lambda row: (-row.max_retention_drop, -row.max_margin_jump, row.n),
+    )[:12]

     lines = [
-        "# Collatz Pressure Sign Pattern Scan - Checkpoint 130",
+        "# Collatz Pressure Sign Pattern Scan - Checkpoint 132",
         "",
         f"- rows: `{len(rows)}`",
         f"- rows with positive pressure depths: `{len(nonempty)}`",
@@ -351,28 +454,54 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
         f"- max local island count: `{max_islands}`",
         f"- max sign-change-up count: `{max_sign_changes}`",
         f"- positive block length counts: `{markdown_kv_counter(block_length_counts)}`",
+        f"- all-ones depth first counts: `{markdown_kv_counter(all_ones_first_counts)}`",
+        f"- all-ones depth mode counts: `{markdown_kv_counter(all_ones_mode_counts)}`",
+        f"- all-ones depth max counts: `{markdown_kv_counter(all_ones_max_counts)}`",
+        f"- sign-change cause counts: `{markdown_label_counter(cause_counts)}`",
         "",
         "## Top Positive-Depth Samples",
         "",
-        "| n | positive depths | blocks | frontier | frontier margin | islands | sign-up | margins |",
-        "|---:|---|---|---:|---:|---|---|---|",
+        "| n | positive depths | blocks | max block | all-ones max | frontier | frontier margin | islands | sign-up | margins |",
+        "|---:|---|---|---:|---:|---:|---:|---|---|---|",
     ]
     for row in top_pressure:
         lines.append(
             "| "
             f"{row.n} | {row.positive_depths} | {row.positive_blocks} | "
+            f"{row.max_positive_block_length} | {row.residual_all_ones_depth_max} | "
             f"{row.first_frontier_depth} | {row.frontier_margin} | "
             f"{row.local_islands} | {row.sign_change_up_positions} | "
             f"{row.margin_profile} |"
         )

+    lines.extend(
+        [
+            "",
+            "## Deepest All-Ones Samples",
+            "",
+            "| n | all-ones depths | max | counts ge4/ge5/ge6 | max block | positive blocks | residual mod 32 |",
+            "|---:|---|---:|---|---:|---|---|",
+        ]
+    )
+    for row in top_all_ones:
+        lines.append(
+            "| "
+            f"{row.n} | {row.residual_all_ones_depth_seq} | "
+            f"{row.residual_all_ones_depth_max} | "
+            f"{row.count_all_ones_depth_ge_4}/"
+            f"{row.count_all_ones_depth_ge_5}/"
+            f"{row.count_all_ones_depth_ge_6} | "
+            f"{row.max_positive_block_length} | {row.positive_blocks} | "
+            f"{row.residual_mod_32_seq} |"
+        )
+
     lines.extend(
         [
             "",
             "## Local-Island Samples",
             "",
-            "| n | islands | first sign-change pair | sign-up | height seq | first-failed seq | residual mod 16 |",
-            "|---:|---|---|---|---|---|---|",
+            "| n | islands | first sign-change pair | sign-up | causes | height seq | first-failed seq | all-ones depths | residual mod 16 |",
+            "|---:|---|---|---|---|---|---|---|---|",
         ]
     )
     if top_islands:
@@ -380,19 +509,20 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
             lines.append(
                 "| "
                 f"{row.n} | {row.local_islands} | {row.first_sign_change_pair} | "
-                f"{row.sign_change_up_positions} | {row.height_seq} | "
-                f"{row.first_failed_depth_seq} | {row.residual_mod_16_seq} |"
+                f"{row.sign_change_up_positions} | {row.sign_change_cause_labels} | "
+                f"{row.height_seq} | {row.first_failed_depth_seq} | "
+                f"{row.residual_all_ones_depth_seq} | {row.residual_mod_16_seq} |"
             )
     else:
-        lines.append("| - | none observed | - | - | - | - | - |")
+        lines.append("| - | none observed | - | - | - | - | - | - | - |")

     lines.extend(
         [
             "",
             "## Sign-Change-Up Samples",
             "",
-            "| n | sign-up | margin jump | retention drop | continuation drop | margins | retentions | continuations |",
-            "|---:|---|---:|---:|---:|---|---|---|",
+            "| n | sign-up | causes | margin jump | retention drop | continuation drop | drop details | margins | retentions | continuations |",
+            "|---:|---|---|---:|---:|---:|---|---|---|---|",
         ]
     )
     if sign_samples:
@@ -400,12 +530,35 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
             lines.append(
                 "| "
                 f"{row.n} | {row.sign_change_up_positions} | "
+                f"{row.sign_change_cause_labels} | "
                 f"{row.max_margin_jump} | {row.max_retention_drop} | "
-                f"{row.max_continuation_drop} | {row.margin_profile} | "
-                f"{row.retention_profile} | {row.continuation_profile} |"
+                f"{row.max_continuation_drop} | {row.sign_change_drop_details} | "
+                f"{row.margin_profile} | {row.retention_profile} | "
+                f"{row.continuation_profile} |"
+            )
+    else:
+        lines.append("| - | none observed | - | 0 | 0 | 0 | - | - | - | - |")
+
+    lines.extend(
+        [
+            "",
+            "## Largest Retention-Drop Sign-Change Samples",
+            "",
+            "| n | sign-up | causes | retention drop | continuation drop | drop details | all-ones depths |",
+            "|---:|---|---|---:|---:|---|---|",
+        ]
+    )
+    if retention_drop_samples:
+        for row in retention_drop_samples:
+            lines.append(
+                "| "
+                f"{row.n} | {row.sign_change_up_positions} | "
+                f"{row.sign_change_cause_labels} | {row.max_retention_drop} | "
+                f"{row.max_continuation_drop} | {row.sign_change_drop_details} | "
+                f"{row.residual_all_ones_depth_seq} |"
             )
     else:
-        lines.append("| - | none observed | 0 | 0 | 0 | - | - | - |")
+        lines.append("| - | none observed | - | 0 | 0 | - | - |")

     lines.extend(
         [
@@ -421,6 +574,10 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
             "presence of local islands and sign-change-up rows means pressure is a",
             "margin sign profile, not just carrier nesting.",
             "",
+            "Checkpoint 132 adds the direct all-ones-depth observable",
+            "`v2(residual + 1)`.  This separates the previous residue-class signal",
+            "from the actual low-bit all-ones concentration inside the window.",
+            "",
         ]
     )
     append_distribution_table(
@@ -465,6 +622,41 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
         "residual mod 32 first",
         "max block length counts",
     )
+    append_distribution_table(
+        lines,
+        "Positive Block Length By All-Ones Depth First",
+        table_count_by(rows, "residual_all_ones_depth_first", "max_positive_block_length"),
+        "all-ones depth first",
+        "max block length counts",
+    )
+    append_distribution_table(
+        lines,
+        "Positive Block Length By All-Ones Depth Mode",
+        table_count_by(rows, "residual_all_ones_depth_mode", "max_positive_block_length"),
+        "all-ones depth mode",
+        "max block length counts",
+    )
+    append_distribution_table(
+        lines,
+        "Positive Block Length By All-Ones Depth Max",
+        table_count_by(rows, "residual_all_ones_depth_max", "max_positive_block_length"),
+        "all-ones depth max",
+        "max block length counts",
+    )
+    append_distribution_table(
+        lines,
+        "Frontier Depth By All-Ones Depth First",
+        table_count_by(rows, "residual_all_ones_depth_first", "first_frontier_depth", True),
+        "all-ones depth first",
+        "frontier depth counts",
+    )
+    append_distribution_table(
+        lines,
+        "Frontier Depth By All-Ones Depth Max",
+        table_count_by(rows, "residual_all_ones_depth_max", "first_frontier_depth", True),
+        "all-ones depth max",
+        "frontier depth counts",
+    )
     append_distribution_table(
         lines,
         "Local Island Rows By Residual Mod 16 First",
@@ -479,12 +671,49 @@ def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
         "residual mod 16 first",
         "sign-change-up count rows",
     )
+    append_distribution_table(
+        lines,
+        "Local Island Rows By All-Ones Depth First",
+        table_count_by(with_island, "residual_all_ones_depth_first", "local_island_count"),
+        "all-ones depth first",
+        "local island count rows",
+    )
+    append_distribution_table(
+        lines,
+        "Local Island Rows By All-Ones Depth Max",
+        table_count_by(with_island, "residual_all_ones_depth_max", "local_island_count"),
+        "all-ones depth max",
+        "local island count rows",
+    )
+    append_distribution_table(
+        lines,
+        "Sign-Change-Up Rows By All-Ones Depth First",
+        table_count_by(
+            with_sign_change,
+            "residual_all_ones_depth_first",
+            "sign_change_up_count",
+        ),
+        "all-ones depth first",
+        "sign-change-up count rows",
+    )
+    append_distribution_table(
+        lines,
+        "Sign-Change-Up Rows By All-Ones Depth Max",
+        table_count_by(
+            with_sign_change,
+            "residual_all_ones_depth_max",
+            "sign_change_up_count",
+        ),
+        "all-ones depth max",
+        "sign-change-up count rows",
+    )
     lines.extend(
         [
             "",
             "## Sign-Change-Up Depth Counts",
             "",
             f"- depth counts: `{markdown_kv_counter(count_list_field(rows, 'sign_change_up_positions'))}`",
+            f"- cause counts: `{markdown_label_counter(cause_counts)}`",
             "",
         ]
     )
diff --git a/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md b/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
index 0aca5765..d376fd96 100644
--- a/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
+++ b/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
@@ -1,4 +1,4 @@
-# Collatz Pressure Sign Pattern Scan - Checkpoint 130
+# Collatz Pressure Sign Pattern Scan - Checkpoint 132

 - rows: `1024`
 - rows with positive pressure depths: `511`
@@ -12,40 +12,70 @@
 - max local island count: `1`
 - max sign-change-up count: `1`
 - positive block length counts: `1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3`
+- all-ones depth first counts: `1:513; 2:256; 3:128; 4:64; 5:32; 6:16; 7:8; 8:4; 9:2; 10:1`
+- all-ones depth mode counts: `1:1024`
+- all-ones depth max counts: `1:54; 2:156; 3:240; 4:83; 5:36; 6:391; 7:34; 8:25; 9:2; 10:1; 11:2`
+- sign-change cause counts: `retention_drop_dominant:4`

 ## Top Positive-Depth Samples

-| n | positive depths | blocks | frontier | frontier margin | islands | sign-up | margins |
-|---:|---|---|---:|---:|---|---|---|
-| 2047 | 2;3;4;5;6;7;8;9 | 2-9 | 2 | 9 |  |  | 2:9;3:11;4:9;5:6;6:3;7:2;8:2;9:1;10:0;11:-1 |
-| 1819 | 2;3;4;5;6;7;8;9 | 2-9 | 2 | 8 |  |  | 2:8;3:11;4:9;5:6;6:3;7:2;8:2;9:1;10:0;11:-1 |
-| 1915 | 2;3;4;5;6;7;8;9 | 2-9 | 2 | 6 |  |  | 2:6;3:11;4:9;5:6;6:3;7:2;8:2;9:1;10:0;11:-1 |
-| 1023 | 2;3;4;5;6;7;8 | 2-8 | 2 | 7 |  |  | 2:7;3:5;4:5;5:4;6:3;7:2;8:1;9:0;10:-1;11:0 |
-| 511 | 2;3;4;5;6;7 | 2-7 | 2 | 6 |  |  | 2:6;3:4;4:4;5:3;6:2;7:1;8:0;9:-1;10:0;11:0 |
-| 681 | 2;3;4;5;6;7 | 2-7 | 2 | 6 |  |  | 2:6;3:4;4:4;5:3;6:2;7:1;8:0;9:-1;10:0;11:0 |
-| 1535 | 2;3;4;5;6;7 | 2-7 | 2 | 6 |  |  | 2:6;3:4;4:4;5:3;6:2;7:1;8:0;9:-1;10:0;11:0 |
-| 895 | 2;3;4;5;6 | 2-6 | 2 | 9 |  |  | 2:9;3:6;4:4;5:3;6:1;7:-1;8:-1;9:0;10:0;11:0 |
-| 1193 | 2;3;4;5;6 | 2-6 | 2 | 9 |  |  | 2:9;3:6;4:4;5:3;6:1;7:-1;8:-1;9:0;10:0;11:0 |
-| 671 | 2;3;4;5;6 | 2-6 | 2 | 8 |  |  | 2:8;3:3;4:2;5:1;6:1;7:0;8:-1;9:0;10:0;11:0 |
-| 795 | 2;3;4;5;6 | 2-6 | 2 | 8 |  |  | 2:8;3:6;4:4;5:3;6:1;7:-1;8:-1;9:0;10:0;11:0 |
-| 1789 | 2;3;4;5;6 | 2-6 | 2 | 8 |  |  | 2:8;3:3;4:2;5:1;6:1;7:0;8:-1;9:0;10:0;11:0 |
+| n | positive depths | blocks | max block | all-ones max | frontier | frontier margin | islands | sign-up | margins |
+|---:|---|---|---:|---:|---:|---:|---|---|---|
+| 2047 | 2;3;4;5;6;7;8;9 | 2-9 | 8 | 10 | 2 | 9 |  |  | 2:9;3:11;4:9;5:6;6:3;7:2;8:2;9:1;10:0;11:-1 |
+| 1819 | 2;3;4;5;6;7;8;9 | 2-9 | 8 | 11 | 2 | 8 |  |  | 2:8;3:11;4:9;5:6;6:3;7:2;8:2;9:1;10:0;11:-1 |
+| 1915 | 2;3;4;5;6;7;8;9 | 2-9 | 8 | 11 | 2 | 6 |  |  | 2:6;3:11;4:9;5:6;6:3;7:2;8:2;9:1;10:0;11:-1 |
+| 1023 | 2;3;4;5;6;7;8 | 2-8 | 7 | 9 | 2 | 7 |  |  | 2:7;3:5;4:5;5:4;6:3;7:2;8:1;9:0;10:-1;11:0 |
+| 511 | 2;3;4;5;6;7 | 2-7 | 6 | 8 | 2 | 6 |  |  | 2:6;3:4;4:4;5:3;6:2;7:1;8:0;9:-1;10:0;11:0 |
+| 681 | 2;3;4;5;6;7 | 2-7 | 6 | 9 | 2 | 6 |  |  | 2:6;3:4;4:4;5:3;6:2;7:1;8:0;9:-1;10:0;11:0 |
+| 1535 | 2;3;4;5;6;7 | 2-7 | 6 | 8 | 2 | 6 |  |  | 2:6;3:4;4:4;5:3;6:2;7:1;8:0;9:-1;10:0;11:0 |
+| 895 | 2;3;4;5;6 | 2-6 | 5 | 8 | 2 | 9 |  |  | 2:9;3:6;4:4;5:3;6:1;7:-1;8:-1;9:0;10:0;11:0 |
+| 1193 | 2;3;4;5;6 | 2-6 | 5 | 8 | 2 | 9 |  |  | 2:9;3:6;4:4;5:3;6:1;7:-1;8:-1;9:0;10:0;11:0 |
+| 671 | 2;3;4;5;6 | 2-6 | 5 | 8 | 2 | 8 |  |  | 2:8;3:3;4:2;5:1;6:1;7:0;8:-1;9:0;10:0;11:0 |
+| 795 | 2;3;4;5;6 | 2-6 | 5 | 8 | 2 | 8 |  |  | 2:8;3:6;4:4;5:3;6:1;7:-1;8:-1;9:0;10:0;11:0 |
+| 1789 | 2;3;4;5;6 | 2-6 | 5 | 8 | 2 | 8 |  |  | 2:8;3:3;4:2;5:1;6:1;7:0;8:-1;9:0;10:0;11:0 |
+
+## Deepest All-Ones Samples
+
+| n | all-ones depths | max | counts ge4/ge5/ge6 | max block | positive blocks | residual mod 32 |
+|---:|---|---:|---|---:|---|---|
+| 1819 | 1;11;10;9;8;7;6;5;4;3;2;1;1;6;5;4;3;2;1;3;2;1;1;1;1;2;1;1;1;2;1;2;1;2;1;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1 | 11 | 15/12/9 | 8 | 2-9 | 9;31;31;31;31;31;31;31;15;7;11;17;29;31;31;15;7;27;9;23;19;13;1;1;25;11;17;13;25;27;25;3;21;11;1;17;29;11;1;17;5;9;31;31;31;15;7;11;17;5;13;13;29;11;17;13;5;1;1;1;1;1;1;1 |
+| 1915 | 1;2;1;1;2;1;11;10;9;8;7;6;5;4;3;2;1;1;6;5;4;3;2;1;3;2;1;1;1;1;2;1;1;1;2;1;2;1;2;1;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1 | 11 | 15/12/9 | 8 | 2-9 | 25;11;1;25;27;9;31;31;31;31;31;31;31;15;7;11;17;29;31;31;15;7;27;9;23;19;13;1;1;25;11;17;13;25;27;25;3;21;11;1;17;29;11;1;17;5;9;31;31;31;15;7;11;17;5;13;13;29;11;17;13;5;1;1 |
+| 2047 | 10;9;8;7;6;5;4;3;2;1;1;6;5;4;3;2;1;3;2;1;1;1;1;2;1;1;1;2;1;2;1;2;1;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1;1;1 | 10 | 14/11/8 | 8 | 2-9 | 31;31;31;31;31;31;15;7;11;17;29;31;31;15;7;27;9;23;19;13;1;1;25;11;17;13;25;27;25;3;21;11;1;17;29;11;1;17;5;9;31;31;31;15;7;11;17;5;13;13;29;11;17;13;5;1;1;1;1;1;1;1;1;1 |
+| 1023 | 9;8;7;6;5;4;3;2;1;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 9 | 6/5/4 | 7 | 2-8 | 31;31;31;31;31;15;23;3;5;21;13;1;17;5;7;11;17;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 681 | 9;8;7;6;5;4;3;2;1;1;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 9 | 6/5/4 | 6 | 2-7 | 31;31;31;31;31;15;7;11;1;17;21;13;1;17;5;7;11;17;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 511 | 8;7;6;5;4;3;2;1;1;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 8 | 5/4/3 | 6 | 2-7 | 31;31;31;31;15;7;11;1;17;21;13;1;17;5;7;11;17;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 1535 | 8;7;6;5;4;3;2;1;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 8 | 5/4/3 | 6 | 2-7 | 31;31;31;31;15;23;3;5;21;13;1;17;5;7;11;17;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 671 | 4;3;2;1;3;2;1;1;4;3;2;1;1;8;7;6;5;4;3;2;1;1;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 8 | 7/4/3 | 5 | 2-6 | 15;7;27;9;23;19;13;9;15;23;19;13;29;31;31;31;31;15;7;11;1;17;21;13;1;17;5;7;11;17;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 795 | 1;7;6;5;4;3;2;1;2;1;1;4;3;2;1;1;8;7;6;5;4;3;2;1;1;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 8 | 10/7/5 | 5 | 2-6 | 9;31;31;31;15;23;19;29;19;13;9;15;23;19;13;29;31;31;31;31;15;7;11;1;17;21;13;1;17;5;7;11;17;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 807 | 2;1;2;1;8;7;6;5;4;3;2;1;1;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 8 | 5/4/3 | 5 | 2-6 | 27;25;19;29;31;31;31;31;15;7;11;1;17;21;13;1;17;5;7;11;17;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 895 | 6;5;4;3;2;1;2;1;1;4;3;2;1;1;8;7;6;5;4;3;2;1;1;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 8 | 9/6/4 | 5 | 2-6 | 31;31;15;23;19;29;19;13;9;15;23;19;13;29;31;31;31;31;15;7;11;1;17;21;13;1;17;5;7;11;17;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 1007 | 3;2;1;3;2;1;1;4;3;2;1;1;8;7;6;5;4;3;2;1;1;1;1;1;1;1;3;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 8 | 6/4/3 | 5 | 2-6 | 7;27;9;23;19;13;9;15;23;19;13;29;31;31;31;31;15;7;11;1;17;21;13;1;17;5;7;11;17;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |

 ## Local-Island Samples

-| n | islands | first sign-change pair | sign-up | height seq | first-failed seq | residual mod 16 |
-|---:|---|---|---|---|---|---|
-| 1567 | 3 | 2->3 | 2 | 1;1;1;1;2;2;2;6;3;1;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;2;3;3;3;7;4;2;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 15;7;11;1;1;1;5;13;11;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
-| 1639 | 5 | 4->5 | 4 | 1;1;2;1;1;1;3;1;1;1;2;4;1;1;1;1;1;1;2;1;1;2;5;2;1;1;7;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;3;2;2;2;4;2;2;2;3;5;2;2;2;2;2;2;3;2;2;3;6;3;2;2;8;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 11;9;15;7;3;13;15;7;11;1;5;15;15;15;15;7;11;9;7;11;1;5;9;7;3;5;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
-| 1775 | 5 | 4->5 | 4 | 1;1;1;2;1;1;1;4;3;1;2;2;4;2;1;1;1;1;1;1;2;4;3;3;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;3;2;2;2;5;4;2;3;3;5;3;2;2;2;2;2;2;3;5;4;4;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 7;11;9;15;7;3;5;13;11;1;1;5;9;15;15;15;15;7;11;1;5;13;13;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| n | islands | first sign-change pair | sign-up | causes | height seq | first-failed seq | all-ones depths | residual mod 16 |
+|---:|---|---|---|---|---|---|---|---|
+| 1567 | 3 | 2->3 | 2 | retention_drop_dominant | 1;1;1;1;2;2;2;6;3;1;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;2;3;3;3;7;4;2;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 4;3;2;1;1;1;1;1;2;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 15;7;11;1;1;1;5;13;11;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 1639 | 5 | 4->5 | 4 | retention_drop_dominant | 1;1;2;1;1;1;3;1;1;1;2;4;1;1;1;1;1;1;2;1;1;2;5;2;1;1;7;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;3;2;2;2;4;2;2;2;3;5;2;2;2;2;2;2;3;2;2;3;6;3;2;2;8;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 2;1;4;3;2;1;4;3;2;1;1;7;6;5;4;3;2;1;3;2;1;1;1;3;2;1;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 11;9;15;7;3;13;15;7;11;1;5;15;15;15;15;7;11;9;7;11;1;5;9;7;3;5;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 1775 | 5 | 4->5 | 4 | retention_drop_dominant | 1;1;1;2;1;1;1;4;3;1;2;2;4;2;1;1;1;1;1;1;2;4;3;3;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;3;2;2;2;5;4;2;3;3;5;3;2;2;2;2;2;2;3;5;4;4;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 3;2;1;4;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 | 7;11;9;15;7;3;5;13;11;1;1;5;9;15;15;15;15;7;11;1;5;13;13;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |

 ## Sign-Change-Up Samples

-| n | sign-up | margin jump | retention drop | continuation drop | margins | retentions | continuations |
-|---:|---|---:|---:|---:|---|---|---|
-| 1567 | 2 | 3 | 5 | 1 | 2:-2;3:1;4:0;5:-1;6:0;7:0;8:0;9:0;10:0;11:0 | 2:8;3:3;4:2;5:1;6:0;7:0;8:0;9:0;10:0;11:0 | 2:3;3:2;4:1;5:0;6:0;7:0;8:0;9:0;10:0;11:0 |
-| 1639 | 4 | 3 | 9 | 6 | 2:3;3:0;4:0;5:1;6:0;7:-1;8:0;9:0;10:0;11:0 | 2:21;3:12;4:6;5:3;6:2;7:1;8:0;9:0;10:0;11:0 | 2:12;3:6;4:3;5:2;6:1;7:0;8:0;9:0;10:0;11:0 |
-| 1775 | 4 | 3 | 5 | 3 | 2:4;3:3;4:0;5:1;6:0;7:-1;8:0;9:0;10:0;11:0 | 2:14;3:9;4:6;5:3;6:2;7:1;8:0;9:0;10:0;11:0 | 2:9;3:6;4:3;5:2;6:1;7:0;8:0;9:0;10:0;11:0 |
-| 1899 | 2 | 3 | 5 | 1 | 2:0;3:3;4:2;5:1;6:0;7:-1;8:0;9:0;10:0;11:0 | 2:10;3:5;4:4;5:3;6:2;7:1;8:0;9:0;10:0;11:0 | 2:5;3:4;4:3;5:2;6:1;7:0;8:0;9:0;10:0;11:0 |
+| n | sign-up | causes | margin jump | retention drop | continuation drop | drop details | margins | retentions | continuations |
+|---:|---|---|---:|---:|---:|---|---|---|---|
+| 1567 | 2 | retention_drop_dominant | 3 | 5 | 1 | 2:ret=5,cont=1,jump=3,cause=retention_drop_dominant | 2:-2;3:1;4:0;5:-1;6:0;7:0;8:0;9:0;10:0;11:0 | 2:8;3:3;4:2;5:1;6:0;7:0;8:0;9:0;10:0;11:0 | 2:3;3:2;4:1;5:0;6:0;7:0;8:0;9:0;10:0;11:0 |
+| 1639 | 4 | retention_drop_dominant | 3 | 9 | 6 | 4:ret=3,cont=1,jump=1,cause=retention_drop_dominant | 2:3;3:0;4:0;5:1;6:0;7:-1;8:0;9:0;10:0;11:0 | 2:21;3:12;4:6;5:3;6:2;7:1;8:0;9:0;10:0;11:0 | 2:12;3:6;4:3;5:2;6:1;7:0;8:0;9:0;10:0;11:0 |
+| 1775 | 4 | retention_drop_dominant | 3 | 5 | 3 | 4:ret=3,cont=1,jump=1,cause=retention_drop_dominant | 2:4;3:3;4:0;5:1;6:0;7:-1;8:0;9:0;10:0;11:0 | 2:14;3:9;4:6;5:3;6:2;7:1;8:0;9:0;10:0;11:0 | 2:9;3:6;4:3;5:2;6:1;7:0;8:0;9:0;10:0;11:0 |
+| 1899 | 2 | retention_drop_dominant | 3 | 5 | 1 | 2:ret=5,cont=1,jump=3,cause=retention_drop_dominant | 2:0;3:3;4:2;5:1;6:0;7:-1;8:0;9:0;10:0;11:0 | 2:10;3:5;4:4;5:3;6:2;7:1;8:0;9:0;10:0;11:0 | 2:5;3:4;4:3;5:2;6:1;7:0;8:0;9:0;10:0;11:0 |
+
+## Largest Retention-Drop Sign-Change Samples
+
+| n | sign-up | causes | retention drop | continuation drop | drop details | all-ones depths |
+|---:|---|---|---:|---:|---|---|
+| 1639 | 4 | retention_drop_dominant | 9 | 6 | 4:ret=3,cont=1,jump=1,cause=retention_drop_dominant | 2;1;4;3;2;1;4;3;2;1;1;7;6;5;4;3;2;1;3;2;1;1;1;3;2;1;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 1567 | 2 | retention_drop_dominant | 5 | 1 | 2:ret=5,cont=1,jump=3,cause=retention_drop_dominant | 4;3;2;1;1;1;1;1;2;1;2;1;2;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 1775 | 4 | retention_drop_dominant | 5 | 3 | 4:ret=3,cont=1,jump=1,cause=retention_drop_dominant | 3;2;1;4;3;2;1;1;2;1;1;1;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 1899 | 2 | retention_drop_dominant | 5 | 1 | 2:ret=5,cont=1,jump=3,cause=retention_drop_dominant | 1;1;2;1;2;1;7;6;5;4;3;2;1;1;1;1;1;2;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |

 ## Reading

@@ -58,6 +88,10 @@ This is not evidence for an unconditional pressure-prefix theorem.  The
 presence of local islands and sign-change-up rows means pressure is a
 margin sign profile, not just carrier nesting.

+Checkpoint 132 adds the direct all-ones-depth observable
+`v2(residual + 1)`.  This separates the previous residue-class signal
+from the actual low-bit all-ones concentration inside the window.
+

 ## Frontier Depth By Residual Mod 16 First

@@ -147,6 +181,72 @@ margin sign profile, not just carrier nesting.
 | 29 | 0:31;1:27;2:2;3:2;4:1;5:1 |
 | 31 | 1:13;2:14;3:11;4:13;5:7;6:3;7:1;8:1 |

+## Positive Block Length By All-Ones Depth First
+
+| all-ones depth first | max block length counts |
+|---:|---|
+| 1 | 0:301;1:172;2:14;3:6;4:13;5:5;8:2 |
+| 2 | 0:147;1:91;2:5;3:4;4:5;5:4 |
+| 3 | 0:51;1:68;2:5;3:1;4:1;5:2 |
+| 4 | 0:14;1:36;2:10;3:1;4:1;5:2 |
+| 5 | 1:13;2:10;3:6;4:2;5:1 |
+| 6 | 2:4;3:5;4:6;5:1 |
+| 7 | 4:4;5:4 |
+| 8 | 4:1;5:1;6:2 |
+| 9 | 6:1;7:1 |
+| 10 | 8:1 |
+
+## Positive Block Length By All-Ones Depth Mode
+
+| all-ones depth mode | max block length counts |
+|---:|---|
+| 1 | 0:513;1:380;2:48;3:23;4:33;5:20;6:3;7:1;8:3 |
+
+## Positive Block Length By All-Ones Depth Max
+
+| all-ones depth max | max block length counts |
+|---:|---|
+| 1 | 0:54 |
+| 2 | 0:156 |
+| 3 | 0:234;1:6 |
+| 4 | 0:66;1:15;2:2 |
+| 5 | 0:2;1:24;2:6;3:4 |
+| 6 | 0:1;1:334;2:38;3:12;4:6 |
+| 7 | 1:1;2:2;3:7;4:22;5:2 |
+| 8 | 4:5;5:18;6:2 |
+| 9 | 6:1;7:1 |
+| 10 | 8:1 |
+| 11 | 8:2 |
+
+## Frontier Depth By All-Ones Depth First
+
+| all-ones depth first | frontier depth counts |
+|---:|---|
+| 1 | 2:211;3:1 |
+| 2 | 2:109 |
+| 3 | 2:77 |
+| 4 | 2:49;3:1 |
+| 5 | 2:32 |
+| 6 | 2:16 |
+| 7 | 2:8 |
+| 8 | 2:4 |
+| 9 | 2:2 |
+| 10 | 2:1 |
+
+## Frontier Depth By All-Ones Depth Max
+
+| all-ones depth max | frontier depth counts |
+|---:|---|
+| 3 | 2:6 |
+| 4 | 2:16;3:1 |
+| 5 | 2:34 |
+| 6 | 2:390 |
+| 7 | 2:33;3:1 |
+| 8 | 2:25 |
+| 9 | 2:2 |
+| 10 | 2:1 |
+| 11 | 2:2 |
+
 ## Local Island Rows By Residual Mod 16 First

 | residual mod 16 first | local island count rows |
@@ -164,6 +264,38 @@ margin sign profile, not just carrier nesting.
 | 11 | 1:1 |
 | 15 | 1:1 |

+## Local Island Rows By All-Ones Depth First
+
+| all-ones depth first | local island count rows |
+|---:|---|
+| 2 | 1:1 |
+| 3 | 1:1 |
+| 4 | 1:1 |
+
+## Local Island Rows By All-Ones Depth Max
+
+| all-ones depth max | local island count rows |
+|---:|---|
+| 4 | 1:1 |
+| 7 | 1:2 |
+
+## Sign-Change-Up Rows By All-Ones Depth First
+
+| all-ones depth first | sign-change-up count rows |
+|---:|---|
+| 1 | 1:1 |
+| 2 | 1:1 |
+| 3 | 1:1 |
+| 4 | 1:1 |
+
+## Sign-Change-Up Rows By All-Ones Depth Max
+
+| all-ones depth max | sign-change-up count rows |
+|---:|---|
+| 4 | 1:1 |
+| 7 | 1:3 |
+
 ## Sign-Change-Up Depth Counts

 - depth counts: `2:2; 4:2`
+- cause counts: `retention_drop_dominant:4`
````
`````
