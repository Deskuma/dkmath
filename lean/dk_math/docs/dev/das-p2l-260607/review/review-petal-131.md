# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 6806f532235d838b415fa079504ab757cfc753a9

## Report

Checkpoint 130 を実装しました。

pressure sign-pattern scan を追加しました: [pressure_sign_pattern_scan.py](/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py:1)。`odd n <= 2047`, `steps = 64`, depths `2..11` で実行し、結果は [pressure_sign_pattern_scan.md](/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md#L1) と CSV に出しています。観測結果は、positive depth あり `511/1024`、local island `3`、sign-change-up `4`。`n = 1567, 1639, 1775` が local island の代表例です。

Lean 側は重くせず、scan を受ける薄い分類 API だけ入れました: [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean#L7205)。追加は `SourcePressurePositiveBlock`、bounded local island/frontier predicate、それぞれの margin equivalence です。これは prefix 定理ではなく、pressure を margin sign profile として扱うための観測ハンドルです。

Docs は README、Guide、Status を同期し、新規に [Collatz-PressureSignPatternScan-130.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md#L1) と [report-petal-130.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-130.md#L1) を追加しました。次は `residual_mod_16/32` と frontier/block/island の aggregate correlation scan が自然です。

検証:
`python3 ...pressure_sign_pattern_scan.py --max-n 2047 --steps 64 --r-start 2 --depth-len 10` passed
`lake build DkMath.Collatz.PetalBridge` passed
`lake build DkMath.Collatz.Collatz2K26` passed
対象 Collatz 2ファイルの `sorry` scan はヒットなし
`git diff --check` passed
既存の unrelated warning として `ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告は継続しています。

## Review

## 状況分析

Checkpoint `130` は、Route A から Route B へ戻る判断として良い。
ここまでで `height_i / residual_i / first_failed_i` の time profile は揃っていたので、今回は pressure-depth 側の sign pattern を実測する段階だった。

今回の実装では `pressure_sign_pattern_scan.py` が追加され、`odd n <= 2047`, `steps = 64`, depths `2..11` の scan が実行されている。結果として、positive depth ありは `511/1024`、local island は `3`、sign-change-up は `4`。代表的 local island は `n = 1567, 1639, 1775` と報告されている。

Lean 側も重くせず、`SourcePressurePositiveBlock`、bounded local island/frontier predicate、それぞれの margin equivalence だけを追加している。これは良い判断じゃ。今回の追加は prefix 定理ではなく、あくまで pressure を margin sign profile として読むための観測ハンドルになっている。

## レビュー

## 良い点

第一に、scan が二軸を分けている点が良い。

```text
time index i:
  height_i
  residual_i
  first_failed_i

pressure depth j:
  margin_j
  positive_j
  frontier_j
  local_island_j
  sign_change_up_j
```

ここを分けたまま scan しているので、`i` と `j` を混ぜた危険な theorem に進みにくい。これは checkpoint `129` までの軸警告をきちんと守っている。

第二に、local island が実際に観測されたのが大きい。
`rows with local islands: 3`、`rows with sign-change-up positions: 4` は少数だが、存在するだけで「無条件 prefix theorem」は危険だと示せる。特に `1567`, `1639`, `1775` は、今後も obstruction witness として使える。

第三に、Lean 側の追加が薄い。

```lean
SourcePressurePositiveBlock
sourcePressurePositiveBlock_iff_margin
ExistsSourcePressureLocalIslandBelow
existsSourcePressureLocalIslandBelow_iff_margin
ExistsSourcePressureFrontierBelow
existsSourcePressureFrontierBelow_iff_margin
```

これはちょうど良い。
最大性・一意性・prefix 性を主張せず、scan 結果を受けるための分類語彙に徹している。

## 注意点

一つだけ用語上の注意がある。

Python 側の `first_failure_pair` は、実装を見る限り、一般の `SourcePressurePrefixFailure` というより、

```text
隣接する非正 -> 正 の sign-change-up pair
```

に近い。

つまり、

```text
2 -> 3
4 -> 5
```

のような adjacent witness を取っている。
これは便利だが、Lean 側の `SourcePressurePrefixFailure` は「浅い非 selected と深い selected」の一般形なので、完全に同じ意味ではない。

したがって、scan 表示名としては次 checkpoint で

```text
first_failure_pair
```

よりも、

```text
first_adjacent_failure_pair
```

または

```text
first_sign_change_pair
```

へ寄せた方が、後で混乱しにくい。

もう一つ、`rows with positive blocks` は、single depth の positive も block と見るのか、長さ `>= 2` だけを block と見るのかを明記した方がよい。現状の summary では positive blocks が `132` と出ているが、`positive_depths` 非空の `511` とは別なので、これはおそらく「複数深さまたは range block を持つ行」の意味に近い。次回 doc で、

```text
positive block:
  length >= 2 の consecutive positive depths
```

なのか、

```text
positive block:
  length >= 1 を許す consecutive positive depths
```

なのかを固定すると良い。

## 解説

今回、かなり重要な観測が出ている。

positive pressure depth は `511/1024` と、かなりの頻度で現れる。
一方で local island は `3`、sign-change-up は `4` と少ない。

これは、pressure sign profile が完全にランダムというより、

```text
基本的には block/prefix 的に見えることが多い
しかし例外的に island / sign-change-up が実在する
```

という状態じゃ。

つまり、次の推論はこうなる。

```text
carrier nesting:
  深い carrier は浅い carrier に含まれる

pressure block:
  多くの場合、positive depth は連続的に見える

pressure island:
  しかし retention / continuation の比率変化により、局所的な正 margin が孤立することがある
```

この「例外が少数だが実在する」という状態は、研究上とても良い。
なぜなら、無条件 prefix theorem を捨てる理由がありつつ、完全に無秩序でもないからじゃ。

ここからは、island がなぜ発生するかを追えばよい。

## 次の指示

Checkpoint `131` は、Lean theorem 追加よりも **aggregate correlation scan** を優先するのが良い。

今回の scan は「個別行の sign pattern」を出した。
次は、その集計を行う。

## Checkpoint 131 推奨内容

### 1. `residual_mod_16 / 32` と pressure feature の相関表

追加したい summary tables。

```text
frontier_depth by residual_mod_16
frontier_depth by residual_mod_32

positive_block_length by residual_mod_16
positive_block_length by residual_mod_32

local_island_depth by residual_mod_16
local_island_depth by residual_mod_32

sign_change_up_depth by residual_mod_16
sign_change_up_depth by residual_mod_32
```

ここで大事なのは、`residual_mod_16_seq` 全体を見るだけでなく、どの時刻 `i` の residual を使うかじゃ。

まずは簡単に三種類を分けるとよい。

```text
residual_mod_16_first:
  residual_shape_seq[0] mod 16

residual_mod_16_last:
  residual_shape_seq[-1] mod 16

residual_mod_16_mode:
  window 内で最頻の mod 16 residue
```

同様に `mod 32` も見る。

### 2. island witness の局所 time profile を切り出す

local island がある `n = 1567, 1639, 1775` は、単なる代表例ではなく、別枠で詳しく出すべきじゃ。

追加したい island-local summary。

```text
n
island_depth
sign_change_pair
margin_profile around island
retention_profile around island
continuation_profile around island

height_seq prefix around event
first_failed_depth_seq prefix around event
residual_mod_16_seq prefix around event
residual_mod_32_seq prefix around event
```

ただし、pressure depth の `j` と time index の `i` は別軸なので、「around event」は time ではなく、まずは単に先頭 `16` step などでよい。

### 3. positive block の長さ分布

今の scan では `positive_blocks` が出ている。
次は block length distribution を集計する。

```text
positive_block_length_counts:
  len 1:
  len 2:
  len 3:
  ...

max_positive_block_length:
rows_with_block_len_ge_2:
rows_with_block_len_ge_4:
```

これで、pressure が「だいたい prefix/block 的」なのか、「短い positive 島が多い」のかが見える。

### 4. sign-change-up の原因分解

`sign_change_up` が出た行では、margin jump, retention drop, continuation drop が取れている。
次は sign-change-up の直前直後で、どちらが効いているかを分類する。

```text
sign_change_caused_by:
  retention_drop_dominant
  continuation_hold_dominant
  both
  unclear
```

雑でもよい。例えば、

```text
retention_drop = retention[j] - retention[j+1]
continuation_drop = continuation[j] - continuation[j+1]
margin_jump = margin[j+1] - margin[j]
```

この値を見るだけで、island が「retention が急に落ちた」ためなのか、「continuation が相対的に残った」ためなのかが見えてくる。

## 一歩先ゆく推論

ここから見えてきた仮説はこれじゃ。

```text
local island は、深い continuation が突然増える現象ではなく、
浅い retention が急に落ちることで margin が正に転じる現象かもしれない。
```

実際、代表例 `n = 1567` の sign-change-up sample では、margin は `2:-2;3:1` へ跳ねている。retention は `2:8;3:3`、continuation は `2:3;3:2`。つまり continuation は減っているが、retention の落ち方が大きいために margin が正へ移っている。

これはかなり重要。

つまり island は「深い層が強くなった」のではなく、

```text
浅い retention が薄くなりすぎて、
相対的に continuation が半分を超える
```

現象として見える。

この見方なら、pressure island は異常ではない。
`retention` と `continuation` の減衰率差から自然に生じる sign pattern じゃ。

次はこの減衰率差を観測する。

## さらなる次の一手

Checkpoint `131` の scan で相関が見えたら、Checkpoint `132` では軽い Lean 定義として次が候補になる。

## 1. retention-drop dominant

```lean
def SourcePressureRetentionDropDominant
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourceRetentionMass n k (r + j) >
    SourceRetentionMass n k (r + j + 1) ∧
  SourceContinuationMass n k (r + j) ≥
    SourceContinuationMass n k (r + j + 1)
```

ただし、実際の mass theorem 名に合わせる必要がある。
これはまだ仮名じゃ。

## 2. margin jump

もし `SourcePressureMarginInt` だけで行くなら、まずこちらが軽い。

```lean
def SourcePressureMarginJumpUp
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureMarginInt n k (r + j) <
    SourcePressureMarginInt n k (r + j + 1)
```

さらに符号変化込み。

```lean
def SourcePressureSignChangeUpWithJump
    (n : OddNat) (k r j : ℕ) : Prop :=
  SourcePressureSignChangeUp n k r j ∧
    SourcePressureMarginInt n k (r + j) <
      SourcePressureMarginInt n k (r + j + 1)
```

ただし `SourcePressureSignChangeUp` なら後半はほぼ自明に近い。
なぜなら左が `≤ 0`、右が `> 0` だから。別 theorem として軽く出せる。

```lean
theorem sourcePressureMargin_lt_of_signChangeUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureSignChangeUp n k r j) :
    SourcePressureMarginInt n k (r + j) <
      SourcePressureMarginInt n k (r + j + 1) := by
  rcases h with ⟨hle, hpos⟩
  omega
```

これはかなり軽くて良い。

## 賢狼が試して欲しい実験補題

## 実験 A: sign-change-up implies strict margin jump

```lean
theorem sourcePressureMargin_lt_of_signChangeUp
    (n : OddNat) (k r j : ℕ)
    (h : SourcePressureSignChangeUp n k r j) :
    SourcePressureMarginInt n k (r + j) <
      SourcePressureMarginInt n k (r + j + 1) := by
  rcases h with ⟨hle, hpos⟩
  omega
```

## 実験 B: positive block singleton

```lean
theorem sourcePressurePositiveBlock_singleton
    (n : OddNat) (k r j : ℕ)
    (h : IsSourcePressureDepth n k r j) :
    SourcePressurePositiveBlock n k r j 1 := by
  constructor
  · omega
  · intro t hle hlt
    have ht : t = j := by omega
    simpa [ht] using h
```

これは block API の基本 constructor になる。

## 実験 C: positive block from margin interval

```lean
theorem sourcePressurePositiveBlock_of_forall_margin_pos
    (n : OddNat) (k r a len : ℕ)
    (hlen : 0 < len)
    (hpos : ∀ j, a ≤ j → j < a + len →
      0 < SourcePressureMarginInt n k (r + j)) :
    SourcePressurePositiveBlock n k r a len := by
  exact (sourcePressurePositiveBlock_iff_margin n k r a len).2
    ⟨hlen, hpos⟩
```

## 実験 D: exists local island below constructor

```lean
theorem existsSourcePressureLocalIslandBelow_of_lt
    (n : OddNat) (k r m j : ℕ)
    (hjm : j < m)
    (hisland : SourcePressureLocalIsland n k r j) :
    ExistsSourcePressureLocalIslandBelow n k r m := by
  exact ⟨j, hjm, hisland⟩
```

## 実験 E: exists frontier below constructor

```lean
theorem existsSourcePressureFrontierBelow_of_lt
    (n : OddNat) (k r m j : ℕ)
    (hjm : j < m)
    (hfront : SourcePressureFrontier n k r j) :
    ExistsSourcePressureFrontierBelow n k r m := by
  exact ⟨j, hjm, hfront⟩
```

## 実験 F: local island gives sign-change-up at previous depth

すでに frontier から sign-change-up はある。local island からも、左側で sign-change-up が出る。

```lean
theorem sourcePressureSignChangeUp_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureSignChangeUp n k r (j - 1) := by
  rcases hisland with ⟨hjpos, hsel, hprev_not, _hnext_not⟩
  unfold SourcePressureSignChangeUp
  constructor
  · have hnotpos :
        ¬ 0 < SourcePressureMarginInt n k (r + (j - 1)) := by
      intro hpos
      exact hprev_not
        ((isSourcePressureDepth_iff_margin_pos n k r (j - 1)).2 hpos)
    omega
  · have hpos :
        0 < SourcePressureMarginInt n k (r + j) :=
      (isSourcePressureDepth_iff_margin_pos n k r j).1 hsel
    have hidx : r + (j - 1) + 1 = r + j := by omega
    simpa [hidx] using hpos
```

これは、local island を sign-change-up 系に接続する良い補題じゃ。

## Python 側の次観測

Checkpoint `131` の scan 拡張案。

```text
# Aggregate Correlation Scan

## Parameters
max_n:
steps:
r_start:
depth_len:

## Existing Summary
rows:
rows_with_positive_depths:
rows_with_positive_blocks:
rows_with_local_islands:
rows_with_sign_change_up:

## Frontier By Residue
frontier_depth_by_residual_mod_16_first:
frontier_depth_by_residual_mod_16_mode:
frontier_depth_by_residual_mod_32_first:
frontier_depth_by_residual_mod_32_mode:

## Island By Residue
local_island_depth_by_residual_mod_16_first:
local_island_depth_by_residual_mod_16_mode:
local_island_depth_by_residual_mod_32_first:
local_island_depth_by_residual_mod_32_mode:

## Block Length Distribution
positive_block_length_counts:
positive_block_length_by_residual_mod_16:
positive_block_length_by_residual_mod_32:

## Sign Change Cause
sign_change_up_depth_counts:
sign_change_margin_jump_counts:
sign_change_retention_drop_counts:
sign_change_continuation_drop_counts:

## Representative Rows
first_local_island:
largest_margin_jump:
largest_retention_drop:
largest_positive_block:
```

## Codex への次指示まとめ

```text
Checkpoint 131:
Extend pressure sign-pattern scan with aggregate correlation tables.

Primary goal:
  Keep time axis i and depth axis j separate, but aggregate correlations between:
    residual_mod_16 / residual_mod_32
    first_frontier_depth
    positive_block_length
    local_island_depth
    sign_change_up_depth
    margin_jump / retention_drop / continuation_drop

Update Python:
  Add aggregate summary tables to pressure_sign_pattern_scan.py or a companion script.

Preferred outputs:
  pressure_sign_pattern_correlation.md
  optional CSV for aggregate counts

Lean optional, small only:
  sourcePressureMargin_lt_of_signChangeUp
  sourcePressurePositiveBlock_singleton
  existsSourcePressureLocalIslandBelow_of_lt
  existsSourcePressureFrontierBelow_of_lt
  sourcePressureSignChangeUp_of_localIsland

Do not:
  introduce Real.log
  claim pressure prefix
  define full ShapePressureGrid yet
  merge time index i and pressure depth j
```

## 総括

Checkpoint `130` は成功じゃ。
これで Route B は「思いつきの Lean predicate」ではなく、実測 scan に戻った。

結果はとても良い。

```text
positive block は多い。
local island は少数だが実在する。
sign-change-up も少数だが実在する。
```

これは、pressure が完全な prefix ではないが、完全な乱雑でもないことを示している。

次は相関を見る。
特に賢狼は、

```text
island / sign-change-up は retention drop の急変として説明できるか？
```

を見たい。

ここが見えれば、`ShapePressureGrid` はただの表ではなく、
**time profile が depth sign pattern をどう作るかを見る格子**として自然に立ち上がる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index a44bd916..6f6c1cd8 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -7202,6 +7202,97 @@ theorem sourcePressureLocalIsland_iff_margin
         (isSourcePressureDepth_iff_margin_pos n k r (j + 1)).1 hnext
       omega

+/--
+A consecutive block of positive source-pressure depths.
+
+Checkpoint 130 keeps this predicate intentionally thin.  The Python
+pressure-sign scan shows that positive depths often appear as blocks, while
+local islands can also occur.  This predicate records only the block condition;
+it does not assert maximality, uniqueness, or prefix behavior.
+-/
+def SourcePressurePositiveBlock
+    (n : OddNat) (k r a len : ℕ) : Prop :=
+  0 < len ∧
+    ∀ j, a ≤ j → j < a + len → IsSourcePressureDepth n k r j
+
+/--
+Positive pressure block in margin language.
+-/
+theorem sourcePressurePositiveBlock_iff_margin
+    (n : OddNat) (k r a len : ℕ) :
+    SourcePressurePositiveBlock n k r a len ↔
+      0 < len ∧
+        ∀ j, a ≤ j → j < a + len →
+          0 < SourcePressureMarginInt n k (r + j) := by
+  unfold SourcePressurePositiveBlock
+  constructor
+  · intro h
+    constructor
+    · exact h.1
+    · intro j hle hlt
+      exact (isSourcePressureDepth_iff_margin_pos n k r j).1
+        (h.2 j hle hlt)
+  · intro h
+    constructor
+    · exact h.1
+    · intro j hle hlt
+      exact (isSourcePressureDepth_iff_margin_pos n k r j).2
+        (h.2 j hle hlt)
+
+/--
+There is a local source-pressure island below a finite depth bound.
+-/
+def ExistsSourcePressureLocalIslandBelow
+    (n : OddNat) (k r m : ℕ) : Prop :=
+  ∃ j, j < m ∧ SourcePressureLocalIsland n k r j
+
+/--
+Existence of a bounded local pressure island in margin language.
+-/
+theorem existsSourcePressureLocalIslandBelow_iff_margin
+    (n : OddNat) (k r m : ℕ) :
+    ExistsSourcePressureLocalIslandBelow n k r m ↔
+      ∃ j, j < m ∧
+        0 < j ∧
+        0 < SourcePressureMarginInt n k (r + j) ∧
+        SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
+        SourcePressureMarginInt n k (r + (j + 1)) ≤ 0 := by
+  unfold ExistsSourcePressureLocalIslandBelow
+  constructor
+  · intro h
+    rcases h with ⟨j, hjm, hjisland⟩
+    rw [sourcePressureLocalIsland_iff_margin] at hjisland
+    exact ⟨j, hjm, hjisland⟩
+  · intro h
+    rcases h with ⟨j, hjm, hjmargin⟩
+    exact ⟨j, hjm, (sourcePressureLocalIsland_iff_margin n k r j).2 hjmargin⟩
+
+/--
+There is a source-pressure frontier below a finite depth bound.
+-/
+def ExistsSourcePressureFrontierBelow
+    (n : OddNat) (k r m : ℕ) : Prop :=
+  ∃ j, j < m ∧ SourcePressureFrontier n k r j
+
+/--
+Existence of a bounded pressure frontier in margin language.
+-/
+theorem existsSourcePressureFrontierBelow_iff_margin
+    (n : OddNat) (k r m : ℕ) :
+    ExistsSourcePressureFrontierBelow n k r m ↔
+      ∃ j, j < m ∧
+        0 < SourcePressureMarginInt n k (r + j) ∧
+        ∀ i, i < j → SourcePressureMarginInt n k (r + i) ≤ 0 := by
+  unfold ExistsSourcePressureFrontierBelow
+  constructor
+  · intro h
+    rcases h with ⟨j, hjm, hfront⟩
+    rw [sourcePressureFrontier_iff_margin] at hfront
+    exact ⟨j, hjm, hfront⟩
+  · intro h
+    rcases h with ⟨j, hjm, hmargin⟩
+    exact ⟨j, hjm, (sourcePressureFrontier_iff_margin n k r j).2 hmargin⟩
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 4e4c5757..30d88424 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -167,6 +167,12 @@ SourcePressureFrontier
 SourcePressureSignChangeUp
 SourcePressureLocalIsland
 sourcePressureLocalIsland_iff_margin
+SourcePressurePositiveBlock
+sourcePressurePositiveBlock_iff_margin
+ExistsSourcePressureLocalIslandBelow
+existsSourcePressureLocalIslandBelow_iff_margin
+ExistsSourcePressureFrontierBelow
+existsSourcePressureFrontierBelow_iff_margin
 ```

 The central No.100 layer is:
@@ -225,6 +231,8 @@ docs/Collatz-GnomonEvaluation-125.md
 docs/Collatz-GnomonResidualShape-126.md
 docs/Collatz-WindowResidualShape-127.md
 docs/Collatz-ResidualShapeSequence-128.md
+docs/Collatz-FirstFailedDepthSequence-129.md
+docs/Collatz-PressureSignPatternScan-130.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 145e8d86..e78ee74a 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -298,6 +298,20 @@ sourcePressureLocalIsland_iff_margin
 These are observation predicates for margin sign profiles.  They should be
 used to classify pressure islands before proposing any new monotonicity theorem.

+Checkpoint 130 adds thin sign-pattern classification handles:
+
+```lean
+SourcePressurePositiveBlock
+sourcePressurePositiveBlock_iff_margin
+ExistsSourcePressureLocalIslandBelow
+existsSourcePressureLocalIslandBelow_iff_margin
+ExistsSourcePressureFrontierBelow
+existsSourcePressureFrontierBelow_iff_margin
+```
+
+These names are for reading scan output.  They do not assert maximality,
+uniqueness, unconditional prefix behavior, or a global pressure shape theorem.
+
 ## Residue Counts

 Named residue counts exist for low layers:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index ce728208..eba153f3 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -201,6 +201,38 @@ sourcePressureLocalIsland_iff_margin
 This keeps pressure-island language on the margin-sign surface rather than
 turning it into an unsupported prefix theorem.

+Checkpoint 130 adds a Python pressure sign-pattern scan and thin Lean
+classification handles:
+
+```lean
+SourcePressurePositiveBlock
+sourcePressurePositiveBlock_iff_margin
+ExistsSourcePressureLocalIslandBelow
+existsSourcePressureLocalIslandBelow_iff_margin
+ExistsSourcePressureFrontierBelow
+existsSourcePressureFrontierBelow_iff_margin
+```
+
+The scan output lives at:
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
+```
+
+Observed at `odd n <= 2047`, `steps = 64`, depths `2..11`:
+
+```text
+rows with positive pressure depths: 511 / 1024
+rows with local islands: 3
+rows with sign-change-up positions: 4
+max positive depth count: 8
+```
+
+This confirms that pressure should remain a sign-pattern surface.  Prefix-like
+blocks are common, but local islands and sign-change-up rows are real.
+
 The first theorem set is deliberately thin:

 ```lean
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md
new file mode 100644
index 00000000..22706367
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md
@@ -0,0 +1,136 @@
+# Collatz Pressure Sign Pattern Scan - Checkpoint 130
+
+Checkpoint 130 returns from Route A list helpers to Route B pressure
+observation.
+
+The new scan keeps the two axes separate:
+
+```text
+time index i:
+  height_i
+  residual_i
+  first_failed_i
+
+pressure depth j:
+  margin_j
+  positive_j
+  frontier_j
+  local_island_j
+  sign_change_up_j
+```
+
+## Files
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
+```
+
+## Default Scan Used
+
+```text
+odd n <= 2047
+steps = 64
+r_start = 2
+depth_len = 10
+depths = 2..11
+```
+
+The scan records:
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
+first_frontier_depth
+frontier_margin
+local_islands
+sign_change_up_positions
+first_failure_pair
+margin_jump
+retention_drop
+continuation_drop
+```
+
+## Observed Summary
+
+```text
+rows: 1024
+rows with positive pressure depths: 511
+rows with local islands: 3
+rows with sign-change-up positions: 4
+rows with positive blocks: 132
+max positive depth count: 8
+max local island count: 1
+max sign-change-up count: 1
+```
+
+Representative local-island rows:
+
+```text
+n = 1567, island depth 3, first failure pair 2 -> 3
+n = 1639, island depth 5, first failure pair 4 -> 5
+n = 1775, island depth 5, first failure pair 4 -> 5
+```
+
+These rows are the important obstruction witnesses.  They show again that
+pressure is not simply carrier nesting and does not support an unconditional
+prefix theorem.
+
+## Lean Surface Added
+
+Checkpoint 130 adds only thin predicates and margin bridges:
+
+```lean
+SourcePressurePositiveBlock
+sourcePressurePositiveBlock_iff_margin
+ExistsSourcePressureLocalIslandBelow
+existsSourcePressureLocalIslandBelow_iff_margin
+ExistsSourcePressureFrontierBelow
+existsSourcePressureFrontierBelow_iff_margin
+```
+
+These are classification handles for scan output.
+
+They do not assert maximality, uniqueness, global prefix behavior, or a heavy
+`ShapePressureGrid`.
+
+## Inference
+
+Positive blocks are common, but islands and sign-change-up rows exist.  The next
+step should therefore avoid any unconditional monotonicity theorem.
+
+The useful direction is conditional classification:
+
+```text
+positive block if every depth in an interval has positive margin
+local island if positive margin is surrounded by nonpositive margins
+frontier below if first positive margin appears before a bound
+```
+
+This keeps the future `ShapePressureGrid` honest: time features and depth signs
+must remain separate axes until a real correlation is observed.
+
+## Suggested Next Work
+
+Checkpoint 131 should either:
+
+```text
+1. extend the scan summary with aggregate correlations between
+   residual_mod_16/residual_mod_32 and first_frontier_depth
+```
+
+or:
+
+```text
+2. add one small Lean theorem using the new predicates,
+   such as a local-island-below constructor from a concrete island witness.
+```
+
+The scan route is preferred.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-130.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-130.md
new file mode 100644
index 00000000..30bfb8db
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-130.md
@@ -0,0 +1,183 @@
+# Report Petal 130
+
+## Summary
+
+Checkpoint 130 returns to Route B: pressure sign-pattern observation.
+
+The checkpoint adds a Python scan that records both axes:
+
+```text
+time index i:
+  height_i
+  residual_i
+  first_failed_i
+
+pressure depth j:
+  margin_j
+  positive_j
+  frontier_j
+  local_island_j
+  sign_change_up_j
+```
+
+The scan found that positive pressure depths often form blocks, but local
+islands and sign-change-up rows also occur.  Therefore the pressure surface
+must remain a margin-sign profile; it should not be collapsed into an
+unconditional prefix theorem.
+
+## Python Scan
+
+Added:
+
+```text
+python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.csv
+python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
+```
+
+Run used:
+
+```text
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
+  --max-n 2047 --steps 64 --r-start 2 --depth-len 10
+```
+
+Observed:
+
+```text
+rows: 1024
+rows with positive pressure depths: 511
+rows with local islands: 3
+rows with sign-change-up positions: 4
+rows with positive blocks: 132
+max positive depth count: 8
+max local island count: 1
+max sign-change-up count: 1
+```
+
+Representative local-island rows:
+
+```text
+n = 1567, island depth 3, first failure pair 2 -> 3
+n = 1639, island depth 5, first failure pair 4 -> 5
+n = 1775, island depth 5, first failure pair 4 -> 5
+```
+
+These are obstruction witnesses against a naive pressure-prefix theorem.
+
+## Lean Surface
+
+Added thin classification handles:
+
+```lean
+SourcePressurePositiveBlock
+sourcePressurePositiveBlock_iff_margin
+ExistsSourcePressureLocalIslandBelow
+existsSourcePressureLocalIslandBelow_iff_margin
+ExistsSourcePressureFrontierBelow
+existsSourcePressureFrontierBelow_iff_margin
+```
+
+These are intentionally light.  They classify observed sign patterns; they do
+not assert maximality, uniqueness, global prefix behavior, or a heavy
+`ShapePressureGrid`.
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md
+```
+
+## Added Inference
+
+The pressure surface now has three useful finite readings:
+
+```text
+positive block:
+  every depth in an interval has positive margin
+
+local island:
+  positive margin surrounded by nonpositive margins
+
+frontier below:
+  the first positive margin appears before a finite bound
+```
+
+The scan shows all three are useful handles, but the next step should still be
+data-driven.  The strongest next scan would aggregate correlations between:
+
+```text
+residual_mod_16 / residual_mod_32
+first_frontier_depth
+positive block length
+local island depth
+```
+
+This is the next realistic approach toward a later `ShapePressureGrid`.
+
+## Suggested Checkpoint 131
+
+Recommended:
+
+```text
+extend the pressure scan with aggregate correlation tables
+```
+
+Candidate summaries:
+
+```text
+frontier_depth by residual_mod_16
+positive_block_length by residual_mod_16
+local_island_depth by residual_mod_16
+sign_change_up_depth by residual_mod_16
+```
+
+If Lean-only work is requested, keep it small: add constructor-style theorems
+for the new bounded predicates from explicit witnesses.
+
+## Verification
+
+Commands:
+
+```text
+python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 2047 --steps 64 --r-start 2 --depth-len 10
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
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
+local Collatz sorry scan: passed, no hits in GnomonEvaluation/PetalBridge
+diff whitespace check: passed
+Python py_compile: passed
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
new file mode 100644
index 00000000..49d7395d
--- /dev/null
+++ b/python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
@@ -0,0 +1,362 @@
+#!/usr/bin/env python3
+"""Scan Collatz time profiles against pressure-depth sign patterns.
+
+Checkpoint 130 returns from the one-dimensional Lean list API to experimental
+pressure observation.  This script keeps the two axes visible:
+
+* time index i:
+  height_i, residual_i, first_failed_i
+* pressure-depth index j:
+  margin_j, selected_j, frontier_j, island_j
+
+The output is observational data.  It is intended to guide the next Lean
+predicate, not to assert a global pressure monotonicity theorem.
+"""
+
+from __future__ import annotations
+
+import argparse
+import csv
+from dataclasses import dataclass
+from pathlib import Path
+
+
+@dataclass(frozen=True)
+class PressureSignPatternRow:
+    n: int
+    steps: int
+    r_start: int
+    depth_len: int
+    height_seq: str
+    residual_shape_seq: str
+    first_failed_depth_seq: str
+    residual_mod_8_seq: str
+    residual_mod_16_seq: str
+    residual_mod_32_seq: str
+    positive_depths: str
+    positive_blocks: str
+    positive_depth_count: int
+    first_frontier_depth: int
+    frontier_margin: int
+    local_islands: str
+    local_island_count: int
+    sign_change_up_positions: str
+    sign_change_up_count: int
+    first_failure_pair: str
+    max_margin_jump: int
+    max_retention_drop: int
+    max_continuation_drop: int
+    margin_profile: str
+    retention_profile: str
+    continuation_profile: str
+
+
+def join_ints(values: list[int]) -> str:
+    return ";".join(str(value) for value in values)
+
+
+def join_pairs(values: list[tuple[int, int]]) -> str:
+    return ";".join(f"{left}:{right}" for left, right in values)
+
+
+def join_blocks(blocks: list[tuple[int, int]]) -> str:
+    return ";".join(f"{start}-{end}" if start != end else str(start) for start, end in blocks)
+
+
+def v2(n: int) -> int:
+    if n <= 0:
+        raise ValueError("v2 expects a positive integer")
+    count = 0
+    while n % 2 == 0:
+        count += 1
+        n //= 2
+    return count
+
+
+def accelerated_step(n: int) -> tuple[int, int]:
+    value = 3 * n + 1
+    height = v2(value)
+    return value >> height, height
+
+
+def orbit_labels_and_heights(n: int, steps: int) -> tuple[list[int], list[int]]:
+    labels: list[int] = []
+    heights: list[int] = []
+    current = n
+    for _ in range(steps + 1):
+        labels.append(current)
+        current, height = accelerated_step(current)
+        heights.append(height)
+    return labels, heights
+
+
+def count_residue(values: list[int], modulus: int, residue: int) -> int:
+    return sum(1 for value in values if value % modulus == residue)
+
+
+def retention_mass(labels: list[int], steps: int, depth: int) -> int:
+    return count_residue(labels[:steps], 2**depth, 2**depth - 1)
+
+
+def continuation_mass(labels: list[int], steps: int, depth: int) -> int:
+    return count_residue(labels[:steps], 2 ** (depth + 1), 2 ** (depth + 1) - 1)
+
+
+def margin_at(labels: list[int], steps: int, depth: int) -> int:
+    return 2 * continuation_mass(labels, steps, depth) - retention_mass(labels, steps, depth)
+
+
+def consecutive_blocks(depths: list[int]) -> list[tuple[int, int]]:
+    if not depths:
+        return []
+    blocks: list[tuple[int, int]] = []
+    start = depths[0]
+    prev = depths[0]
+    for depth in depths[1:]:
+        if depth == prev + 1:
+            prev = depth
+        else:
+            blocks.append((start, prev))
+            start = depth
+            prev = depth
+    blocks.append((start, prev))
+    return blocks
+
+
+def first_failure_pair(depths: list[int], r_start: int) -> tuple[int, int] | None:
+    selected = set(depths)
+    if not depths:
+        return None
+    for depth in range(r_start, max(depths)):
+        if depth not in selected and depth + 1 in selected:
+            return (depth, depth + 1)
+    return None
+
+
+def max_adjacent_drop(values: dict[int, int], depths: list[int]) -> int:
+    drops = [values[d] - values[d + 1] for d in depths[:-1]]
+    return max(drops, default=0)
+
+
+def max_adjacent_jump(values: dict[int, int], depths: list[int]) -> int:
+    jumps = [abs(values[d + 1] - values[d]) for d in depths[:-1]]
+    return max(jumps, default=0)
+
+
+def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPatternRow:
+    labels, heights_all = orbit_labels_and_heights(n, steps)
+    height_seq = heights_all[:steps]
+    residual_shape_seq = labels[1 : steps + 1]
+    first_failed_depth_seq = [height + 1 for height in height_seq]
+
+    depths = list(range(r_start, r_start + depth_len))
+    extended_depths = list(range(r_start, r_start + depth_len + 1))
+    margins = {depth: margin_at(labels, steps, depth) for depth in extended_depths}
+    retentions = {
+        depth: retention_mass(labels, steps, depth) for depth in extended_depths
+    }
+    continuations = {
+        depth: continuation_mass(labels, steps, depth) for depth in extended_depths
+    }
+    positive_depths = [depth for depth in depths if margins[depth] > 0]
+    blocks = consecutive_blocks(positive_depths)
+    frontier = positive_depths[0] if positive_depths else -1
+    frontier_margin = margins[frontier] if frontier >= 0 else 0
+    local_islands = [
+        depth
+        for depth in depths
+        if depth > r_start and margins[depth] > 0 and margins[depth - 1] <= 0 and margins[depth + 1] <= 0
+    ]
+    sign_change_up = [
+        depth
+        for depth in depths
+        if margins[depth] <= 0 and margins[depth + 1] > 0
+    ]
+    failure_pair = first_failure_pair(positive_depths, r_start)
+
+    return PressureSignPatternRow(
+        n=n,
+        steps=steps,
+        r_start=r_start,
+        depth_len=depth_len,
+        height_seq=join_ints(height_seq),
+        residual_shape_seq=join_ints(residual_shape_seq),
+        first_failed_depth_seq=join_ints(first_failed_depth_seq),
+        residual_mod_8_seq=join_ints([value % 8 for value in residual_shape_seq]),
+        residual_mod_16_seq=join_ints([value % 16 for value in residual_shape_seq]),
+        residual_mod_32_seq=join_ints([value % 32 for value in residual_shape_seq]),
+        positive_depths=join_ints(positive_depths),
+        positive_blocks=join_blocks(blocks),
+        positive_depth_count=len(positive_depths),
+        first_frontier_depth=frontier,
+        frontier_margin=frontier_margin,
+        local_islands=join_ints(local_islands),
+        local_island_count=len(local_islands),
+        sign_change_up_positions=join_ints(sign_change_up),
+        sign_change_up_count=len(sign_change_up),
+        first_failure_pair=(
+            "" if failure_pair is None else f"{failure_pair[0]}->{failure_pair[1]}"
+        ),
+        max_margin_jump=max_adjacent_jump(margins, depths),
+        max_retention_drop=max_adjacent_drop(retentions, depths),
+        max_continuation_drop=max_adjacent_drop(continuations, depths),
+        margin_profile=join_pairs([(depth, margins[depth]) for depth in depths]),
+        retention_profile=join_pairs([(depth, retentions[depth]) for depth in depths]),
+        continuation_profile=join_pairs(
+            [(depth, continuations[depth]) for depth in depths]
+        ),
+    )
+
+
+def scan(max_n: int, steps: int, r_start: int, depth_len: int) -> list[PressureSignPatternRow]:
+    return [row_for(n, steps, r_start, depth_len) for n in range(1, max_n + 1, 2)]
+
+
+def write_csv(rows: list[PressureSignPatternRow], path: Path) -> None:
+    path.parent.mkdir(parents=True, exist_ok=True)
+    with path.open("w", newline="", encoding="utf-8") as f:
+        writer = csv.DictWriter(
+            f,
+            fieldnames=list(PressureSignPatternRow.__dataclass_fields__),
+            lineterminator="\n",
+        )
+        writer.writeheader()
+        for row in rows:
+            writer.writerow(row.__dict__)
+
+
+def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
+    path.parent.mkdir(parents=True, exist_ok=True)
+    nonempty = [row for row in rows if row.positive_depth_count > 0]
+    with_island = [row for row in rows if row.local_island_count > 0]
+    with_sign_change = [row for row in rows if row.sign_change_up_count > 0]
+    block_rows = [row for row in rows if ";" in row.positive_blocks or "-" in row.positive_blocks]
+    max_positive = max((row.positive_depth_count for row in rows), default=0)
+    max_islands = max((row.local_island_count for row in rows), default=0)
+    max_sign_changes = max((row.sign_change_up_count for row in rows), default=0)
+    top_pressure = sorted(
+        nonempty,
+        key=lambda row: (-row.positive_depth_count, -row.frontier_margin, row.n),
+    )[:12]
+    top_islands = sorted(
+        with_island,
+        key=lambda row: (-row.local_island_count, -row.sign_change_up_count, row.n),
+    )[:12]
+    sign_samples = sorted(
+        with_sign_change,
+        key=lambda row: (-row.sign_change_up_count, -row.max_margin_jump, row.n),
+    )[:12]
+
+    lines = [
+        "# Collatz Pressure Sign Pattern Scan - Checkpoint 130",
+        "",
+        f"- rows: `{len(rows)}`",
+        f"- rows with positive pressure depths: `{len(nonempty)}`",
+        f"- rows with local islands: `{len(with_island)}`",
+        f"- rows with sign-change-up positions: `{len(with_sign_change)}`",
+        f"- rows with positive blocks: `{len(block_rows)}`",
+        f"- max positive depth count: `{max_positive}`",
+        f"- max local island count: `{max_islands}`",
+        f"- max sign-change-up count: `{max_sign_changes}`",
+        "",
+        "## Top Positive-Depth Samples",
+        "",
+        "| n | positive depths | blocks | frontier | frontier margin | islands | sign-up | margins |",
+        "|---:|---|---|---:|---:|---|---|---|",
+    ]
+    for row in top_pressure:
+        lines.append(
+            "| "
+            f"{row.n} | {row.positive_depths} | {row.positive_blocks} | "
+            f"{row.first_frontier_depth} | {row.frontier_margin} | "
+            f"{row.local_islands} | {row.sign_change_up_positions} | "
+            f"{row.margin_profile} |"
+        )
+
+    lines.extend(
+        [
+            "",
+            "## Local-Island Samples",
+            "",
+            "| n | islands | first failure pair | sign-up | height seq | first-failed seq | residual mod 16 |",
+            "|---:|---|---|---|---|---|---|",
+        ]
+    )
+    if top_islands:
+        for row in top_islands:
+            lines.append(
+                "| "
+                f"{row.n} | {row.local_islands} | {row.first_failure_pair} | "
+                f"{row.sign_change_up_positions} | {row.height_seq} | "
+                f"{row.first_failed_depth_seq} | {row.residual_mod_16_seq} |"
+            )
+    else:
+        lines.append("| - | none observed | - | - | - | - | - |")
+
+    lines.extend(
+        [
+            "",
+            "## Sign-Change-Up Samples",
+            "",
+            "| n | sign-up | margin jump | retention drop | continuation drop | margins | retentions | continuations |",
+            "|---:|---|---:|---:|---:|---|---|---|",
+        ]
+    )
+    if sign_samples:
+        for row in sign_samples:
+            lines.append(
+                "| "
+                f"{row.n} | {row.sign_change_up_positions} | "
+                f"{row.max_margin_jump} | {row.max_retention_drop} | "
+                f"{row.max_continuation_drop} | {row.margin_profile} | "
+                f"{row.retention_profile} | {row.continuation_profile} |"
+            )
+    else:
+        lines.append("| - | none observed | 0 | 0 | 0 | - | - | - |")
+
+    lines.extend(
+        [
+            "",
+            "## Reading",
+            "",
+            "The scan keeps time profiles and pressure-depth profiles separate.  The",
+            "current data should be used to decide whether the next Lean predicate is a",
+            "positive block, a local-island existence predicate, or a frontier-below",
+            "predicate.",
+            "",
+            "This is not evidence for an unconditional pressure-prefix theorem.  The",
+            "presence of local islands and sign-change-up rows means pressure is a",
+            "margin sign profile, not just carrier nesting.",
+            "",
+        ]
+    )
+    path.write_text("\n".join(lines), encoding="utf-8")
+
+
+def parse_args() -> argparse.Namespace:
+    parser = argparse.ArgumentParser()
+    parser.add_argument("--max-n", type=int, default=511)
+    parser.add_argument("--steps", type=int, default=64)
+    parser.add_argument("--r-start", type=int, default=2)
+    parser.add_argument("--depth-len", type=int, default=10)
+    parser.add_argument(
+        "--out-dir",
+        type=Path,
+        default=Path("python/Collatz/PetalBridge/results"),
+    )
+    return parser.parse_args()
+
+
+def main() -> None:
+    args = parse_args()
+    rows = scan(args.max_n, args.steps, args.r_start, args.depth_len)
+    csv_path = args.out_dir / "pressure_sign_pattern_scan.csv"
+    summary_path = args.out_dir / "pressure_sign_pattern_scan.md"
+    write_csv(rows, csv_path)
+    write_summary(rows, summary_path)
+    print(f"wrote {csv_path}")
+    print(f"wrote {summary_path}")
+
+
+if __name__ == "__main__":
+    main()
diff --git a/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md b/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
new file mode 100644
index 00000000..fde15131
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
@@ -0,0 +1,55 @@
+# Collatz Pressure Sign Pattern Scan - Checkpoint 130
+
+- rows: `1024`
+- rows with positive pressure depths: `511`
+- rows with local islands: `3`
+- rows with sign-change-up positions: `4`
+- rows with positive blocks: `132`
+- max positive depth count: `8`
+- max local island count: `1`
+- max sign-change-up count: `1`
+
+## Top Positive-Depth Samples
+
+| n | positive depths | blocks | frontier | frontier margin | islands | sign-up | margins |
+|---:|---|---|---:|---:|---|---|---|
+| 2047 | 2;3;4;5;6;7;8;9 | 2-9 | 2 | 9 |  |  | 2:9;3:11;4:9;5:6;6:3;7:2;8:2;9:1;10:0;11:-1 |
+| 1819 | 2;3;4;5;6;7;8;9 | 2-9 | 2 | 8 |  |  | 2:8;3:11;4:9;5:6;6:3;7:2;8:2;9:1;10:0;11:-1 |
+| 1915 | 2;3;4;5;6;7;8;9 | 2-9 | 2 | 6 |  |  | 2:6;3:11;4:9;5:6;6:3;7:2;8:2;9:1;10:0;11:-1 |
+| 1023 | 2;3;4;5;6;7;8 | 2-8 | 2 | 7 |  |  | 2:7;3:5;4:5;5:4;6:3;7:2;8:1;9:0;10:-1;11:0 |
+| 511 | 2;3;4;5;6;7 | 2-7 | 2 | 6 |  |  | 2:6;3:4;4:4;5:3;6:2;7:1;8:0;9:-1;10:0;11:0 |
+| 681 | 2;3;4;5;6;7 | 2-7 | 2 | 6 |  |  | 2:6;3:4;4:4;5:3;6:2;7:1;8:0;9:-1;10:0;11:0 |
+| 1535 | 2;3;4;5;6;7 | 2-7 | 2 | 6 |  |  | 2:6;3:4;4:4;5:3;6:2;7:1;8:0;9:-1;10:0;11:0 |
+| 895 | 2;3;4;5;6 | 2-6 | 2 | 9 |  |  | 2:9;3:6;4:4;5:3;6:1;7:-1;8:-1;9:0;10:0;11:0 |
+| 1193 | 2;3;4;5;6 | 2-6 | 2 | 9 |  |  | 2:9;3:6;4:4;5:3;6:1;7:-1;8:-1;9:0;10:0;11:0 |
+| 671 | 2;3;4;5;6 | 2-6 | 2 | 8 |  |  | 2:8;3:3;4:2;5:1;6:1;7:0;8:-1;9:0;10:0;11:0 |
+| 795 | 2;3;4;5;6 | 2-6 | 2 | 8 |  |  | 2:8;3:6;4:4;5:3;6:1;7:-1;8:-1;9:0;10:0;11:0 |
+| 1789 | 2;3;4;5;6 | 2-6 | 2 | 8 |  |  | 2:8;3:3;4:2;5:1;6:1;7:0;8:-1;9:0;10:0;11:0 |
+
+## Local-Island Samples
+
+| n | islands | first failure pair | sign-up | height seq | first-failed seq | residual mod 16 |
+|---:|---|---|---|---|---|---|
+| 1567 | 3 | 2->3 | 2 | 1;1;1;1;2;2;2;6;3;1;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;2;3;3;3;7;4;2;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 15;7;11;1;1;1;5;13;11;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 1639 | 5 | 4->5 | 4 | 1;1;2;1;1;1;3;1;1;1;2;4;1;1;1;1;1;1;2;1;1;2;5;2;1;1;7;2;1;4;1;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;3;2;2;2;4;2;2;2;3;5;2;2;2;2;2;2;3;2;2;3;6;3;2;2;8;3;2;5;2;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 11;9;15;7;3;13;15;7;11;1;5;15;15;15;15;7;11;9;7;11;1;5;9;7;3;5;9;3;5;3;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+| 1775 | 5 | 4->5 | 4 | 1;1;1;2;1;1;1;4;3;1;2;2;4;2;1;1;1;1;1;1;2;4;3;3;3;1;2;3;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2;2 | 2;2;2;3;2;2;2;5;4;2;3;3;5;3;2;2;2;2;2;2;3;5;4;4;4;2;3;4;5;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3 | 7;11;9;15;7;3;5;13;11;1;1;5;9;15;15;15;15;7;11;1;5;13;13;13;11;1;13;5;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1 |
+
+## Sign-Change-Up Samples
+
+| n | sign-up | margin jump | retention drop | continuation drop | margins | retentions | continuations |
+|---:|---|---:|---:|---:|---|---|---|
+| 1567 | 2 | 3 | 5 | 1 | 2:-2;3:1;4:0;5:-1;6:0;7:0;8:0;9:0;10:0;11:0 | 2:8;3:3;4:2;5:1;6:0;7:0;8:0;9:0;10:0;11:0 | 2:3;3:2;4:1;5:0;6:0;7:0;8:0;9:0;10:0;11:0 |
+| 1639 | 4 | 3 | 9 | 6 | 2:3;3:0;4:0;5:1;6:0;7:-1;8:0;9:0;10:0;11:0 | 2:21;3:12;4:6;5:3;6:2;7:1;8:0;9:0;10:0;11:0 | 2:12;3:6;4:3;5:2;6:1;7:0;8:0;9:0;10:0;11:0 |
+| 1775 | 4 | 3 | 5 | 3 | 2:4;3:3;4:0;5:1;6:0;7:-1;8:0;9:0;10:0;11:0 | 2:14;3:9;4:6;5:3;6:2;7:1;8:0;9:0;10:0;11:0 | 2:9;3:6;4:3;5:2;6:1;7:0;8:0;9:0;10:0;11:0 |
+| 1899 | 2 | 3 | 5 | 1 | 2:0;3:3;4:2;5:1;6:0;7:-1;8:0;9:0;10:0;11:0 | 2:10;3:5;4:4;5:3;6:2;7:1;8:0;9:0;10:0;11:0 | 2:5;3:4;4:3;5:2;6:1;7:0;8:0;9:0;10:0;11:0 |
+
+## Reading
+
+The scan keeps time profiles and pressure-depth profiles separate.  The
+current data should be used to decide whether the next Lean predicate is a
+positive block, a local-island existence predicate, or a frontier-below
+predicate.
+
+This is not evidence for an unconditional pressure-prefix theorem.  The
+presence of local islands and sign-change-up rows means pressure is a
+margin sign profile, not just carrier nesting.
````
`````
