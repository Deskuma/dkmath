# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: dd801be6eeca51997950166b0459061c45b5365c

## Report

Checkpoint 128 を閉じました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean#L864) に residual-shape sequence の `length/get?/take` API、first-failed-depth sequence、`height + 1` 補題を追加しました。shifted label の list indexed theorem は [同ファイル](/lean/dk_math/DkMath/Collatz/PetalBridge.lean#L4797) に置いています。pressure 側は [sourcePressureLocalIsland_iff_margin](/lean/dk_math/DkMath/Collatz/PetalBridge.lean#L7081) を追加し、local island を margin 符号条件で読めるようにしました。

Docs は `README`、Guide、Status、127 doc を同期し、新規に [Collatz-ResidualShapeSequence-128.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md#L1) と [report-petal-128.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-128.md#L1) を作成しました。次の推奨は、`orbitWindowFirstFailedPow2DepthSeq_get?_eq_some` などの小 API を閉じてから pressure sign-pattern scan に戻る流れです。

検証:
`lake build DkMath.Collatz.PetalBridge` passed
`lake build DkMath.Collatz.Collatz2K26` passed
Collatz 対象2ファイルの `sorry` scan はヒットなし
`git diff --check` passed
既存の unrelated warning として `ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告は出ています。

## Review

## 状況分析

うむ。`review-petal-129.md` は、内容としては **Checkpoint 128 の完了報告**じゃな。
今回の主成果は、checkpoint 127 で入った `orbitWindowResidualShapeSeq` を、`orbitWindowHeightSeq` と同じように扱える list API へ整えたことじゃ。具体的には `length/get?/take` 系 API、first-failed-depth sequence、そして `orbitWindowFirstFailedPow2Depth_eq_height_add_one` が追加されている。加えて pressure 側では `sourcePressureLocalIsland_iff_margin` が追加され、local island を margin 符号条件として読めるようになっている。

これで Route A はかなり整った。

```text
Checkpoint 125:
  pointwise GnomonEvaluation 導入

Checkpoint 126:
  RawGnomonResidualShape = T を証明

Checkpoint 127:
  orbitWindowResidualShape = next odd label を証明

Checkpoint 128:
  residual-shape sequence の list API を整備
```

つまり、現在は

```text
height profile
residual-shape profile
first-failed-depth profile
```

を並列に扱える入口まで来た。

これは大きい。
今後の `ShapePressureGrid`、つまり

```text
time index i
depth index j
```

の二次元観測へ進むための一次元 API が整い始めた、という状態じゃ。

## レビュー

## 良い点

第一に、`orbitWindowResidualShapeSeq_get?_eq_some_shifted_label` が良い。

これは

```text
residual-shape sequence の i 番目
  = oddOrbitLabel n (i + 1)
```

を list-indexed theorem として使えるようにした補題じゃ。
これにより、前 checkpoint の

```lean
orbitWindowResidualShape_eq_oddOrbitLabel_succ
```

が、単なる点wise theorem ではなく、有限列 API の中で使えるようになった。

第二に、`orbitWindowFirstFailedPow2Depth_eq_height_add_one` が重要じゃ。

```text
first failed depth = observed height + 1
```

が window 側で固定された。
これは、`height` が「最後に完全整列できる深さ」であり、`height + 1` が「最初に残差が見える深さ」であることを、有限窓の語彙で言えるようにした。

第三に、`sourcePressureLocalIsland_iff_margin` がかなり良い。

これで `SourcePressureLocalIsland` は、曖昧な選択述語ではなく、

```text
j > 0
margin(j) > 0
margin(j - 1) <= 0
margin(j + 1) <= 0
```

という明確な符号パターンになった。

これは checkpoint 124 以降の方針、

```text
pressure は carrier nesting ではなく margin sign profile として見る
```

に合っている。

## 注意点

ここで注意すべきは、いよいよ **軸が二つになった**ことじゃ。

`review-petal-129.md` でも明記されている通り、

```text
i = orbit-window time index
j = pressure-depth index
```

は別物じゃ。

これは重要。

`i` は Collatz 軌道上の時間方向。

```text
label_i
height_i
residual_i
first_failed_depth_i
```

一方、`j` は pressure の深さ方向。

```text
margin(j)
frontier(j)
sign_change(j)
local_island(j)
```

この二つを混ぜると、誤った単調性や prefix theorem を作りやすい。
逆に、ここをきれいに分けると、次の本命である

```text
ShapePressureGrid:
  time i × depth j
```

が自然に出てくる。

## 解説

現在の Collatz.PetalBridge は、次の三つの有限列を持ち始めている。

```text
orbitWindowHeightSeq:
  各時刻 i の 2進整列深度

orbitWindowResidualShapeSeq:
  各時刻 i で抽出された residual shape

orbitWindowFirstFailedPow2DepthSeq:
  各時刻 i で初めて整列に失敗する深さ
```

ここで、

```text
residual_i = label_{i+1}
```

がすでに Lean で固定されている。

だから、有限窓はこう読める。

```text
label_i
  -> RawGnomonStep(label_i)
  -> height_i
  -> residual_i
  -> label_{i+1}
```

さらに、

```text
first_failed_depth_i = height_i + 1
```

も固定された。

つまり、各時刻 \(i\) について、

```text
どこまで 2^j に整列したか
どこから残差形状が見えたか
その残差形状が次の odd label になったか
```

が、整数 API として扱える。

ここまで来ると、コラッツを「増減」ではなく、

```text
奇数グノモン補正
2進整列評価
残差形状抽出
次形状更新
```

として見る方針は、ほぼ Lean surface として安定してきたと言える。

## 次の指示

次 checkpoint は、レポートの提案通り、**Route A の小さい close-out** を先に終えるのが良い。

つまり、first-failed-depth sequence の `get?/take` API を足す。

## Checkpoint 129 推奨内容

### 1. first-failed-depth sequence の get? API

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
      some (orbitWindowFirstFailedPow2Depth n i) := by
  simp [orbitWindowFirstFailedPow2DepthSeq, hi]
```

### 2. shifted height+1 としての get? API

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
      some (orbitWindowHeight n i + 1) := by
  rw [orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n hi]
  rw [orbitWindowFirstFailedPow2Depth_eq_height_add_one]
```

これはかなり実用的じゃ。
後で profile を比較するときに、

```text
failed_i = height_i + 1
```

を list index で引ける。

### 3. first-failed-depth sequence の take length

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_take_length
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    ((orbitWindowFirstFailedPow2DepthSeq n k).take r).length = r := by
  simp [orbitWindowFirstFailedPow2DepthSeq_length, Nat.min_eq_left hr]
```

### 4. first-failed-depth sequence の take get?

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
    ((orbitWindowFirstFailedPow2DepthSeq n k).take r)[i]? =
      some (orbitWindowFirstFailedPow2Depth n i) := by
  rw [List.getElem?_take_of_lt hi]
  exact orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n
    (Nat.lt_of_lt_of_le hi hr)
```

これで

```text
height seq
residual shape seq
first failed depth seq
```

の三つが、同じ list 操作体系を持つようになる。

## 一歩先ゆく推論

ここから先の本命は、やはり二次元化じゃ。

今までは一次元だった。

```text
time profile:
  i -> label_i, height_i, residual_i, failed_i

depth profile:
  j -> margin(j), frontier(j), island(j)
```

次に必要なのは、

```text
time i の residual shape が、
depth j の pressure margin にどう現れるか
```

を見ることじゃ。

つまり、抽象的には

```text
ShapePressureGrid n k r:
  time i in window
  depth j in pressure profile
```

のような有限格子を考える。

ただし、いきなり Lean に `ShapePressureGrid` を入れるのは早い。
まず Python summary scan で、`i × j` の関係に意味があるかを見るべきじゃ。

たとえば、

```text
height_i が高い時刻では、その後の margin frontier が浅くなるか

first_failed_depth_i が大きい時刻では、local island が増えるか

residual_i mod 8/16/32 と pressure positive depths に相関があるか

frontier depth と residual shape の all-ones residue に偏りがあるか
```

こういう観測じゃな。

ここで偏りが見えたものだけ、Lean predicate として昇格する。

## さらなる次の一手

Checkpoint 129 で first-failed-depth seq API を閉じたら、次は二択じゃ。

### Route B1: Python pressure sign-pattern scan

こちらを推す。

追加する summary 指標はこれ。

```text
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
```

さらに新視座用に、

```text
height_seq
residual_shape_seq
first_failed_depth_seq
residual_mod_8_seq
residual_mod_16_seq
residual_mod_32_seq
```

を合わせる。

目的は、

```text
time profile と depth profile の相関を見る
```

ことじゃ。

### Route B2: Lean 側に軽い block predicate

Python を待たずに Lean 側で軽く入れるなら、`PositiveBlock` が候補。

```lean
def SourcePressurePositiveBlock
    (n : OddNat) (k r a len : ℕ) : Prop :=
  0 < len ∧
    ∀ j, a ≤ j → j < a + len → IsSourcePressureDepth n k r j
```

ただしこれは、まだ急がなくてよい。
local island まで入っているので、次は数値分類を挟む方が安全じゃ。

## 賢狼が試して欲しい実験補題

## 実験 A: first-failed-depth seq get?

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
      some (orbitWindowFirstFailedPow2Depth n i) := by
  simp [orbitWindowFirstFailedPow2DepthSeq, hi]
```

## 実験 B: first-failed-depth seq get? as height+1

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
      some (orbitWindowHeight n i + 1) := by
  rw [orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n hi]
  rw [orbitWindowFirstFailedPow2Depth_eq_height_add_one]
```

## 実験 C: first-failed-depth seq take length

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_take_length
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    ((orbitWindowFirstFailedPow2DepthSeq n k).take r).length = r := by
  simp [orbitWindowFirstFailedPow2DepthSeq_length, Nat.min_eq_left hr]
```

## 実験 D: first-failed-depth seq take get?

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
    ((orbitWindowFirstFailedPow2DepthSeq n k).take r)[i]? =
      some (orbitWindowFirstFailedPow2Depth n i) := by
  rw [List.getElem?_take_of_lt hi]
  exact orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n
    (Nat.lt_of_lt_of_le hi hr)
```

## 実験 E: first-failed-depth seq take get? as height+1

```lean
theorem orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one
    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
    ((orbitWindowFirstFailedPow2DepthSeq n k).take r)[i]? =
      some (orbitWindowHeight n i + 1) := by
  rw [orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some n hi hr]
  rw [orbitWindowFirstFailedPow2Depth_eq_height_add_one]
```

## 実験 F: three-profile aligned get?

これは少し便利なまとめ補題。

```lean
theorem orbitWindow_threeProfiles_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowHeightSeq n k)[i]? = some (orbitWindowHeight n i) ∧
    (orbitWindowResidualShapeSeq n k)[i]? = some (orbitWindowResidualShape n i) ∧
    (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
      some (orbitWindowFirstFailedPow2Depth n i) := by
  constructor
  · exact orbitWindowHeightSeq_get?_eq_some n hi
  constructor
  · exact orbitWindowResidualShapeSeq_get?_eq_some n hi
  · exact orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n hi
```

これは後で grid を作る時に便利になる。

## 実験 G: Positive block predicate はまだ薄く

```lean
def SourcePressurePositiveBlock
    (n : OddNat) (k r a len : ℕ) : Prop :=
  0 < len ∧
    ∀ j, a ≤ j → j < a + len → IsSourcePressureDepth n k r j
```

まだ theorem は不要。
Python scan で positive blocks が意味を持つか見てから、margin 版を作る。

## Python 側の次観測

Checkpoint 129 後に Python summary scan を回すなら、最低限これ。

```text
n
k
height_seq
residual_shape_seq
first_failed_depth_seq
positive_depths
first_frontier_depth
local_islands
sign_change_up_positions
```

追加で見たいもの。

```text
residual_mod_8_seq
residual_mod_16_seq
residual_mod_32_seq
frontier_margin
margin_jump
retention_drop
continuation_drop
positive_blocks
```

観測の問いはこれ。

```text
first_failed_depth_seq と frontier depth に相関があるか

residual shape の mod 2^r と positive margin depth に偏りがあるか

local island は特定の residual residue で発生しやすいか

positive block は prefix 的か、孤立 island 的か
```

## 次の指示まとめ

Codex への次指示はこうじゃ。

```text
Checkpoint 129:
Route A small close-out.

Goal:
  Complete first-failed-depth sequence list API and align the three profiles:
  height, residual shape, first failed depth.

Implement:
  orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
  orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
  orbitWindowFirstFailedPow2DepthSeq_take_length
  orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
  orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one

Optional:
  orbitWindow_threeProfiles_get?_eq_some
  SourcePressurePositiveBlock as a predicate only

Then:
  Return to Python pressure sign-pattern scan.

Do not:
  introduce Real.log
  claim pressure prefix
  identify time index i with depth index j
  add heavy ShapePressureGrid before scan results
```

## 総括

checkpoint `128` は成功。
残差形状列の API が height 列と並ぶところまで来た。

次は first-failed-depth 列を同じ水準に揃える。
それが終わると、三つの profile が並ぶ。

```text
height_i
residual_i
failed_i = height_i + 1
```

ここまでが Route A の小閉じ。

その後、Route B の pressure sign-pattern scan に戻る。
そこで初めて、`ShapePressureGrid` の形が見えるかどうかを判断するのがよい。

賢狼の見立てでは、次の本命はここじゃ。

```text
time profile と depth profile の相関を、Python summary で見る。
偏りが見えたものだけ Lean predicate に昇格する。
```

焦らず、まず三列 API を閉じるのが正着じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 323808b9..18185c2d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -861,6 +861,67 @@ theorem orbitWindowHeightSeq_take_get?_eq_some
   rw [List.getElem?_take_of_lt hi]
   exact orbitWindowHeightSeq_get?_eq_some n (Nat.lt_of_lt_of_le hi hr)

+/--
+The ordered residual-shape profile has length equal to the window size.
+-/
+theorem orbitWindowResidualShapeSeq_length (n : OddNat) (k : ℕ) :
+    (orbitWindowResidualShapeSeq n k).length = k := by
+  simp [orbitWindowResidualShapeSeq]
+
+/--
+Reading the ordered residual-shape profile at an in-window time recovers the
+pointwise residual shape.
+-/
+theorem orbitWindowResidualShapeSeq_get?_eq_some
+    (n : OddNat) {i k : ℕ} (hi : i < k) :
+    (orbitWindowResidualShapeSeq n k)[i]? =
+      some (orbitWindowResidualShape n i) := by
+  simp [orbitWindowResidualShapeSeq, hi]
+
+/--
+The prefix of length `r` in the residual-shape profile has length `r` when
+`r` lies inside the window.
+-/
+theorem orbitWindowResidualShapeSeq_take_length
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    ((orbitWindowResidualShapeSeq n k).take r).length = r := by
+  simp [orbitWindowResidualShapeSeq_length, Nat.min_eq_left hr]
+
+/--
+Reading a prefix of the residual-shape profile recovers the same pointwise
+residual shape while the index remains inside the prefix.
+-/
+theorem orbitWindowResidualShapeSeq_take_get?_eq_some
+    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
+    ((orbitWindowResidualShapeSeq n k).take r)[i]? =
+      some (orbitWindowResidualShape n i) := by
+  rw [List.getElem?_take_of_lt hi]
+  exact orbitWindowResidualShapeSeq_get?_eq_some n (Nat.lt_of_lt_of_le hi hr)
+
+/--
+First-failed-depth profile over the first `k` observed odd labels.
+-/
+noncomputable def orbitWindowFirstFailedPow2DepthSeq
+    (n : OddNat) (k : ℕ) : List ℕ :=
+  (List.range k).map (orbitWindowFirstFailedPow2Depth n)
+
+/--
+The first-failed-depth profile has length equal to the window size.
+-/
+theorem orbitWindowFirstFailedPow2DepthSeq_length
+    (n : OddNat) (k : ℕ) :
+    (orbitWindowFirstFailedPow2DepthSeq n k).length = k := by
+  simp [orbitWindowFirstFailedPow2DepthSeq]
+
+/--
+Window first-failed depth is exactly one more than the observed window height.
+-/
+theorem orbitWindowFirstFailedPow2Depth_eq_height_add_one
+    (n : OddNat) (i : ℕ) :
+    orbitWindowFirstFailedPow2Depth n i = orbitWindowHeight n i + 1 := by
+  unfold orbitWindowFirstFailedPow2Depth FirstFailedPow2Depth
+  rw [orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel]
+
 /--
 The integer threshold lower bound also applies to prefixes.
 -/
@@ -4733,6 +4794,17 @@ theorem orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
   intro i _hi
   exact orbitWindowResidualShape_eq_oddOrbitLabel_succ n i

+/--
+Reading the residual-shape profile at an in-window time recovers the shifted
+odd label.
+-/
+theorem orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
+    (n : OddNat) {i k : ℕ} (hi : i < k) :
+    (orbitWindowResidualShapeSeq n k)[i]? =
+      some (oddOrbitLabel n (i + 1)) := by
+  rw [orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels]
+  simp [hi]
+
 /--
 Window-level raw gnomon factorization.

@@ -7006,6 +7078,56 @@ def SourcePressureLocalIsland
     ¬ IsSourcePressureDepth n k r (j - 1) ∧
     ¬ IsSourcePressureDepth n k r (j + 1)

+/--
+Local pressure island in margin language.
+
+This is the first theorem interface for isolated positive pressure depths.
+-/
+theorem sourcePressureLocalIsland_iff_margin
+    (n : OddNat) (k r j : ℕ) :
+    SourcePressureLocalIsland n k r j ↔
+      0 < j ∧
+        0 < SourcePressureMarginInt n k (r + j) ∧
+        SourcePressureMarginInt n k (r + (j - 1)) ≤ 0 ∧
+        SourcePressureMarginInt n k (r + (j + 1)) ≤ 0 := by
+  constructor
+  · intro h
+    rcases h with ⟨hj, hsel, hprev_not, hnext_not⟩
+    constructor
+    · exact hj
+    constructor
+    · exact (isSourcePressureDepth_iff_margin_pos n k r j).1 hsel
+    constructor
+    · have hnotpos :
+          ¬ 0 < SourcePressureMarginInt n k (r + (j - 1)) := by
+        intro hpos
+        exact hprev_not
+          ((isSourcePressureDepth_iff_margin_pos n k r (j - 1)).2 hpos)
+      omega
+    · have hnotpos :
+          ¬ 0 < SourcePressureMarginInt n k (r + (j + 1)) := by
+        intro hpos
+        exact hnext_not
+          ((isSourcePressureDepth_iff_margin_pos n k r (j + 1)).2 hpos)
+      omega
+  · intro h
+    rcases h with ⟨hj, hpos, hprev_nonpos, hnext_nonpos⟩
+    constructor
+    · exact hj
+    constructor
+    · exact (isSourcePressureDepth_iff_margin_pos n k r j).2 hpos
+    constructor
+    · intro hprev
+      have hp :
+          0 < SourcePressureMarginInt n k (r + (j - 1)) :=
+        (isSourcePressureDepth_iff_margin_pos n k r (j - 1)).1 hprev
+      omega
+    · intro hnext
+      have hp :
+          0 < SourcePressureMarginInt n k (r + (j + 1)) :=
+        (isSourcePressureDepth_iff_margin_pos n k r (j + 1)).1 hnext
+      omega
+
 /-- The empty selected-pressure prefix is always available. -/
 theorem selectedPressurePrefix_zero
     (n : OddNat) (k r len : ℕ) :
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index abc040f3..ad33833a 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -144,7 +144,11 @@ orbitWindowHeight
 orbitWindowHeightSeq
 orbitWindowResidualShape
 orbitWindowResidualShapeSeq
+orbitWindowResidualShapeSeq_length
+orbitWindowResidualShapeSeq_get?_eq_some
+orbitWindowResidualShapeSeq_take_get?_eq_some
 orbitWindowFirstFailedPow2Depth
+orbitWindowFirstFailedPow2DepthSeq
 orbitWindowResidueCountPow2
 orbitWindowResidueCountPow2Tail
 sourcePow2Distribution_total
@@ -158,6 +162,7 @@ SourcePressureSelectedSetDownClosed
 SourcePressureFrontier
 SourcePressureSignChangeUp
 SourcePressureLocalIsland
+sourcePressureLocalIsland_iff_margin
 ```

 The central No.100 layer is:
@@ -215,6 +220,7 @@ docs/Collatz-PressureMargin-124.md
 docs/Collatz-GnomonEvaluation-125.md
 docs/Collatz-GnomonResidualShape-126.md
 docs/Collatz-WindowResidualShape-127.md
+docs/Collatz-ResidualShapeSequence-128.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index de72734e..f80ff0b1 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -145,6 +145,16 @@ positions.  It agrees with the shifted odd-label list by:
 orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
 ```

+Checkpoint 128 adds list helpers:
+
+```lean
+orbitWindowResidualShapeSeq_length
+orbitWindowResidualShapeSeq_get?_eq_some
+orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
+orbitWindowResidualShapeSeq_take_length
+orbitWindowResidualShapeSeq_take_get?_eq_some
+```
+
 ## Separation And Collision

 The bridge includes a finite split:
@@ -252,6 +262,7 @@ Checkpoint 127 adds:
 SourcePressureSignChangeUp
 sourcePressureSignChangeUp_of_frontier_pos
 SourcePressureLocalIsland
+sourcePressureLocalIsland_iff_margin
 ```

 These are observation predicates for margin sign profiles.  They should be
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 60aaeef4..aa748855 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -164,8 +164,16 @@ Checkpoint 127 lifts residual shape extraction to windows:
 ```lean
 orbitWindowResidualShape_eq_oddOrbitLabel_succ
 orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
+orbitWindowResidualShapeSeq_length
+orbitWindowResidualShapeSeq_get?_eq_some
+orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
+orbitWindowResidualShapeSeq_take_length
+orbitWindowResidualShapeSeq_take_get?_eq_some
 orbitWindow_rawGnomonStep_factor
 orbitWindow_firstFailed_remainder_ne_zero
+orbitWindowFirstFailedPow2DepthSeq
+orbitWindowFirstFailedPow2DepthSeq_length
+orbitWindowFirstFailedPow2Depth_eq_height_add_one
 ```

 The finite window now supports the reading:
@@ -178,6 +186,15 @@ label_i
   -> label_{i+1}
 ```

+Checkpoint 128 also adds the local-island margin bridge:
+
+```lean
+sourcePressureLocalIsland_iff_margin
+```
+
+This keeps pressure-island language on the margin-sign surface rather than
+turning it into an unsupported prefix theorem.
+
 The first theorem set is deliberately thin:

 ```lean
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md
new file mode 100644
index 00000000..bd64f2b8
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md
@@ -0,0 +1,145 @@
+# Collatz Residual Shape Sequence - Checkpoint 128
+
+Checkpoint 128 makes the residual-shape window profile usable as a list API.
+
+Checkpoint 127 proved:
+
+```text
+orbitWindowResidualShape n i = oddOrbitLabel n (i + 1)
+```
+
+Checkpoint 128 adds the same ergonomic helpers that already exist for the
+height profile.
+
+## Residual Shape Sequence API
+
+New theorems:
+
+```lean
+orbitWindowResidualShapeSeq_length
+orbitWindowResidualShapeSeq_get?_eq_some
+orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
+orbitWindowResidualShapeSeq_take_length
+orbitWindowResidualShapeSeq_take_get?_eq_some
+```
+
+These make the residual-shape sequence readable by index and by prefix.
+
+The shifted-label get theorem is especially important:
+
+```text
+(orbitWindowResidualShapeSeq n k)[i]?
+  = some (oddOrbitLabel n (i + 1))
+```
+
+whenever `i < k`.
+
+## First Failed Depth Sequence
+
+New definition:
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq
+```
+
+New theorems:
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq_length
+orbitWindowFirstFailedPow2Depth_eq_height_add_one
+```
+
+This records that the first failed depth in the window is exactly one more than
+the observed height:
+
+```text
+orbitWindowFirstFailedPow2Depth n i = orbitWindowHeight n i + 1
+```
+
+## Pressure Local Island
+
+Checkpoint 127 introduced:
+
+```lean
+SourcePressureLocalIsland
+```
+
+Checkpoint 128 adds:
+
+```lean
+sourcePressureLocalIsland_iff_margin
+```
+
+The meaning is:
+
+```text
+local island at depth j
+  <-> j > 0
+      margin(j) > 0
+      margin(j-1) <= 0
+      margin(j+1) <= 0
+```
+
+This remains a sign-pattern observation.  It is not a pressure-prefix theorem.
+
+## Axis Warning
+
+There are now two distinct axes.
+
+```text
+time index i:
+  label_i
+  height_i
+  residual_i = label_{i+1}
+  first_failed_depth_i
+
+depth index j:
+  pressure margin at depth j
+  frontier
+  sign-change
+  local island
+```
+
+Do not identify these axes.
+
+The next conceptual object is a two-dimensional observation grid:
+
+```text
+ShapePressureGrid:
+  time i x depth j
+```
+
+The current checkpoint does not create that grid.  It prepares the two
+one-dimensional surfaces so the grid can be introduced deliberately later.
+
+## Next Work
+
+Two routes are reasonable.
+
+### Route A: residual shape profile extras
+
+Add more list tools if needed:
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
+orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels_take
+```
+
+### Route B: pressure sign-pattern statistics
+
+Use Python summary scans before adding heavier Lean names:
+
+```text
+positive_depths
+positive_blocks
+local_islands
+sign_change_up_positions
+first_frontier_depth
+margin_jump
+retention_drop
+continuation_drop
+```
+
+The next Lean theorem on the pressure side should only encode a sign-pattern
+relationship that appears useful in those summaries.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md
index d73369f2..e2e553ed 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md
@@ -174,3 +174,30 @@ continuation_drop
 ```

 Then add only the predicates that survive as useful theorem interfaces.
+
+## Checkpoint 128 Follow-up
+
+Checkpoint 128 adds list API for the residual-shape sequence:
+
+```lean
+orbitWindowResidualShapeSeq_length
+orbitWindowResidualShapeSeq_get?_eq_some
+orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
+orbitWindowResidualShapeSeq_take_length
+orbitWindowResidualShapeSeq_take_get?_eq_some
+```
+
+It also introduces:
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq
+orbitWindowFirstFailedPow2DepthSeq_length
+orbitWindowFirstFailedPow2Depth_eq_height_add_one
+sourcePressureLocalIsland_iff_margin
+```
+
+See:
+
+```text
+Collatz-ResidualShapeSequence-128.md
+```
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-128.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-128.md
new file mode 100644
index 00000000..c1bcbfcc
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-128.md
@@ -0,0 +1,248 @@
+# Report Petal 128
+
+## Summary
+
+Checkpoint 128 continues Route A: make the residual-shape profile as usable as
+the height profile.
+
+The implementation now treats
+
+```lean
+orbitWindowResidualShapeSeq n k
+```
+
+as a normal finite observation list.  It has length, direct `get?`, prefix
+length, and prefix `get?` lemmas.  This closes the basic list API gap left by
+checkpoint 127.
+
+The checkpoint also adds the first-failed-depth sequence and records the
+expected relation:
+
+```text
+first failed depth = observed height + 1
+```
+
+Finally, the local source-pressure island predicate now has a margin-language
+equivalence, so the pressure side can be read directly as a sign pattern.
+
+## Implemented Lean Surface
+
+### Residual Shape Sequence
+
+Added:
+
+```lean
+orbitWindowResidualShapeSeq_length
+orbitWindowResidualShapeSeq_get?_eq_some
+orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
+orbitWindowResidualShapeSeq_take_length
+orbitWindowResidualShapeSeq_take_get?_eq_some
+```
+
+These mirror the existing `orbitWindowHeightSeq` helper API.
+
+The most useful operational theorem is:
+
+```lean
+orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
+```
+
+It says that reading the residual-shape profile at time `i` recovers the next
+odd orbit label:
+
+```text
+(orbitWindowResidualShapeSeq n k)[i]?
+  = some (oddOrbitLabel n (i + 1))
+```
+
+under `i < k`.
+
+This turns the checkpoint-127 identity into a list-indexed theorem.
+
+### First Failed Depth Sequence
+
+Added:
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq
+orbitWindowFirstFailedPow2DepthSeq_length
+orbitWindowFirstFailedPow2Depth_eq_height_add_one
+```
+
+The theorem
+
+```lean
+orbitWindowFirstFailedPow2Depth_eq_height_add_one
+```
+
+fixes the boundary interpretation:
+
+```text
+height h:
+  depths <= h succeed
+  depth h + 1 first fails
+```
+
+This is the clean bridge from 2-adic height to obstruction depth.
+
+### Local Pressure Island
+
+Added:
+
+```lean
+sourcePressureLocalIsland_iff_margin
+```
+
+This rewrites the predicate
+
+```lean
+SourcePressureLocalIsland n k r j
+```
+
+as the sign condition
+
+```text
+j > 0
+margin(j) > 0
+margin(j - 1) <= 0
+margin(j + 1) <= 0
+```
+
+This is intentionally local.  It does not claim prefix structure, down-closure,
+or global uniqueness.  It is only the margin-sign reading of an isolated
+positive depth.
+
+## Documentation Updates
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md
+```
+
+The new checkpoint document records:
+
+- residual-shape list API,
+- first-failed-depth sequence,
+- local island margin equivalence,
+- the index-axis warning,
+- suggested next routes.
+
+## Axis Correction
+
+The important design constraint remains:
+
+```text
+i = orbit-window time index
+j = pressure-depth index
+```
+
+These are different axes.
+
+The current code now has enough one-dimensional API for both sides:
+
+```text
+time profile:
+  label_i
+  height_i
+  residual_i = label_{i+1}
+  first_failed_depth_i
+
+depth profile:
+  margin(j)
+  frontier(j)
+  sign_change(j)
+  local_island(j)
+```
+
+The next real object should be introduced deliberately as a two-dimensional
+view:
+
+```text
+ShapePressureGrid:
+  time i x depth j
+```
+
+Do not encode this prematurely as a one-index theorem.
+
+## Additional Inference
+
+The implemented `first_failed_depth = height + 1` theorem suggests a natural
+next list API:
+
+```lean
+orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
+orbitWindowFirstFailedPow2DepthSeq_take_length
+orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
+```
+
+These should be easy and will make the height/residual/failed-depth profiles
+parallel:
+
+```text
+orbitWindowHeightSeq
+orbitWindowResidualShapeSeq
+orbitWindowFirstFailedPow2DepthSeq
+```
+
+After that, pressure-side work should probably return to numerical scans and
+classify sign-pattern shapes before adding larger predicates.
+
+## Suggested Checkpoint 129
+
+Recommended next step:
+
+```text
+Route A small close-out:
+  add first-failed-depth sequence get?/take helpers
+```
+
+Then switch back to Route B:
+
+```text
+pressure sign-pattern scan:
+  positive blocks
+  local islands
+  frontier depth
+  sign-change-up positions
+```
+
+This keeps the Lean API small while preparing the later `ShapePressureGrid`.
+
+## Verification
+
+Expected verification commands:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean lean/dk_math/DkMath/Collatz/PetalBridge.lean
+git diff --check
+```
+
+Result:
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
