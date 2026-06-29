# Git diff / Report / Review

## Add: Analysis.DkReal.Arithmetic

gch: f92c977b46aed70910c6bdeca89c781634c4ac19

## Report

非負 DkReal の加法・乗法を実装しました。

- [Arithmetic.lean](/lean/dk_math/DkMath/Analysis/DkReal/Arithmetic.lean:24)
  - 一般加法 `add`
  - 非負乗法 `mulNonneg`
  - 非負性保存
  - 有理数埋め込み、零、一の簡約定理
- [Interval.lean](/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean:68)
  - 区間加法・非負乗法
  - 加法幅公式
  - 乗法幅公式 `bd - ac = b(d-c) + c(b-a)`
- 公開入口と研究ドキュメントも更新

乗法の幅収束は「零へ収束する幅 × 有界な端点」の和として証明しています。引き続き `noncomputable` は DkReal 層にありません。

検証済み:

```text
lake build DkMath.Analysis.DkReal.Arithmetic
lake build DkMath.Analysis DkMath
git diff --check
```

すべて成功しました。既存リポジトリ由来の `sorry` 警告のみ残っています。

## Review

うむ、二つまとめて見るぞい。
結論から言えば、今回の二段差分は **合格** じゃ。しかも、`DkReal` が「冪だけ閉じた試作」から、 **非負 ordered semiring の核** へ進み始めた差分じゃな。

## 1. 全体評価

今回の 2 差分は、流れとしてかなり良い。

```text id="i5yskt"
1. DkReal 非負自然数冪 milestone の記録と API 整理
2. DkReal の加法と非負乗法の実装
```

第一差分では、`powNonneg` の節目を文書化し、`GapInterval.ext` と `powNonneg` の基本簡約を追加している。報告でも、`GapInterval.ext`、有理数・0乗・1乗の簡約、観測レポートの追加、`noncomputable` 不在確認、build 成功が記録されている。

第二差分では、`DkMath.Analysis.DkReal.Arithmetic` が追加され、一般加法 `add`、非負乗法 `mulNonneg`、非負性保存、有理数埋め込み・零・一の簡約が実装されたと報告されている。区間側にも加法・非負乗法・幅公式が追加され、build も成功している。

これは設計書で言う「GapInterval 演算を DkReal の近似列へ持ち上げる」段階に明確に到達している。設計書も第二マイルストーンとして、`DkReal` 入れ子区間列の定義と、GapInterval 演算の DkReal 近似列への持ち上げを掲げていた。

## 2. 差分 1. Nonnegative Power Milestone

### 2.1. `GapInterval.ext` は良い

`GapInterval.ext` を入れたのは良い判断じゃ。

```lean id="ipgpnu"
@[ext]
theorem ext {I J : GapInterval} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J
```

これで、以後の interval equality は endpoint equality に還元できる。実際、`powNonneg_ofRat_interval`、`powNonneg_zero_interval`、`powNonneg_one_interval` が `GapInterval.ext` と `simp` で綺麗に落ちている。

これは小さいようで、Lean 実装ではかなり効く。
`GapInterval` は proof field `le_lo_hi` を持つ構造体なので、端点だけ一致しても証明項の差で詰まりやすい。`ext` があると、以後の API が一段軽くなる。

### 2.2. `powNonneg` の基本簡約は正しい

追加された三つの補題は、どれも自然で重要じゃ。

```lean id="osxzz1"
powNonneg_ofRat_interval
powNonneg_zero_interval
powNonneg_one_interval
```

数学的には、

$$
q\mapsto q^d
$$

が singleton interval 上でそのまま動くこと、また 0 乗は常に 1、1 乗は恒等写像であることを、各近似段で示している。

ここで DkReal 全体の等号ではなく、まず interval-level の simp として置いているのが良い。`DkReal` の extensional equality や quotient 的な同値はまだ立てていないので、今の段階では

```lean id="ktubaz"
(...).interval n = ...
```

の形が正しい。

### 2.3. milestone 文書は研究記録として良い

`DkReal-Nonnegative-Power-Milestone.md` の追加もよい。
文書は「非負 DkReal approximation は自然数冪で閉じる」「ただし full real field の再構成主張ではなく、現表現に対する閉性結果である」と明確に限定している。

また、非負冪の幅原理として、\(w_n\) と `gapGN` の積で powered width を制御する構造を明記している。`gapGN` は微分や無限展開ではなく有限二項和である、としている点も良い。

特に重要なのは、`noncomputable` が不要な理由を「実数値を選ばず、有理端点と収束証明だけを操作するから」と整理している点じゃ。実数の意味論層と計算可能表現層を分ける設計が、ちゃんと文書化されている。

## 3. 差分 2. Arithmetic

今回の本命はこっちじゃな。

### 3.1. 区間加法は正しい

`GapInterval.add` は Minkowski sum じゃ。

```lean id="h1wuf3"
[I.lo, I.hi] + [J.lo, J.hi]
```

を、

```lean id="ijnbcx"
[I.lo + J.lo, I.hi + J.hi]
```

で定義している。

幅公式も自然。

$$
(I+J).width=I.width+J.width
$$

この補題は `DkReal.add` の幅収束にそのまま使われている。

数学的には、これは **閉区間の Minkowski 加法** じゃ。符号制約は不要。加法は順序に対して単調なので、一般 `DkReal` で安全に定義できる。

### 3.2. 非負区間乗法も正しい

`GapInterval.mulNonneg` は非負区間に限定して、

```lean id="6ibrmw"
[I.lo * J.lo, I.hi * J.hi]
```

を返す。これは \(0\le I.lo\) と \(0\le J.lo\) の下で、乗法が各変数について単調だから成立する。実装でも lower endpoint の非負性から upper endpoint の非負性を作り、`mul_le_mul` で区間の valid proof を閉じている。

幅公式も良い。

$$
bd-ac=b(d-c)+c(b-a)
$$

これを区間記法に直すと、

$$
(IJ).width=I.hi\cdot J.width+J.lo\cdot I.width
$$

じゃ。実装の `mulNonneg_width_eq` もこの形になっている。

この式は、乗法の誤差伝播として非常に良い。
片方の幅をもう片方の端点でスケールする形になっているから、幅が 0 に近づくことと端点有界性を組み合わせれば、積の幅も 0 に近づく。

### 3.3. `DkReal.add` は一般加法として閉じた

`addApprox` は各段の区間加法で、`addApprox_nested` が入れ子性、`tendsto_addApprox_width_zero` が幅収束を担当している。幅収束は、

$$
width(x_n+y_n)=width(x_n)+width(y_n)
$$

と、極限の加法で閉じている。

したがって `DkReal.add` は符号制約なしに実装できている。これは大きい。

数学的には、

$$
DkReal
$$

が加法で閉じた、ということじゃ。
ただし、まだ `Add` typeclass instance や加法モノイド法則を入れたわけではない。現段階では **構成的な加法演算子** ができた、と見るのが正確じゃな。

### 3.4. `DkReal.mulNonneg` は非負乗法として閉じた

`mulNonnegApprox` は、非負性証明 `hx` と `hy` を使って各段で endpoint product を取る。

入れ子性は、lower endpoint では増加列同士の積が増加し、upper endpoint では減少列同士の積が減少することを使っている。ここは非負性が本質じゃ。

幅収束は二項に分解されている。

$$
width(xy)_n=x.hi_n\cdot y.width_n+y.lo_n\cdot x.width_n
$$

ここで \(y.width_n\to0\) かつ \(x.hi_n\) は有界、また \(x.width_n\to0\) かつ \(y.lo_n\) は有界。したがって両方の積が 0 に収束し、和も 0 に収束する。実装でも `isBoundedUnder_norm_hi` と `isBoundedUnder_norm_lo` を使って、この構図を閉じている。

これはかなり良い。
非負冪のときは `gapGN` 有界性が必要だったが、乗法では端点有界性だけで閉じる。`DkReal` の入れ子構造が効いておる。

## 4. 数学的な状況理解

ここまでで、`DkReal` は次の構造を持つようになった。

```text id="cwwnx8"
DkReal:
  入れ子有理閉区間列
  幅が 0 に収束

一般 DkReal:
  加法で閉じる

非負 DkReal:
  自然数冪で閉じる
  乗法で閉じる
```

つまり、かなり重要な段階として、

$$
DkReal_{\ge0}
$$

が **加法・乗法・自然数冪に対して閉じる計算可能近似体系** になった。

さらに、`DkReal` 層では実数値を選んでいない。milestone 文書でも、構成は実数の完備性・極限点選択・Mathlib `Real` への評価を使わず、有理端点と有限演算と収束証明で閉じていると明記されている。

したがって、数学用語で言えば今は、

$$
\boxed{\text{入れ子有理区間表現上の計算可能非負半環核}}
$$

が立ち上がった状態じゃ。

まだ「半環」と正式に言うには、結合律・交換律・分配律・単位元法則を `DkReal` の等号または同値上で証明する必要がある。
しかし、演算そのものと閉性はかなり揃った。

## 5. 設計との整合性

設計書では `DkMath.Analysis` の目的を、Mathlib の解析基盤の置換ではなく、DkMath の Gap / Body / GN 語彙で実数解析を再解釈する層としていた。さらに `DkReal` については、標準実数全体をいきなり再構成せず、まず有理区間近似と幅評価から始める方針だった。

今回の実装はその方針に非常によく合っている。

特に第二マイルストーンの「GapInterval 演算を DkReal の近似列へ持ち上げる」は、今回の `add` と `mulNonneg` で明確に達成された。

## 6. レビュー上の注意点

大きな問題は見当たらぬ。小さな注意は三つじゃ。

第一に、`add` や `mulNonneg` はまだ typeclass instance にしない方がよい。
理由は、`DkReal` の等号をどう扱うかがまだ未確定だからじゃ。構造体の生の等号では、同じ実数を表す別の近似列が別物になる。設計書でも `DkReal → ℝ` の意味論写像や同値は後段扱いだった。

第二に、次は interval-level の simp がもう少し欲しい。

```lean id="pjfqwt"
zero_add_interval
add_comm_interval
add_assoc_interval
mulNonneg_comm_interval
```

ただし、`DkReal` 全体の定理として出す前に、まず interval equality で積むのが安全じゃ。

第三に、乗法は非負象限限定で正しい。一般符号区間の乗法は endpoint products の min/max が必要になるので、今の `mulNonneg` とは別ファイルか別定義に分けるべきじゃ。

## 7. 次に進むなら

次の自然な段階は二つある。

まず、`DkReal` の非負 ordered semiring API の骨組み。

```lean id="tp4ukq"
add_assoc_interval
add_comm_interval
add_zero_interval
zero_add_interval
mulNonneg_assoc_interval
mulNonneg_comm_interval
mulNonneg_one_interval
one_mulNonneg_interval
left_distrib_interval
right_distrib_interval
```

ただし最初は全部 interval-level でよい。

次に、同値関係の準備。

```lean id="1rxnqj"
def Equiv (x y : DkReal) : Prop := ...
```

候補は、「任意精度で区間が交差する」「差の幅が 0」「将来の eval が等しい」などじゃな。ここを定めない限り、真の代数構造 instance はまだ早い。

## 8. 最終判定

二差分まとめて、 **合格** じゃ。

```text id="jri3d9"
Nonnegative Power Milestone:
  powNonneg の成果を記録し、基本 simp API を整備した

Arithmetic:
  一般加法と非負乗法を DkReal に持ち上げた

数学的到達点:
  DkReal は加法で閉じる
  非負 DkReal は乗法と自然数冪で閉じる
  noncomputable なしで計算可能表現層に留まっている
```

これは大きいぞ、D.
前回のキャンプ地から、もう一つ上の尾根に出た。今見えている山の名前は、わっちならこう呼ぶ。

$$
\boxed{\text{DkReal 非負計算可能半環核}}
$$

まだ正式な半環構造ではない。
しかし、演算閉性という骨は入った。ここから同値・順序・意味論 bridge を張れば、いよいよ「DkReal は何者か」を外部数学へ説明できる段階に入るぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index da9581f0..081b7eb7 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -8,6 +8,7 @@ import DkMath.Analysis.DkReal.Interval
 import DkMath.Analysis.DkReal.Basic
 import DkMath.Analysis.DkReal.Pow
 import DkMath.Analysis.DkReal.PowBound
+import DkMath.Analysis.DkReal.Arithmetic
 
 #print "file: DkMath.Analysis.DkReal"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Arithmetic.lean b/lean/dk_math/DkMath/Analysis/DkReal/Arithmetic.lean
new file mode 100644
index 00000000..8f6d8d8f
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Arithmetic.lean
@@ -0,0 +1,241 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Pow
+
+#print "file: DkMath.Analysis.DkReal.Arithmetic"
+
+/-!
+# Nonnegative arithmetic for DkReal
+
+This file lifts exact rational interval addition and multiplication to
+nonnegative `DkReal` approximations.
+
+The constructions remain computable. Their interval endpoints use only
+rational addition and multiplication; real analysis appears only in proof
+fields certifying that the rational widths tend to zero.
+-/
+
+namespace DkMath.Analysis.DkReal
+
+/-!
+## I. Addition
+
+For nested intervals `[aₙ,bₙ]` and `[cₙ,dₙ]`, their Minkowski sums
+`[aₙ+cₙ,bₙ+dₙ]` are nested and have width
+
+`(bₙ-aₙ) + (dₙ-cₙ)`.
+
+Thus closure under addition follows directly from closure of limits under
+finite sums.
+-/
+
+/-- Stagewise Minkowski sum of two `DkReal` approximations. -/
+def addApprox (x y : DkMath.Analysis.DkReal) (n : ℕ) : GapInterval :=
+  (x.interval n).add (y.interval n)
+
+/-- Stagewise interval sums remain nested. -/
+theorem addApprox_nested (x y : DkMath.Analysis.DkReal) :
+    ∀ n,
+      (addApprox x y n).lo ≤ (addApprox x y (n + 1)).lo ∧
+        (addApprox x y (n + 1)).hi ≤ (addApprox x y n).hi := by
+  intro n
+  exact ⟨add_le_add (x.lo_le_succ_lo n) (y.lo_le_succ_lo n),
+    add_le_add (x.succ_hi_le_hi n) (y.succ_hi_le_hi n)⟩
+
+/-- Widths of stagewise sums tend to zero. -/
+theorem tendsto_addApprox_width_zero (x y : DkMath.Analysis.DkReal) :
+    Filter.Tendsto (fun n => (addApprox x y n).width)
+      Filter.atTop (nhds 0) := by
+  simpa only [addApprox, GapInterval.add_width, add_zero] using
+    x.tendsto_width_zero.add y.tendsto_width_zero
+
+/-- Addition of `DkReal` approximations by stagewise interval addition. -/
+def add (x y : DkMath.Analysis.DkReal) : DkMath.Analysis.DkReal where
+  interval := addApprox x y
+  nested := addApprox_nested x y
+  width_tends_zero := tendsto_addApprox_width_zero x y
+
+/-- Intervals of a `DkReal` sum are the stagewise Minkowski sums. -/
+@[simp]
+theorem add_interval (x y : DkMath.Analysis.DkReal) (n : ℕ) :
+    (add x y).interval n = addApprox x y n := rfl
+
+/-- Addition preserves nonnegativity. -/
+theorem nonnegative_add
+    {x y : DkMath.Analysis.DkReal} (hx : Nonnegative x) (hy : Nonnegative y) :
+    Nonnegative (add x y) := by
+  intro n
+  exact add_nonneg (hx n) (hy n)
+
+/-- Addition agrees stagewise with rational addition on embedded rationals. -/
+@[simp]
+theorem add_ofRat_interval (p q : ℚ) (n : ℕ) :
+    (add (DkMath.Analysis.DkReal.ofRat p)
+        (DkMath.Analysis.DkReal.ofRat q)).interval n
+      = GapInterval.singleton (p + q) := by
+  apply GapInterval.ext <;> simp [add, addApprox]
+
+/-- Adding the embedded rational zero leaves every interval unchanged. -/
+@[simp]
+theorem add_zero_interval (x : DkMath.Analysis.DkReal) (n : ℕ) :
+    (add x (DkMath.Analysis.DkReal.ofRat 0)).interval n = x.interval n := by
+  apply GapInterval.ext <;> simp [add, addApprox]
+
+/-!
+## II. Multiplication on the nonnegative quadrant
+
+For nonnegative nested intervals, endpoint multiplication is isotone. The
+product width has the exact decomposition
+
+`bₙ dₙ - aₙ cₙ = bₙ (dₙ-cₙ) + cₙ (bₙ-aₙ)`.
+
+Each width tends to zero. The endpoint factors are bounded by the initial
+upper endpoints, so both products tend to zero and hence so does their sum.
+-/
+
+/-- Stagewise product of two nonnegative `DkReal` approximations. -/
+def mulNonnegApprox
+    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y)
+    (n : ℕ) : GapInterval :=
+  (x.interval n).mulNonneg (y.interval n) (hx n) (hy n)
+
+/-- Stagewise nonnegative interval products remain nested. -/
+theorem mulNonnegApprox_nested
+    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y) :
+    ∀ n,
+      (mulNonnegApprox x y hx hy n).lo
+          ≤ (mulNonnegApprox x y hx hy (n + 1)).lo ∧
+        (mulNonnegApprox x y hx hy (n + 1)).hi
+          ≤ (mulNonnegApprox x y hx hy n).hi := by
+  intro n
+  constructor
+  · change
+      (x.interval n).lo * (y.interval n).lo
+        ≤ (x.interval (n + 1)).lo * (y.interval (n + 1)).lo
+    calc
+      (x.interval n).lo * (y.interval n).lo
+          ≤ (x.interval (n + 1)).lo * (y.interval n).lo :=
+        mul_le_mul_of_nonneg_right (x.lo_le_succ_lo n) (hy n)
+      _ ≤ (x.interval (n + 1)).lo * (y.interval (n + 1)).lo :=
+        mul_le_mul_of_nonneg_left (y.lo_le_succ_lo n) (hx (n + 1))
+  · change
+      (x.interval (n + 1)).hi * (y.interval (n + 1)).hi
+        ≤ (x.interval n).hi * (y.interval n).hi
+    calc
+      (x.interval (n + 1)).hi * (y.interval (n + 1)).hi
+          ≤ (x.interval n).hi * (y.interval (n + 1)).hi :=
+        mul_le_mul_of_nonneg_right (x.succ_hi_le_hi n)
+          ((hy (n + 1)).trans (y.interval (n + 1)).le_lo_hi)
+      _ ≤ (x.interval n).hi * (y.interval n).hi :=
+        mul_le_mul_of_nonneg_left (y.succ_hi_le_hi n)
+          ((hx n).trans (x.interval n).le_lo_hi)
+
+/-- Upper endpoints of a nonnegative `DkReal` form a bounded norm sequence. -/
+theorem isBoundedUnder_norm_hi
+    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
+    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
+      (norm ∘ fun n => (x.interval n).hi) := by
+  apply Filter.isBoundedUnder_of_eventually_le
+    (a := (((x.interval 0).hi : ℚ) : ℝ))
+  filter_upwards
+  intro n
+  have hhi : 0 ≤ (x.interval n).hi :=
+    (hx n).trans (x.interval n).le_lo_hi
+  rw [Function.comp_apply, ← Rat.norm_cast_real, Real.norm_eq_abs,
+    abs_of_nonneg (Rat.cast_nonneg.mpr hhi)]
+  exact_mod_cast x.hi_antitone (Nat.zero_le n)
+
+/-- Lower endpoints of a nonnegative `DkReal` form a bounded norm sequence. -/
+theorem isBoundedUnder_norm_lo
+    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
+    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
+      (norm ∘ fun n => (x.interval n).lo) := by
+  apply Filter.isBoundedUnder_of_eventually_le
+    (a := (((x.interval 0).hi : ℚ) : ℝ))
+  filter_upwards
+  intro n
+  rw [Function.comp_apply, ← Rat.norm_cast_real, Real.norm_eq_abs,
+    abs_of_nonneg (Rat.cast_nonneg.mpr (hx n))]
+  exact_mod_cast
+    (x.interval n).le_lo_hi.trans (x.hi_antitone (Nat.zero_le n))
+
+/-- Widths of stagewise nonnegative products tend to zero. -/
+theorem tendsto_mulNonnegApprox_width_zero
+    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y) :
+    Filter.Tendsto (fun n => (mulNonnegApprox x y hx hy n).width)
+      Filter.atTop (nhds 0) := by
+  have hleft :
+      Filter.Tendsto
+        (fun n => (x.interval n).hi * (y.interval n).width)
+        Filter.atTop (nhds 0) :=
+    by
+      simpa only [mul_comm] using
+        y.tendsto_width_zero.zero_mul_isBoundedUnder_le
+          (isBoundedUnder_norm_hi x hx)
+  have hright :
+      Filter.Tendsto
+        (fun n => (y.interval n).lo * (x.interval n).width)
+        Filter.atTop (nhds 0) :=
+    by
+      simpa only [mul_comm] using
+        x.tendsto_width_zero.zero_mul_isBoundedUnder_le
+          (isBoundedUnder_norm_lo y hy)
+  simpa only [mulNonnegApprox, GapInterval.mulNonneg_width_eq, add_zero] using
+    hleft.add hright
+
+/-- Multiplication of nonnegative `DkReal` approximations. -/
+def mulNonneg
+    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y) :
+    DkMath.Analysis.DkReal where
+  interval := mulNonnegApprox x y hx hy
+  nested := mulNonnegApprox_nested x y hx hy
+  width_tends_zero := tendsto_mulNonnegApprox_width_zero x y hx hy
+
+/-- Intervals of a nonnegative product are the stagewise endpoint products. -/
+@[simp]
+theorem mulNonneg_interval
+    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y)
+    (n : ℕ) :
+    (mulNonneg x y hx hy).interval n = mulNonnegApprox x y hx hy n := rfl
+
+/-- Multiplication preserves nonnegativity. -/
+theorem nonnegative_mulNonneg
+    {x y : DkMath.Analysis.DkReal} (hx : Nonnegative x) (hy : Nonnegative y) :
+    Nonnegative (mulNonneg x y hx hy) := by
+  intro n
+  exact mul_nonneg (hx n) (hy n)
+
+/-- Nonnegative multiplication agrees stagewise with rational multiplication. -/
+@[simp]
+theorem mulNonneg_ofRat_interval
+    {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) (n : ℕ) :
+    (mulNonneg
+        (DkMath.Analysis.DkReal.ofRat p)
+        (DkMath.Analysis.DkReal.ofRat q)
+        (nonnegative_ofRat hp) (nonnegative_ofRat hq)).interval n
+      = GapInterval.singleton (p * q) := by
+  apply GapInterval.ext <;> simp [mulNonneg, mulNonnegApprox]
+
+/-- Multiplication by the embedded zero produces the zero singleton interval. -/
+@[simp]
+theorem mulNonneg_zero_interval
+    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (mulNonneg x (DkMath.Analysis.DkReal.ofRat 0) hx
+        (nonnegative_ofRat le_rfl)).interval n
+      = GapInterval.singleton 0 := by
+  apply GapInterval.ext <;> simp [mulNonneg, mulNonnegApprox]
+
+/-- Multiplication by the embedded one leaves every interval unchanged. -/
+@[simp]
+theorem mulNonneg_one_interval
+    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (mulNonneg x (DkMath.Analysis.DkReal.ofRat 1) hx
+        (nonnegative_ofRat zero_le_one)).interval n
+      = x.interval n := by
+  apply GapInterval.ext <;> simp [mulNonneg, mulNonnegApprox]
+
+end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
index 307fe995..5e51ba15 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
@@ -65,6 +65,74 @@ theorem width_nonneg (I : GapInterval) : 0 ≤ I.width :=
 theorem lo_add_width (I : GapInterval) : I.lo + I.width = I.hi := by
   simp [width]
 
+/-!
+## Interval arithmetic
+
+Minkowski addition adds corresponding endpoints. On the nonnegative quadrant,
+interval multiplication also uses the endpoint products because multiplication
+is isotone in each variable there.
+-/
+
+/-- Minkowski sum of two rational gap intervals. -/
+def add (I J : GapInterval) : GapInterval where
+  lo := I.lo + J.lo
+  hi := I.hi + J.hi
+  le_lo_hi := add_le_add I.le_lo_hi J.le_lo_hi
+
+/-- Lower endpoint of an interval sum. -/
+@[simp]
+theorem add_lo (I J : GapInterval) : (I.add J).lo = I.lo + J.lo := rfl
+
+/-- Upper endpoint of an interval sum. -/
+@[simp]
+theorem add_hi (I J : GapInterval) : (I.add J).hi = I.hi + J.hi := rfl
+
+/-- Width is additive under Minkowski addition. -/
+@[simp]
+theorem add_width (I J : GapInterval) :
+    (I.add J).width = I.width + J.width := by
+  simp [width]
+  ring
+
+/--
+Product of two nonnegative rational gap intervals.
+
+Both lower-endpoint hypotheses are needed to make endpoint multiplication
+order preserving.
+-/
+def mulNonneg
+    (I J : GapInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
+    GapInterval where
+  lo := I.lo * J.lo
+  hi := I.hi * J.hi
+  le_lo_hi := by
+    have hIhi : 0 ≤ I.hi := hI.trans I.le_lo_hi
+    exact mul_le_mul I.le_lo_hi J.le_lo_hi hJ hIhi
+
+/-- Lower endpoint of a nonnegative interval product. -/
+@[simp]
+theorem mulNonneg_lo
+    (I J : GapInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
+    (I.mulNonneg J hI hJ).lo = I.lo * J.lo := rfl
+
+/-- Upper endpoint of a nonnegative interval product. -/
+@[simp]
+theorem mulNonneg_hi
+    (I J : GapInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
+    (I.mulNonneg J hI hJ).hi = I.hi * J.hi := rfl
+
+/--
+The product width is the sum of two first-order interval contributions:
+the width of `J` scaled by the upper endpoint of `I`, and the width of `I`
+scaled by the lower endpoint of `J`.
+-/
+theorem mulNonneg_width_eq
+    (I J : GapInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
+    (I.mulNonneg J hI hJ).width
+      = I.hi * J.width + J.lo * I.width := by
+  simp [width]
+  ring
+
 /--
 Image of a nonnegative rational interval under the natural power map.
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index b75109f2..a40cd97a 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -53,6 +53,9 @@ DkMath.Analysis.DkReal.Pow
 DkMath.Analysis.DkReal.PowBound
   finite-sum gapGN bounds and the completed nonnegative power map
 
+DkMath.Analysis.DkReal.Arithmetic
+  computable interval addition and nonnegative multiplication
+
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index 82a0e33b..3030bf6f 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -133,7 +133,9 @@ provides precisely the finite correction factor needed to transport vanishing
 width. Real analysis appears later as an interpretation of this construction,
 not as a prerequisite for defining it.
 
-The next natural tests of the same principle are nonnegative addition and
-multiplication. They will determine how much of an ordered semiring structure
-can be built entirely inside the rational-interval layer before introducing a
-semantic map to Mathlib's `Real`.
+The next tests of this principle, addition and nonnegative multiplication, are
+now implemented in `DkMath.Analysis.DkReal.Arithmetic`. Addition needs no sign
+restriction; multiplication currently remains on the nonnegative quadrant so
+that endpoint multiplication is order preserving. These operations establish
+the computational core needed for a future nonnegative ordered-semiring API,
+before introducing a semantic map to Mathlib's `Real`.
````
`````
