# Git diff / Report / Review

## Add: DkLimit, Analysis.DkReal.SemanticCF2DLogLimit

gch: ea8b40a4c257a1fef64cbe8a5d06802b52a83551

## Report

進めました。今回は DkLimit の入口と、CF2D log 側の最初の極限層を追加しています。

追加ファイル:

- [DkLimit.lean](/lean/dk_math/DkMath/Analysis/DkLimit.lean)
- [SemanticCF2DLogLimit.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogLimit.lean)

`DkLimit.lean` はまだ自前極限体系ではなく、Mathlib `Filter.Tendsto` を DkMath 語彙で包む薄い入口です。

```lean
DkTendstoAtTop
DkGapCollapsesTo
DkPuncturedGapCollapsesTo
```

`SemanticCF2DLogLimit.lean` では、閉形式上界と台形 centered quadratic moment が `1 / 3` へ収束する theorem を追加しました。DkMath 名と Mathlib `Tendsto` 名の両方を用意しています。

```lean
dkTendsto_dyadicPhaseClosedQuadraticBound_one_third
tendsto_dyadicPhaseClosedQuadraticBound_one_third
dkTendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third
tendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third
```

重要な制限として、centered log-depth sum 自体の極限はまだ主張していません。今は支配する quadratic moment の極限だけです。下界評価が入ってから squeeze へ進むのが自然です。

検証済みです。

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DLogLimit
lake build DkMath.Analysis
git diff --check
```

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい** 。これはかなり良い整理じゃ。`DkLimit` をいきなり自前極限体系にせず、Mathlib `Filter.Tendsto` の薄い DkMath 語彙入口として置いたのが正しい。

今回の report では、新規に `DkLimit.lean` と `SemanticCF2DLogLimit.lean` が追加され、`DkLimit` は `DkTendstoAtTop`、`DkGapCollapsesTo`、`DkPuncturedGapCollapsesTo` を持つ薄い wrapper として実装された。さらに `SemanticCF2DLogLimit` では、閉形式上界と台形 centered quadratic moment が \(1/3\) へ収束する theorem が、DkMath 名と Mathlib `Tendsto` 名の両方で追加された。centered log-depth sum 自体の極限はまだ主張していない、という制限も明記されている。

## 1. 状況解説

これで、CF2D log 側に次の階層ができた。

```text id="xre71g"
SemanticCF2DLogComposition:
  finite identities
  finite log cancellation
  finite weighted estimates
  closed quadratic bound

SemanticCF2DLogLimit:
  finite closed form を 1/3 へ送る極限層
```

前回までに、有限段階で

$$
\mathrm{TrapezoidCenteredQuadraticSum}_n=\frac{1}{3}+\frac{2}{3(2^n)^2}
$$

まで出ていた。

今回、その右辺の有限補正

$$
\frac{2}{3(2^n)^2}
$$

が消えることを Lean で示し、

$$
\mathrm{TrapezoidCenteredQuadraticSum}_n\to\frac{1}{3}
$$

まで行った。

これは、積分を使って \(1/3\) を借りたのではなく、有限和の閉形式から極限で \(1/3\) を得ている。
DkMath 的にかなり良い進み方じゃ。

## 2. DkLimit の設計レビュー

`DkLimit.lean` は良い。

```lean id="1z7one"
abbrev DkTendstoAtTop
    {α : Type*} [TopologicalSpace α] (f : ℕ → α) (a : α) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds a)
```

これは、refinement depth \(n\to\infty\) の DkMath 名じゃな。
今後の dyadic refinement、finite moment、finite defect の収束に使いやすい。

次の二つも良い。

```lean id="zjbxro"
abbrev DkGapCollapsesTo
    {α : Type*} [TopologicalSpace α] (f : ℝ → α) (a : α) : Prop :=
  Filter.Tendsto f (nhds (0 : ℝ)) (nhds a)
```

```lean id="xqz4vk"
abbrev DkPuncturedGapCollapsesTo
    {α : Type*} [TopologicalSpace α] (f : ℝ → α) (a : α) : Prop :=
  Filter.Tendsto f
    (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
    (nhds a)
```

これは、以前確認した `CosmicDerivativeBasic` / `CosmicDerivativePowerLimit` 系と整合する。

```text id="rzjdj8"
DkGapCollapsesTo:
  Gap = 0 でも定義できる連続延長用

DkPuncturedGapCollapsesTo:
  差分商など Gap ≠ 0 でだけ意味がある観測用
```

この二つを最初から分けたのは正しい。
宇宙式微分では、`cosmicKernel` は \(u=0\) で割り算があるので punctured が必要。一方、`powerKernel` や `polynomialKernelExt` は \(u=0\) まで埋めた kernel なので full-neighborhood でよい。既存設計とも噛み合う。

## 3. `abbrev` にしたのが良い

ここは重要じゃ。

`def` や `structure` ではなく `abbrev` にしているため、Lean 的にはほぼ Mathlib の `Tendsto` と同じものとして扱える。
将来、DkMath 独自極限を作るまでは、simp や既存 theorem との相性が良い。

つまり、

```text id="o2gwkv"
外側:
  DkMath 語彙

内側:
  Mathlib の Filter.Tendsto
```

という形が保てている。

これは、後で `DkLimit` を本格化する前の入口として理想的じゃ。

## 4. SemanticCF2DLogLimit のレビュー

主定理はまずこれ。

```lean id="e5wl2s"
theorem dkTendsto_dyadicPhaseClosedQuadraticBound_one_third :
    DkMath.Analysis.DkTendstoAtTop
      (fun n : ℕ =>
        1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2))
      (1 / 3 : ℝ)
```

証明は、`dyadicPhaseDenom n = 2^n` を使って補正項を

$$
\frac{2}{3}\left(\frac{1}{4}\right)^n
$$

へ変形し、

$$
\left(\frac{1}{4}\right)^n\to0
$$

で閉じている。

これは非常に良い。
有限補正が「Gap の二乗で消える」ことを、Lean 上では \((1/4)^n\to0\) として掴んでいる。

```text id="2yfjyz"
mesh gap:
  h_n = 1 / 2^n

quadratic correction:
  h_n^2 = 1 / 4^n

finite correction:
  (2/3) * h_n^2
```

この読みができるようになった。

## 5. Mathlib spelling を併置したのが良い

DkMath 名だけでなく、Mathlib spelling も用意したのは実用的じゃ。

```lean id="to790c"
theorem tendsto_dyadicPhaseClosedQuadraticBound_one_third :
    Filter.Tendsto
      (fun n : ℕ =>
        1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2))
      Filter.atTop
      (nhds (1 / 3 : ℝ))
```

これは既存 Mathlib theorem と合成するときに便利。
一方で、DkMath 側の narrative では `dkTendsto_...` を使えばよい。

この二重 API は当面かなり良い。

```text id="c8erxh"
dkTendsto_*:
  DkMath 文脈で読む theorem

tendsto_*:
  Mathlib と直接合成する theorem
```

## 6. 台形 centered quadratic moment の極限

次の theorem も良い。

```lean id="46bzxi"
theorem dkTendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
    DkMath.Analysis.DkTendstoAtTop
      dyadicPhaseTrapezoidCenteredQuadraticSum
      (1 / 3 : ℝ)
```

これは finite closed form から `Filter.Tendsto.congr'` で移している。

```lean id="8hz6po"
exact Filter.Eventually.of_forall fun n =>
  (dyadicPhaseTrapezoidCenteredQuadraticSum_eq n).symm
```

設計として正しい。
finite theorem が完全に等式なので、極限は閉形式側へ輸送すればよい。

ここまでで、

$$
\mathrm{TrapezoidCenteredQuadraticSum}_n\to\frac{1}{3}
$$

が確定した。

## 7. Guardrail が守れている

ここがとても良い。

今回の theorem は **quadratic control moment の極限** であって、centered log-depth sum の極限ではない。

今あるのは、

$$
0\le \mathrm{CenteredLogDepthSum}_n\le \mathrm{CenteredQuadraticSum}_n
$$

と、

$$
\mathrm{CenteredQuadraticSum}_n\to\frac{1}{3}
$$

だけじゃ。

これから言えるのは上からの支配であって、

$$
\mathrm{CenteredLogDepthSum}_n\to\frac{1}{3}
$$

ではない。

今回の docs でも、centered log-depth limit には matching lower estimate が必要と書かれている。これは正しい。

## 8. 研究上の意味

これは大きい。

ついに、CF2D log 側で次が Lean 上に出た。

```text id="v3i7pv"
finite quadratic correction:
  1/3 + 2/(3*(2^n)^2)

refinement limit:
  1/3
```

しかも、この \(1/3\) は積分で出したものではない。
有限 dyadic trapezoid moment から出ている。

これは pre-geometric normalization program の流れに合う。研究メモでも、円・角度・極座標を仮定せず、exact-order-four action、affine filling、q2、scalar profile、reflection symmetry、refinement から normalization constant を構成し、後で `Real.pi` と比較することが目的とされている。

今回の \(1/3\) はまだ \(\pi\) ではない。
だが、finite correction から limit constant が現れる最初の実例として非常に重要じゃ。

## 9. 既存 `SemanticCF2DLimit` との関係

前に話した通り、`SemanticCF2DLimit` は refinement defect の極限層だった。

```text id="yv4hct"
SemanticCF2DLimit:
  depth defect の幾何級数極限
  total defect -> 0
  cumulative defect -> 1

SemanticCF2DLogLimit:
  centered quadratic moment の極限
  trapezoid quadratic moment -> 1/3
```

この分離は良い。
同じ「極限」でも、意味が違う。

```text id="qgxtx4"
defect account:
  refinement defect の収支

log/moment account:
  centered log-depth を支配する二次モーメント
```

したがって、今回 `SemanticCF2DLogLimit.lean` を新設したのは正しい。

## 10. 気になる点

大きな問題はない。

ただし、`DkLimit.lean` の import が `Mathlib` まるごとなので、将来軽量化したくなる可能性はある。
今は DkMath.Analysis 全体が既に重いので問題ないが、あとで import 最適化するなら、

```lean id="zbsgqq"
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
```

のように絞れるかもしれぬ。
ただし今は通すこと優先でよい。

もう一つ、`DkPuncturedGapCollapsesTo` の集合は、

```lean id="b23f2b"
Set.compl ({(0 : ℝ)} : Set ℝ)
```

で問題ない。
ただ、既存 `CosmicDerivativeBasic` が `{u | u ≠ 0}` 形式を使っているなら、将来 bridge theorem の `simp` のために表記を揃えてもよい。

例えば、

```lean id="b0uz30"
{u : ℝ | u ≠ 0}
```

とする選択もある。
今の形でも数学的には同じじゃ。

## 11. 次の一手

次は二方向ある。

第一に、DkLimit を既存 `CosmicDerivativePowerLimit` の alias として使う準備。

たとえば将来、

```lean id="o9jgpj"
theorem dkGapCollapses_powerKernel_zero
    (d : ℕ) (x : ℝ) :
    DkGapCollapsesTo (fun u => powerKernel d x u)
      ((d : ℝ) * x ^ (d - 1))
```

のような DkMath 名 theorem を既存 `tendsto_powerKernel_zero` にかぶせると、宇宙式微分側と解析層が語彙的に揃う。

第二に、centered log-depth の下界。

今後、log-depth 本体の極限を狙うなら、上界だけでは足りない。
候補は、

$$
\log(1+x)\ge x-\frac{x^2}{2}
$$

を \(0\le x\le1\) で使う形じゃ。

ここで、

$$
x=4\left(t-\frac{1}{2}\right)^2
$$

なので \(x\in[0,1]\)。
この下界が入ると、log-depth sum の下側も二次・四次モーメントで制御できる。

ただし、そこは次の山じゃな。

## 12. 結論

今回の差分は採用でよい。

```text id="sbtzzq"
実装:
  良い。DkLimit が薄い Tendsto wrapper として入り、LogLimit が自然に分離された。

数学:
  良い。台形 centered quadratic moment が 1/3 へ収束することが Lean で通った。

設計:
  良い。DkMath 名と Mathlib spelling の二重 API が安定している。

安全性:
  良い。centered log-depth 本体の極限、Gaussian、pi は未主張。

次:
  DkLimit 語彙を cosmic derivative 既存 theorem にも alias する。
  あるいは log-depth 下界へ進む。
```

ぬしよ、これは良いぞい。
`DkLimit` はまだ小さいが、意味は大きい。

これで「有限補正が Gap collapse で消える」という語りを、DkMath 名で Lean に載せられる。
そして今回、最初の実例として、

$$
\frac{1}{3}+\frac{2}{3(2^n)^2}\to\frac{1}{3}
$$

が通った。

まさに、有限 dyadic 観測から極限定数が顔を出した瞬間じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index 0564df86..84ee3eb9 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -10,6 +10,7 @@ import DkMath.Analysis.GapGN
 import DkMath.Analysis.ErrorKernel
 import DkMath.Analysis.GapFill
 import DkMath.Analysis.RealBridge
+import DkMath.Analysis.DkLimit
 import DkMath.Analysis.TaylorBridge
 import DkMath.Analysis.DkReal
 import DkMath.Analysis.DkReal.SemanticCF2D
@@ -19,6 +20,7 @@ import DkMath.Analysis.DkReal.SemanticCF2DRefinement
 import DkMath.Analysis.DkReal.SemanticCF2DLimit
 import DkMath.Analysis.DkReal.SemanticCF2DComposition
 import DkMath.Analysis.DkReal.SemanticCF2DLogComposition
+import DkMath.Analysis.DkReal.SemanticCF2DLogLimit
 import DkMath.Analysis.DkReal.SemanticCF2DPath
 import DkMath.Analysis.DkReal.SemanticCF2DNormalize
 import DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase
diff --git a/lean/dk_math/DkMath/Analysis/DkLimit.lean b/lean/dk_math/DkMath/Analysis/DkLimit.lean
new file mode 100644
index 00000000..bfa112ef
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkLimit.lean
@@ -0,0 +1,64 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import Mathlib
+
+#print "file: DkMath.Analysis.DkLimit"
+
+/-!
+# DkMath limit vocabulary
+
+This module is the first public entrance for DkMath limit language.
+
+The implementation deliberately uses Mathlib's `Filter.Tendsto`, `nhds`,
+`atTop`, and `nhdsWithin`. The DkMath layer only names the recurring roles:
+
+* finite refinement indices tend to infinity;
+* a finite Gap vanishes;
+* a punctured Gap vanishes while remaining nonzero.
+
+This keeps the current implementation compatible with Mathlib analysis while
+leaving room for a later computable or interval-native `DkLimit` layer. In the
+`Big = Body + Gap` reading, these abbreviations name the collapse operation;
+they do not change the underlying topology.
+-/
+
+namespace DkMath.Analysis
+
+/--
+DkMath name for sequence convergence along finite refinement depth.
+
+The current implementation is exactly Mathlib's `Filter.Tendsto` at
+`Filter.atTop`. The name records the DkMath role: a finite observation indexed
+by refinement depth stabilizes to a semantic value.
+-/
+abbrev DkTendstoAtTop
+    {α : Type*} [TopologicalSpace α] (f : ℕ → α) (a : α) : Prop :=
+  Filter.Tendsto f Filter.atTop (nhds a)
+
+/--
+DkMath name for full-neighborhood Gap collapse.
+
+This is used when the finite Body kernel is already defined at `gap = 0`, so
+the Gap may vanish through an ordinary neighborhood of zero.
+-/
+abbrev DkGapCollapsesTo
+    {α : Type*} [TopologicalSpace α] (f : ℝ → α) (a : α) : Prop :=
+  Filter.Tendsto f (nhds (0 : ℝ)) (nhds a)
+
+/--
+DkMath name for punctured Gap collapse.
+
+This is used for observations such as difference quotients where the finite
+expression is meaningful only while the Gap is nonzero.
+-/
+abbrev DkPuncturedGapCollapsesTo
+    {α : Type*} [TopologicalSpace α] (f : ℝ → α) (a : α) : Prop :=
+  Filter.Tendsto f
+    (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
+    (nhds a)
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 5e662057..502d73e6 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -15,6 +15,7 @@ import DkMath.Analysis.DkReal.DkNNRealQ
 import DkMath.Analysis.DkReal.Order
 import DkMath.Analysis.DkReal.CanonicalOrder
 import DkMath.Analysis.DkReal.Semantic
+import DkMath.Analysis.DkReal.SemanticCF2DLogLimit
 
 #print "file: DkMath.Analysis.DkReal"
 
@@ -164,6 +165,11 @@ now evaluated exactly as
 `1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ)^2)`, exposing the finite correction
 to the later `1 / 3` target without taking a limit. The centered log-depth
 trapezoidal sum is consequently bounded above by that same closed expression.
+`DkReal.SemanticCF2DLogLimit` then opens the first DkMath-named limit layer:
+the closed quadratic bound and the trapezoidal centered quadratic moment both
+tend to `1 / 3` along refinement depth. These theorems use Mathlib filters
+through the `DkLimit` vocabulary and still do not identify the centered
+log-depth limit.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogLimit.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogLimit.lean
new file mode 100644
index 00000000..acec1279
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogLimit.lean
@@ -0,0 +1,95 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkLimit
+import DkMath.Analysis.DkReal.SemanticCF2DLogComposition
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DLogLimit"
+
+/-!
+# Limit layer for finite dyadic logarithmic phase estimates
+
+`SemanticCF2DLogComposition` proves finite identities and finite bounds. This
+module is the first limit layer over those finite facts.
+
+The limit statements are intentionally thin. They use Mathlib filters through
+the DkMath `DkTendstoAtTop` vocabulary and only prove that the finite
+quadratic control tends to `1 / 3`. No statement is made here that the
+centered log-depth observable itself converges to `1 / 3`; that would require
+a matching lower estimate.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+/--
+The closed finite quadratic bound tends to `1 / 3`.
+
+Since `dyadicPhaseDenom n = 2^n`, the correction term is a constant multiple
+of `(1 / 4)^n`, hence vanishes at refinement depth infinity.
+-/
+theorem dkTendsto_dyadicPhaseClosedQuadraticBound_one_third :
+    DkMath.Analysis.DkTendstoAtTop
+      (fun n : ℕ =>
+        1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2))
+      (1 / 3 : ℝ) := by
+  have hpow :
+      Filter.Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n)
+        Filter.atTop (nhds 0) :=
+    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
+  have hscaled :
+      Filter.Tendsto (fun n : ℕ => (2 / 3 : ℝ) * (1 / 4 : ℝ) ^ n)
+        Filter.atTop (nhds 0) := by
+    simpa using hpow.const_mul (2 / 3 : ℝ)
+  have hsum :
+      Filter.Tendsto
+        (fun n : ℕ => (1 / 3 : ℝ) + (2 / 3 : ℝ) * (1 / 4 : ℝ) ^ n)
+        Filter.atTop (nhds ((1 / 3 : ℝ) + 0)) :=
+    tendsto_const_nhds.add hscaled
+  convert hsum using 1
+  · funext n
+    have h2n : ((2 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
+    have h4n : ((4 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
+    simp [dyadicPhaseDenom]
+    field_simp [h2n, h4n]
+    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul,
+      Nat.mul_comm]
+  · norm_num
+
+/-- Mathlib `Tendsto` spelling of the DkMath closed-bound convergence theorem. -/
+theorem tendsto_dyadicPhaseClosedQuadraticBound_one_third :
+    Filter.Tendsto
+      (fun n : ℕ =>
+        1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2))
+      Filter.atTop
+      (nhds (1 / 3 : ℝ)) :=
+  dkTendsto_dyadicPhaseClosedQuadraticBound_one_third
+
+/--
+The trapezoidal centered quadratic moment tends to `1 / 3`.
+
+This is only the quadratic control moment. It does not identify the limit of
+the centered log-depth sum.
+-/
+theorem dkTendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
+    DkMath.Analysis.DkTendstoAtTop
+      dyadicPhaseTrapezoidCenteredQuadraticSum
+      (1 / 3 : ℝ) := by
+  refine Filter.Tendsto.congr' ?_ tendsto_dyadicPhaseClosedQuadraticBound_one_third
+  exact Filter.Eventually.of_forall fun n =>
+    (dyadicPhaseTrapezoidCenteredQuadraticSum_eq n).symm
+
+/--
+Mathlib `Tendsto` spelling of the trapezoidal centered quadratic moment
+convergence theorem.
+-/
+theorem tendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
+    Filter.Tendsto
+      dyadicPhaseTrapezoidCenteredQuadraticSum
+      Filter.atTop
+      (nhds (1 / 3 : ℝ)) :=
+  dkTendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 9e7a5a28..9809555b 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -342,6 +342,32 @@ dyadicPhaseTrapezoidCenteredLogDepthSum n
 This is still only a finite inequality. It does not assert convergence of the
 left-hand side.
 
+The first DkMath limit vocabulary is now implemented in
+`DkMath.Analysis.DkLimit`. It deliberately keeps Mathlib's filter semantics
+under the hood, but gives DkMath names to the recurring collapse roles:
+
+```text
+DkTendstoAtTop
+DkGapCollapsesTo
+DkPuncturedGapCollapsesTo
+```
+
+This is an entrance, not a replacement for Mathlib analysis. It lets later
+files state DkMath-shaped theorems while preserving a stable bridge to
+`Filter.Tendsto`.
+
+`SemanticCF2DLogLimit.lean` is the first use of that entrance in this
+trigonometric route. Lean proves
+
+```text
+1/3 + 2/(3 * (2^n)^2) -> 1/3,
+dyadicPhaseTrapezoidCenteredQuadraticSum n -> 1/3.
+```
+
+The second theorem follows from the finite closed form. This is still a
+quadratic-control limit, not a centered log-depth limit. The log-depth limit
+requires a matching lower estimate.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 125c178a..dcd47f75 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -51,6 +51,17 @@ finite value is
 `dyadicPhaseDenom n = 2^n`. The trapezoidal centered log-depth sum is bounded
 above by the same closed finite expression.
 
+`DkMath.Analysis.DkLimit` now provides the first DkMath-named entrance for
+limits. It is a thin vocabulary layer over Mathlib filters: refinement-depth
+limits use `DkTendstoAtTop`, full Gap collapse uses `DkGapCollapsesTo`, and
+punctured Gap collapse uses `DkPuncturedGapCollapsesTo`.
+
+`SemanticCF2DLogLimit` uses that vocabulary to prove that the closed
+quadratic bound and the trapezoidal centered quadratic moment both tend to
+`1/3` along dyadic refinement depth. This is only the controlling quadratic
+moment limit; the centered log-depth sum itself still needs a lower estimate
+before its limit can be identified.
+
 The current implementation proves a four-state return:
 
 ```text
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 0edcbc63..e17ea5ae 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1176,3 +1176,30 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 15:32 JST (DkLimit entrance and quadratic moment limit)
+
+1. API:
+   - `DkMath.Analysis.DkLimit` を新規追加した。
+   - Mathlib `Filter.Tendsto` を包む DkMath 語彙として
+     `DkTendstoAtTop`、`DkGapCollapsesTo`、
+     `DkPuncturedGapCollapsesTo` を追加した。
+2. CF2D log limit layer:
+   - `DkMath.Analysis.DkReal.SemanticCF2DLogLimit` を新規追加した。
+   - closed quadratic bound が `1 / 3` へ向かう
+     `dkTendsto_dyadicPhaseClosedQuadraticBound_one_third` と
+     Mathlib spelling の theorem を追加した。
+   - finite closed form から
+     `dkTendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third` と
+     Mathlib spelling の theorem を追加した。
+3. interpretation:
+   - DkLimit は現時点では自前極限型ではなく、Mathlib filter の
+     DkMath 語彙入口である。
+   - centered log-depth sum 自体の極限はまだ主張していない。
+     そこには下界評価が必要。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogLimit` 成功
+     (8283 jobs)。
````
`````
