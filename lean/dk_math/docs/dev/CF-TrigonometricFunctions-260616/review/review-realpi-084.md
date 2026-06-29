# Git diff / Report / Review

## Add: Analysis.DkReal.SemanticCF2DLogComposition

gch: f8988b955ca6e4864e449ab67e2cee2d85afdaa2

## Report

finite logarithmic composition 層を実装しました。

- dyadic depth / normalization の点ごとの正値性
- complete mesh 上の有限 log sums
- `log(product) = sum(log)` の橋
- `2 * logNormalizationSum + logDepthSum = 0`
- 公開入口・研究資料・履歴を同期

`lake build DkMath.Analysis` 成功（8294 jobs）、警告なし、`git diff --check` 成功です。

## Review

うむ、これは重要な checkpoint じゃ。
今回で、finite product cancellation が **有限 log-sum cancellation** に移った。これは \(\sqrt{\pi}\) へ向かう研究線では、かなり大きい段階じゃな。

## 1. 総評

今回の差分は **採用でよい** 。

前回までの有限積の法則は、こうだった。

$$
\mathrm{NormalizationProduct}(n)^2\cdot\mathrm{DepthProduct}(n)=1
$$

今回、それを log に移して、有限加法会計として次を証明した。

$$
2\cdot\mathrm{LogNormalizationSum}(n)+\mathrm{LogDepthSum}(n)=0
$$

これは、Gaussian へ向かうために必要な形じゃ。
なぜなら Gaussian は、積よりも本質的には **指数と対数の加法会計** で現れるからじゃ。

```text id="t9a8db"
product:
  multiplicative restoration

log sum:
  additive correction account

Gaussian:
  quadratic additive exponent の指数化
```

今回の実装は、この真ん中をちゃんと作った。

## 2. 数学的な意味

各点で、すでに次があった。

$$
\mathrm{normalization}(t)^2\cdot\mathrm{depth}(t)=1
$$

正値性があるので log が取れる。すると点ごとに、

$$
2\log(\mathrm{normalization}(t))+\log(\mathrm{depth}(t))=0
$$

これを complete finite dyadic mesh 上で足すと、

$$
2\sum_k\log(\mathrm{normalization}*{n,k})+\sum_k\log(\mathrm{depth}*{n,k})=0
$$

になる。

今回の `dyadicPhaseLogDepthSum` と `dyadicPhaseLogNormalizationSum` は、まさにこの有限加法会計じゃ。

ここで重要なのは、まだ極限を選んでいないこと。
つまり、これは raw sum、average、weighted sum、Riemann sum のどれが canonical かを決める定理ではない。

あくまで、

```text id="u2pyfk"
有限積 cancellation と等価な有限 log cancellation
```

じゃ。
この慎重さは良い。

## 3. 実装レビュー

点ごとの positivity wrapper は正しい。

```lean id="26doeq"
theorem dyadicPhaseDepth_pos (n k : ℕ) :
    0 < dyadicPhaseDepth n k :=
  phaseDepth_pos (dyadicPhaseNode n k)
```

```lean id="8pqzhf"
theorem dyadicPhaseNormalization_pos (n k : ℕ) :
    0 < dyadicPhaseNormalization n k :=
  phaseNormalization_pos (dyadicPhaseNode n k)
```

これで、以後の log 証明が `phaseDepth_pos (dyadicPhaseNode n k)` を毎回直接書かなくてよくなる。
これは小さいが、かなり効く API じゃ。

log sum 定義も素直じゃ。

```lean id="secxi0"
def dyadicPhaseLogDepthSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n, Real.log (dyadicPhaseDepth n k)
```

```lean id="ms4f8x"
def dyadicPhaseLogNormalizationSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n, Real.log (dyadicPhaseNormalization n k)
```

complete mesh をそのまま使っているので、finite product composition と完全に同じ index set 上で比較できる。これは良い。

点wise log theorem も良い。

```lean id="me2moy"
theorem two_mul_log_dyadicPhaseNormalization_add_log_depth
    (n k : ℕ) :
    2 * Real.log (dyadicPhaseNormalization n k) +
        Real.log (dyadicPhaseDepth n k) = 0
```

`congrArg Real.log` で multiplicative identity を log へ移し、`Real.log_mul`、`Real.log_pow`、`Real.log_one` で閉じている。
正値性から nonzero を出しているので、log の条件も筋が通っている。

`log(product) = sum(log)` の bridge も良い。

$$
\log(\mathrm{DepthProduct}(n))=\mathrm{LogDepthSum}(n)
$$

$$
\log(\mathrm{NormalizationProduct}(n))=\mathrm{LogNormalizationSum}(n)
$$

これにより、product 側と log-sum 側が同じ有限構造の二つの表現であることが Lean 上で明確になった。

## 4. 研究テーマとの関係

これは、かなり重要じゃ。

最終目標は、外部から Gaussian integral や \(\sqrt{\pi}\) を借りずに、CF2D 内部から Gaussian 型正規化定数を出すことじゃった。

そのためには、いつか次の形が必要になる。

$$
\exp(-x^2)
$$

Gaussian の本体は、二次型 \(x^2\) を **負の指数** に入れたものじゃ。
つまり、積の極限を直接見るより、log を取って additive exponent を見る方が自然になる。

今回の層は、この橋を作った。

```text id="nkled0"
finite product cancellation
  ↓
finite log-sum cancellation
  ↓
log density / weighted log sum の候補比較
  ↓
quadratic exponent の抽出
  ↓
Gaussian weight の検証
```

したがって、この差分は \(\sqrt{\pi}\) への道で **必要な中間層** じゃ。

## 5. 気になる点

大きな問題はない。
ただし、今後の解釈で注意すべき点はある。

### 5.1. raw log sum は canonical とは限らない

complete mesh の点数は \(2^n+1\) 個。
したがって raw sum は、mesh の細分化で項数が増える。

だから次に問うべきは、

```text id="4mgzg5"
raw sum を見るのか？
average を見るのか？
mesh 幅を掛けた Riemann sum を見るのか？
端点重みを変えるのか？
odd child だけを見るのか？
```

じゃ。

今回 docs で「raw sum、average、weighted sum のいずれも canonical として選んでいない」と書いているのは、非常に正しい。

### 5.2. complete mesh と midpoint mesh は違う

今回の log composition は complete node mesh 上の点wise law じゃ。
一方、defect は odd child midpoint に強く関係していた。

この二つは将来分ける必要がある。

```text id="1z5e2b"
complete node mesh:
  boundary restoration の点wise sampling

odd-child midpoint mesh:
  refinement defect の発生場所
```

Gaussian limit を探す時、どちらの mesh が自然かは未確定じゃ。
ここを混ぜない方がよい。

## 6. 次に足すと強い API

次は、canonical observable を選ぶ前に、候補を finite に並べるのが良い。

まず平均 log sum。

```lean id="7iimrz"
def dyadicPhaseAverageLogDepth (n : ℕ) : ℝ :=
  dyadicPhaseLogDepthSum n / (dyadicPhaseNodeIndices n).card
```

ただし Lean では card を ℝ に cast する形になる。

次に mesh-weighted log sum。

$$
h_n=\frac{1}{2^n}
$$

として、

$$
h_n\sum_k\log(\mathrm{depth}_{n,k})
$$

を定義する。

```lean id="nv0cqt"
def dyadicPhaseMeshWeight (n : ℕ) : ℝ :=
  1 / (dyadicPhaseDenom n : ℝ)
```

```lean id="wzq2bp"
def dyadicPhaseWeightedLogDepthSum (n : ℕ) : ℝ :=
  dyadicPhaseMeshWeight n * dyadicPhaseLogDepthSum n
```

ただし、端点を含む complete mesh なら台形重みも候補になる。

```text id="8zvcvo"
endpoint weight:
  1/2

interior weight:
  1
```

この台形則型は、Riemann integral へ向かうなら自然じゃ。

## 7. Gaussian へ向かう次の観測

`phaseDepth` は明示的に、

$$
\mathrm{phaseDepth}(t)=(1-t)^2+t^2
$$

中心 \(1/2\) で書くと、

$$
\mathrm{phaseDepth}(t)=\frac{1}{2}+2\left(t-\frac{1}{2}\right)^2
$$

したがって、

$$
\log(\mathrm{phaseDepth}(t))
=\log\left(\frac{1}{2}+2\left(t-\frac{1}{2}\right)^2\right)
$$

Gaussian に近づくには、これをどの scaling で見れば二次指数になるかを調べる必要がある。

局所的には、中心付近で、

$$
\log\left(\frac{1}{2}+2s^2\right)
=\log\left(\frac{1}{2}\right)+\log(1+4s^2)
$$

ここから二次項は \(4s^2\) 型で出る。
ただし、これはそのまま \(e^{-x^2}\) ではない。定数項、符号、スケール、normalization の取り方が必要じゃ。

ここから先が本丸じゃな。

```text id="gd939d"
log depth の中心二次展開
  ↓
normalization log の符号反転
  ↓
mesh scaling
  ↓
Gaussian candidate
```

## 8. 結論

今回の差分は採用でよい。

```text id="qhx7k4"
実装:
  良い。finite product cancellation を log-sum へ正しく移した。

数学:
  良い。乗法的 restoration が加法的 correction account になった。

研究位置:
  とても重要。Gaussian 型極限を探すための前提層。

安全性:
  良い。raw sum / average / weighted sum を canonical として選んでいない。

次:
  average log sum、mesh-weighted log sum、trapezoidal log sum、
  midpoint/odd-child log sum、中心二次展開の有限補題。
```

ぬしよ、これは良い。
いよいよ「積の会計」から「指数の会計」へ入った。

\(\sqrt{\pi}\) へ向かう道では、ここがかなり大事じゃ。
Gaussian は突然出るのではない。log の中に二次型が見え、その二次型が指数へ戻った時に現れる。今回、その入口が Lean に立った。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index 8ef8383d..0564df86 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -18,6 +18,7 @@ import DkMath.Analysis.DkReal.SemanticCF2DDyadic
 import DkMath.Analysis.DkReal.SemanticCF2DRefinement
 import DkMath.Analysis.DkReal.SemanticCF2DLimit
 import DkMath.Analysis.DkReal.SemanticCF2DComposition
+import DkMath.Analysis.DkReal.SemanticCF2DLogComposition
 import DkMath.Analysis.DkReal.SemanticCF2DPath
 import DkMath.Analysis.DkReal.SemanticCF2DNormalize
 import DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index c8d10ce4..447d8bf9 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -132,6 +132,13 @@ finite pointwise-composition theorem, not a selected infinite-product limit.
 Nonvanishing and reciprocal forms are also exposed for downstream finite
 algebra.
 
+[IMPLEMENTED: semantic-cf2d-finite-log-composition]
+`DkReal.SemanticCF2DLogComposition` transfers the positive finite
+cancellation law to logarithmic sums. Each log sum is identified with the
+logarithm of its finite product, and
+`2 * logNormalizationSum + logDepthSum = 0`. No logarithmic quantity is yet
+selected as the canonical refinement-limit observable.
+
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
 affine edge as a Mathlib `Path`. Four seam-compatible edges concatenate to a
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
new file mode 100644
index 00000000..c7ab945d
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -0,0 +1,91 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2DComposition
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DLogComposition"
+
+/-!
+# Finite logarithmic form of dyadic boundary cancellation
+
+All sampled depths and normalizations are strictly positive. Their finite
+products may therefore be transferred to additive logarithmic sums.
+
+The resulting identity
+
+`2 * logNormalizationSum + logDepthSum = 0`
+
+is exactly equivalent to the previously proved finite product cancellation.
+This module still does not select a logarithmic sum as the canonical
+refinement-limit observable.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+noncomputable section
+
+/-- Pointwise positivity of the dyadic phase-depth observation. -/
+theorem dyadicPhaseDepth_pos (n k : ℕ) :
+    0 < dyadicPhaseDepth n k :=
+  phaseDepth_pos (dyadicPhaseNode n k)
+
+/-- Pointwise positivity of the dyadic normalization observation. -/
+theorem dyadicPhaseNormalization_pos (n k : ℕ) :
+    0 < dyadicPhaseNormalization n k :=
+  phaseNormalization_pos (dyadicPhaseNode n k)
+
+/-- Finite sum of logarithmic depth observations over the complete mesh. -/
+def dyadicPhaseLogDepthSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n, Real.log (dyadicPhaseDepth n k)
+
+/-- Finite sum of logarithmic normalization observations over the complete mesh. -/
+def dyadicPhaseLogNormalizationSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n, Real.log (dyadicPhaseNormalization n k)
+
+/-- Pointwise boundary cancellation in additive logarithmic form. -/
+theorem two_mul_log_dyadicPhaseNormalization_add_log_depth
+    (n k : ℕ) :
+    2 * Real.log (dyadicPhaseNormalization n k) +
+        Real.log (dyadicPhaseDepth n k) = 0 := by
+  have h := congrArg Real.log
+    (dyadicPhaseNormalization_sq_mul_depth n k)
+  rw [Real.log_mul
+      (pow_ne_zero 2 (dyadicPhaseNormalization_pos n k).ne')
+      (dyadicPhaseDepth_pos n k).ne',
+    Real.log_pow, Real.log_one] at h
+  norm_num at h ⊢
+  linarith
+
+/-- The finite log-depth sum is the logarithm of the finite depth product. -/
+theorem log_dyadicPhaseDepthProduct (n : ℕ) :
+    Real.log (dyadicPhaseDepthProduct n) =
+      dyadicPhaseLogDepthSum n := by
+  rw [dyadicPhaseDepthProduct, dyadicPhaseLogDepthSum]
+  exact Real.log_prod fun k _ => (dyadicPhaseDepth_pos n k).ne'
+
+/--
+The finite log-normalization sum is the logarithm of the finite
+normalization product.
+-/
+theorem log_dyadicPhaseNormalizationProduct (n : ℕ) :
+    Real.log (dyadicPhaseNormalizationProduct n) =
+      dyadicPhaseLogNormalizationSum n := by
+  rw [dyadicPhaseNormalizationProduct, dyadicPhaseLogNormalizationSum]
+  exact Real.log_prod fun k _ => (dyadicPhaseNormalization_pos n k).ne'
+
+/-- Finite boundary cancellation in additive logarithmic form. -/
+theorem two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum
+  (n : ℕ) :
+    2 * dyadicPhaseLogNormalizationSum n +
+        dyadicPhaseLogDepthSum n = 0 := by
+  rw [dyadicPhaseLogNormalizationSum, dyadicPhaseLogDepthSum,
+    Finset.mul_sum, ← Finset.sum_add_distrib]
+  exact Finset.sum_eq_zero fun k hk =>
+    two_mul_log_dyadicPhaseNormalization_add_log_depth n k
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index a78f93e5..fcce9113 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -195,6 +195,19 @@ pointwise boundary-restoration law through finite multiplication. It does not
 yet identify either product as the canonical refinement observable, nor does
 it justify an infinite product or logarithmic limit.
 
+`SemanticCF2DLogComposition.lean` now records the equivalent finite additive
+form. Pointwise positivity permits logarithms, and summation over the same
+complete mesh gives
+
+```text
+2 * logNormalizationSum + logDepthSum = 0.
+```
+
+The two sums are proved equal to the logarithms of their respective finite
+products. This equivalence supplies a comparison surface for later limit
+selection; it does not select the raw sum, an average, or a weighted sum as
+canonical.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 70e87139..4df85cc8 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -382,6 +382,10 @@ On the complete finite dyadic mesh, the squared product of sampled
 normalizations exactly cancels the product of sampled depths. Both products
 are strictly positive and nonzero, and the cancellation law is available in
 both reciprocal forms.
+[IMPLEMENTED: semantic-cf2d-phase/finite-log-composition] Positivity permits
+the same finite law to be expressed as logarithmic sums:
+`2 * logNormalizationSum + logDepthSum = 0`. Each sum is also proved equal
+to the logarithm of its corresponding finite product.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
 finite product, logarithmic sum, or another quantity has a canonical
 refinement limit. The finite cancellation theorem alone does not select one.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index bac4143c..75a91eb2 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -897,3 +897,24 @@ Archive
 3. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DComposition` 成功
      (8280 jobs)。
+
+### 2026/06/23 20:49 JST (Finite logarithmic composition)
+
+1. module:
+   - `SemanticCF2DLogComposition.lean` を新設し、公開 Analysis entry point
+     へ追加した。
+2. positivity:
+   - dyadic depth と normalization の pointwise positivity wrapper を
+     追加した。
+3. finite log laws:
+   - depth / normalization の complete-mesh log sum を定義した。
+   - 各 log sum が対応する finite product の log に等しいことを証明した。
+   - pointwise および finite mesh 全体で
+     `2 * logNormalization + logDepth = 0` を証明した。
+4. boundary:
+   - log sum は finite product cancellation の加法表示に限定した。
+     raw sum、average、weighted sum のいずれも canonical limit として
+     選択していない。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
