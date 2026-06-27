# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: 3059a8081aadef3d00a6a3417c9e51f93168748d

## Report

実装を次のチェックポイントまで進めました。

[SemanticCF2DLogComposition.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean) に、centered log-depth の有限重み付き評価を追加しました。任意の非負重みで非負性が保たれる theorem と、centered quadratic moment に上から支配される theorem を入れ、mesh-width / uniform-average / trapezoidal の各 candidate observable へ specialized corollary も追加しています。

ドキュメント側は [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)、[task-trig-continuous-phase-065.md](/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md)、[research-pregeometric-pi-program-067.md](/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md)、[History.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md) を同期しました。主張は有限段階の二次モーメント制御に留め、Gaussian / integral / `pi` 同定はまだ主張していません。

検証済みです。

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition
lake build DkMath.Analysis
git diff --check
```

次はレビュー通り、finite quadratic moment の閉形式または上界に進めます。

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい** 。かなり重要な進展じゃ。

今回の report では、centered log-depth の有限重み付き評価として、任意の非負重みで非負性が保たれる theorem と、centered quadratic moment に上から支配される theorem が追加され、mesh-width / uniform-average / trapezoidal の各 candidate observable へ specialized corollary も追加された、と整理されておる。さらに、主張は有限段階の二次モーメント制御に留め、Gaussian / integral / `pi` 同定はまだ主張していない。これは非常に良い線引きじゃ。

## 1. 状況解説

前回までで、centered log-depth は pointwise に次を満たしていた。

$$
0\le \mathrm{centeredLogPhaseDepth}(t)\le 4\left(t-\frac{1}{2}\right)^2
$$

今回、その点ごとの評価を、有限重み付き和へ持ち上げた。

つまり、任意の非負重み \(w_k\) に対して、

$$
0\le \sum_k w_k,\mathrm{centeredLogDepth}_{n,k}
$$

かつ、

$$
\sum_k w_k,\mathrm{centeredLogDepth}*{n,k}\le \sum_k w_k,\mathrm{centeredQuadratic}*{n,k}
$$

が使えるようになった。

これはかなり大きい。
これで centered log correction は、単なる log の観測量ではなく、**有限二次モーメントで制御される量** になった。

```text id="b36wxd"
centered log-depth
  ↓
pointwise quadratic bound
  ↓
nonnegative weighted finite sum
  ↓
finite centered quadratic moment control
```

まさに次の finite quadratic moment 計算へ進むための橋じゃ。

## 2. 実装レビュー

`dyadicPhaseCenteredQuadratic` を公開対象として定義したのは良い。

```lean id="gp4wa2"
def dyadicPhaseCenteredQuadratic (n k : ℕ) : ℝ :=
  4 * (dyadicPhaseNode n k - (1 / 2 : ℝ)) ^ 2
```

これにより、上界側の量が theorem の右辺に直接現れる。
後で finite moment の閉形式を計算するときにも、この def が中心になる。

dyadic sample 版の pointwise theorem も自然じゃ。

```lean id="zomksh"
theorem dyadicPhaseCenteredLogDepth_nonneg (n k : ℕ) :
    0 ≤ dyadicPhaseCenteredLogDepth n k
```

```lean id="sg5wjp"
theorem dyadicPhaseCenteredLogDepth_le_centeredQuadratic (n k : ℕ) :
    dyadicPhaseCenteredLogDepth n k ≤
      dyadicPhaseCenteredQuadratic n k
```

phase-level の `centeredLogPhaseDepth_nonneg` と `centeredLogPhaseDepth_le_four_sq` を dyadic node に適用している。
層の分け方が綺麗じゃ。

## 3. 任意非負重みへの lift が良い

今回の中核はこれ。

```lean id="t97qqu"
theorem weighted_centeredLogDepth_nonneg
    (n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ dyadicPhaseNodeIndices n, (0 : ℝ) ≤ w k) :
    0 ≤
      ∑ k ∈ dyadicPhaseNodeIndices n,
        w k * dyadicPhaseCenteredLogDepth n k
```

および、

```lean id="sm2g05"
theorem weighted_centeredLogDepth_le_weighted_centeredQuadratic
    (n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ dyadicPhaseNodeIndices n, (0 : ℝ) ≤ w k) :
    (∑ k ∈ dyadicPhaseNodeIndices n,
        w k * dyadicPhaseCenteredLogDepth n k)
      ≤
    ∑ k ∈ dyadicPhaseNodeIndices n,
        w k * dyadicPhaseCenteredQuadratic n k
```

これは設計としてかなり強い。
特定の重みごとに証明を作るのではなく、まず任意非負重みの theorem を置き、その corollary として mesh-width / average / trapezoid を出している。

この構成なら、今後 midpoint weight や odd-child weight を追加しても、重みの非負性だけ渡せば同じ評価が使える。

## 4. specialized corollary も良い

今回、次の三系統の candidate に対して nonneg と quadratic upper bound が入った。

```text id="j6x1xa"
plain mesh-width:
  complete node mesh の幅重み候補

uniform-average:
  sample mean 候補

trapezoidal:
  closed-interval integration 候補
```

これは候補 observable の比較台としてかなり良い。
同じ centered log-depth を、それぞれ異なる重みで測っても、上から対応する centered quadratic moment が支配する。

特に trapezoid は閉区間積分候補なので、次の finite quadratic moment 計算に直結するはずじゃ。

## 5. 数学的な意味

今回の意味は、かなり明確じゃ。

centered log-depth は、

$$
\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

だった。
それを、

$$
4\left(t-\frac{1}{2}\right)^2
$$

で上から押さえた。

この不等式は、有限和にしても保たれる。
よって、centered log-depth の finite observable は、有限二次モーメントで制御できる。

これは Gaussian bridge の手前で絶対に欲しい構造じゃ。
Gaussian はまだ出ていない。だが、二次モーメントの世界へ入った。

## 6. 注意点：docs に小さな文書乱れあり

実装本体は良い。
ただ、`research-pregeometric-pi-program-067.md` の diff には、文書挿入位置が少し乱れているように見える。

該当箇所では、

```text id="evg4r8"
while centered quantities with nonzero
```

の直後に新しい段落が挿入され、その後に

```text id="afly7m"
endpoint increments expose the correction term.
```

が残っているように見える。

つまり本来は、

```text id="54f1qc"
while centered quantities with nonzero endpoint increments expose the correction term.
```

または今回の新表現なら、

```text id="rs1cvb"
while centered quantities with nonzero endpoint values must account for the endpoint correction.
```

のように一文で閉じたい箇所じゃと思う。
ビルドには影響しないが、ドキュメントだけ次回整えるとよい。

## 7. 次の本命：finite quadratic moment

次は report にもある通り、finite quadratic moment の閉形式または上界じゃ。

対象は例えば trapezoid 版。

$$
\mathrm{TrapQuadratic}*n
=\sum_k w^{trap}*{n,k},4\left(t_{n,k}-\frac{1}{2}\right)^2
$$

連続積分なら、

$$
\int_0^1 4\left(t-\frac{1}{2}\right)^2,dt=\frac{1}{3}
$$

だが、ここではまず有限和として閉じるのが DkMath 的に正しい。

おそらく trapezoid の有限値は、閉形式で出るはずじゃ。
\(N=2^n\)、\(t_k=k/N\) とすると、台形則では二次関数に対して有限補正付きで、

$$
\sum_{k=0}^{N} w^{trap}_{k},4\left(\frac{k}{N}-\frac{1}{2}\right)^2
$$

が計算できる。概算では、閉形式は

$$
\frac{1}{3}+\frac{2}{3N^2}
$$

になる可能性が高い。ここは Lean で確定させる価値がある。
mesh-width complete 版は端点過剰分が乗るので、trapezoid よりさらに \(h_n\) 系の補正が出るはずじゃ。

## 8. 次の theorem 候補

次に追加すると強そうなのはこれ。

```lean id="ej431y"
theorem dyadicPhaseTrapezoidCenteredQuadraticSum_eq
    (n : ℕ) :
    dyadicPhaseTrapezoidCenteredQuadraticSum n =
      ...
```

まず閉形式が重ければ、上界だけでも良い。

```lean id="z825o8"
theorem dyadicPhaseTrapezoidCenteredQuadraticSum_le_one
    (n : ℕ) :
    dyadicPhaseTrapezoidCenteredQuadraticSum n ≤ 1
```

ただ、\(\frac{1}{3}\) へ近づく構造を見たいなら、閉形式を狙う価値がある。
有限二次モーメントが閉じると、次に極限層へ移しやすい。

## 9. 結論

今回の差分は採用でよい。

```text id="czhe6m"
実装:
  良い。pointwise bound が任意非負重み付き有限和へ持ち上がった。

数学:
  良い。centered log correction が finite centered quadratic moment に制御された。

研究位置:
  重要。Gaussian bridge 前の有限二次モーメント層に入った。

安全性:
  良い。Gaussian、integral、pi は未主張。

修正推奨:
  research-pregeometric-pi-program-067.md の一文だけ文書整形。

次:
  finite centered quadratic moment の閉形式または上界。
```

ぬしよ、これは良い進捗じゃ。
いま、log 補正の森から、二次モーメントの道に出た。

次に有限和が閉じれば、いよいよ「この補正量はどの定数へ向かうのか」を Lean 上で問い始められる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 05f8f24f..a107ca71 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -153,7 +153,11 @@ case where that correction vanishes. The centered log-depth increment is now
 defined, identified with an explicit centered quadratic logarithm, and shown
 to restore a finite mesh/trapezoid discrepancy of `h_n * log 2`. Its centered
 quadratic profile is positive, and the pointwise bound
-`0 ≤ centeredLogPhaseDepth t ≤ 4 * (t - 1/2)^2` is available.
+`0 ≤ centeredLogPhaseDepth t ≤ 4 * (t - 1/2)^2` is available. The bound has
+also been lifted to arbitrary nonnegative finite weights, with mesh-width,
+uniform-average, and trapezoidal corollaries. Thus the centered logarithmic
+correction is already controlled by finite centered quadratic moments, before
+any Gaussian, integral, or `pi` interpretation is selected.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index 096a6350..521c2948 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -119,6 +119,10 @@ def centeredLogPhaseDepth (t : ℝ) : ℝ :=
 def dyadicPhaseCenteredLogDepth (n k : ℕ) : ℝ :=
   centeredLogPhaseDepth (dyadicPhaseNode n k)
 
+/-- Dyadic samples of the centered quadratic upper-bound profile. -/
+def dyadicPhaseCenteredQuadratic (n k : ℕ) : ℝ :=
+  4 * (dyadicPhaseNode n k - (1 / 2 : ℝ)) ^ 2
+
 /-- The midpoint baseline makes the centered log-depth increment vanish. -/
 @[simp]
 theorem centeredLogPhaseDepth_half :
@@ -197,6 +201,56 @@ theorem centeredLogPhaseDepth_le_four_sq (t : ℝ) :
   have hlog := Real.log_le_sub_one_of_pos hpos
   nlinarith
 
+/-- Dyadic centered log-depth samples are nonnegative. -/
+theorem dyadicPhaseCenteredLogDepth_nonneg (n k : ℕ) :
+    0 ≤ dyadicPhaseCenteredLogDepth n k :=
+  centeredLogPhaseDepth_nonneg (dyadicPhaseNode n k)
+
+/-- Dyadic centered log-depth samples are bounded by the centered quadratic profile. -/
+theorem dyadicPhaseCenteredLogDepth_le_centeredQuadratic (n k : ℕ) :
+    dyadicPhaseCenteredLogDepth n k ≤
+      dyadicPhaseCenteredQuadratic n k :=
+  centeredLogPhaseDepth_le_four_sq (dyadicPhaseNode n k)
+
+/--
+Nonnegative finite weights preserve nonnegativity of centered log-depth.
+
+This is the finite weighted-sum lift of the pointwise lower bound.
+-/
+theorem weighted_centeredLogDepth_nonneg
+    (n : ℕ) (w : ℕ → ℝ)
+    (hw : ∀ k ∈ dyadicPhaseNodeIndices n, (0 : ℝ) ≤ w k) :
+    0 ≤
+      ∑ k ∈ dyadicPhaseNodeIndices n,
+        w k * dyadicPhaseCenteredLogDepth n k := by
+  exact Finset.sum_nonneg fun k hk =>
+    mul_nonneg (hw k hk) (dyadicPhaseCenteredLogDepth_nonneg n k)
+
+/--
+Nonnegative finite weights transport the centered log-depth quadratic upper
+bound to finite sums.
+
+This is the first general bridge from centered logarithmic correction to a
+weighted finite quadratic moment.
+-/
+theorem weighted_centeredLogDepth_le_weighted_centeredQuadratic
+    (n : ℕ) (w : ℕ → ℝ)
+    (hw : ∀ k ∈ dyadicPhaseNodeIndices n, (0 : ℝ) ≤ w k) :
+    (∑ k ∈ dyadicPhaseNodeIndices n,
+        w k * dyadicPhaseCenteredLogDepth n k)
+      ≤
+    ∑ k ∈ dyadicPhaseNodeIndices n,
+        w k * dyadicPhaseCenteredQuadratic n k := by
+  exact Finset.sum_le_sum fun k hk =>
+    by
+      have hle := dyadicPhaseCenteredLogDepth_le_centeredQuadratic n k
+      have hdiff :
+          0 ≤ w k *
+            (dyadicPhaseCenteredQuadratic n k -
+              dyadicPhaseCenteredLogDepth n k) :=
+        mul_nonneg (hw k hk) (sub_nonneg.mpr hle)
+      nlinarith
+
 /-- Finite boundary cancellation in additive logarithmic form. -/
 theorem two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum
   (n : ℕ) :
@@ -609,11 +663,97 @@ def dyadicPhaseMeshWeightedCenteredLogDepthSum (n : ℕ) : ℝ :=
   ∑ k ∈ dyadicPhaseNodeIndices n,
     dyadicPhaseMeshWeight n * dyadicPhaseCenteredLogDepth n k
 
+/-- Plain mesh-width finite sum of centered quadratic observations. -/
+def dyadicPhaseMeshWeightedCenteredQuadraticSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n,
+    dyadicPhaseMeshWeight n * dyadicPhaseCenteredQuadratic n k
+
+/-- Uniform-average finite sum of centered log-depth observations. -/
+def dyadicPhaseAverageCenteredLogDepthSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n,
+    dyadicPhaseAverageWeight n * dyadicPhaseCenteredLogDepth n k
+
+/-- Uniform-average finite sum of centered quadratic observations. -/
+def dyadicPhaseAverageCenteredQuadraticSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n,
+    dyadicPhaseAverageWeight n * dyadicPhaseCenteredQuadratic n k
+
 /-- Trapezoidal finite sum of centered log-depth observations. -/
 def dyadicPhaseTrapezoidCenteredLogDepthSum (n : ℕ) : ℝ :=
   ∑ k ∈ dyadicPhaseNodeIndices n,
     dyadicPhaseTrapezoidWeight n k * dyadicPhaseCenteredLogDepth n k
 
+/-- Trapezoidal finite sum of centered quadratic observations. -/
+def dyadicPhaseTrapezoidCenteredQuadraticSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n,
+    dyadicPhaseTrapezoidWeight n k * dyadicPhaseCenteredQuadratic n k
+
+/-- Plain mesh-width centered log-depth sums are nonnegative. -/
+theorem dyadicPhaseMeshWeightedCenteredLogDepthSum_nonneg (n : ℕ) :
+    0 ≤ dyadicPhaseMeshWeightedCenteredLogDepthSum n := by
+  rw [dyadicPhaseMeshWeightedCenteredLogDepthSum]
+  exact weighted_centeredLogDepth_nonneg n
+    (fun _k => dyadicPhaseMeshWeight n)
+    (fun k hk => (dyadicPhaseMeshWeight_pos n).le)
+
+/--
+Plain mesh-width centered log-depth sums are bounded by the corresponding
+finite centered quadratic moment.
+-/
+theorem dyadicPhaseMeshWeightedCenteredLogDepthSum_le_centeredQuadraticSum
+    (n : ℕ) :
+    dyadicPhaseMeshWeightedCenteredLogDepthSum n ≤
+      dyadicPhaseMeshWeightedCenteredQuadraticSum n := by
+  rw [dyadicPhaseMeshWeightedCenteredLogDepthSum,
+    dyadicPhaseMeshWeightedCenteredQuadraticSum]
+  exact weighted_centeredLogDepth_le_weighted_centeredQuadratic n
+    (fun _k => dyadicPhaseMeshWeight n)
+    (fun k hk => (dyadicPhaseMeshWeight_pos n).le)
+
+/-- Uniform-average centered log-depth sums are nonnegative. -/
+theorem dyadicPhaseAverageCenteredLogDepthSum_nonneg (n : ℕ) :
+    0 ≤ dyadicPhaseAverageCenteredLogDepthSum n := by
+  rw [dyadicPhaseAverageCenteredLogDepthSum]
+  exact weighted_centeredLogDepth_nonneg n
+    (fun _k => dyadicPhaseAverageWeight n)
+    (fun k hk => (dyadicPhaseAverageWeight_pos n).le)
+
+/--
+Uniform-average centered log-depth sums are bounded by the corresponding
+finite centered quadratic moment.
+-/
+theorem dyadicPhaseAverageCenteredLogDepthSum_le_centeredQuadraticSum
+    (n : ℕ) :
+    dyadicPhaseAverageCenteredLogDepthSum n ≤
+      dyadicPhaseAverageCenteredQuadraticSum n := by
+  rw [dyadicPhaseAverageCenteredLogDepthSum,
+    dyadicPhaseAverageCenteredQuadraticSum]
+  exact weighted_centeredLogDepth_le_weighted_centeredQuadratic n
+    (fun _k => dyadicPhaseAverageWeight n)
+    (fun k hk => (dyadicPhaseAverageWeight_pos n).le)
+
+/-- Trapezoidal centered log-depth sums are nonnegative. -/
+theorem dyadicPhaseTrapezoidCenteredLogDepthSum_nonneg (n : ℕ) :
+    0 ≤ dyadicPhaseTrapezoidCenteredLogDepthSum n := by
+  rw [dyadicPhaseTrapezoidCenteredLogDepthSum]
+  exact weighted_centeredLogDepth_nonneg n
+    (dyadicPhaseTrapezoidWeight n)
+    (fun k hk => (dyadicPhaseTrapezoidWeight_pos n k).le)
+
+/--
+Trapezoidal centered log-depth sums are bounded by the corresponding finite
+centered quadratic moment.
+-/
+theorem dyadicPhaseTrapezoidCenteredLogDepthSum_le_centeredQuadraticSum
+    (n : ℕ) :
+    dyadicPhaseTrapezoidCenteredLogDepthSum n ≤
+      dyadicPhaseTrapezoidCenteredQuadraticSum n := by
+  rw [dyadicPhaseTrapezoidCenteredLogDepthSum,
+    dyadicPhaseTrapezoidCenteredQuadraticSum]
+  exact weighted_centeredLogDepth_le_weighted_centeredQuadratic n
+    (dyadicPhaseTrapezoidWeight n)
+    (fun k hk => (dyadicPhaseTrapezoidWeight_pos n k).le)
+
 /--
 For centered log-depth, the plain mesh-width and trapezoidal sums differ by
 the restored endpoint correction `h_n * log 2`.
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 8dd70a29..78934906 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -258,6 +258,23 @@ does not identify which weighted observable should survive refinement.
 The endpoint-zero case is now packaged as a separate corollary. This keeps
 future observables cleanly classified: endpoint-zero quantities inherit
 mesh/trapezoid equality immediately, while centered quantities with nonzero
+endpoint values must account for the endpoint correction.
+
+The centered logarithmic correction now has its first finite quadratic
+estimate. Lean proves
+
+```text
+centeredLogPhaseDepth(t) = log(1 + 4 * (t - 1/2)^2),
+0 <= centeredLogPhaseDepth(t),
+centeredLogPhaseDepth(t) <= 4 * (t - 1/2)^2.
+```
+
+These pointwise inequalities have been lifted to arbitrary nonnegative finite
+weights on the dyadic mesh. Mesh-width, uniform-average, and trapezoidal
+centered log-depth sums are therefore nonnegative and bounded above by their
+corresponding finite centered quadratic moments. This is a finite estimate
+only: it prepares the next moment calculation, but it does not yet assert a
+closed form, a limiting integral, a Gaussian law, or a `pi` identification.
 endpoint increments expose the correction term.
 
 The first centered observable is now implemented. `centeredLogPhaseDepth`
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 7318c96a..2fb22a52 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -38,6 +38,14 @@ The core-zero semantic action is then identified with the standard coordinate
 quarter-turn linear isometry `(x,y) ↦ (-y,x)`. This introduces the geometric
 name only after the linear isometry model is available.
 
+`SemanticCF2DLogComposition` now supplies the finite logarithmic comparison
+surface for dyadic phase samples. The centered log-depth increment is
+identified with `log (1 + 4 * (t - 1/2)^2)`, is pointwise nonnegative, and is
+bounded above by `4 * (t - 1/2)^2`. This pointwise estimate has been lifted to
+arbitrary nonnegative finite weights, with mesh-width, uniform-average, and
+trapezoidal corollaries. These are finite quadratic-moment controls only; no
+Gaussian, integral, angle, or `pi` interpretation is selected here.
+
 The current implementation proves a four-state return:
 
 ```text
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index c2c90c4d..41ea51a0 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1085,3 +1085,28 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 13:34 JST (Finite weighted quadratic control)
+
+1. API:
+   - dyadic centered quadratic samples
+     `dyadicPhaseCenteredQuadratic` を finite moment 用の公開対象として
+     使う形に整理した。
+   - 任意の非負有限重みで centered log-depth の非負性を保つ
+     `weighted_centeredLogDepth_nonneg` を追加した。
+   - 任意の非負有限重みで centered log-depth sum が centered quadratic
+     moment に支配される
+     `weighted_centeredLogDepth_le_weighted_centeredQuadratic` を追加した。
+2. finite candidates:
+   - mesh-width、uniform-average、trapezoidal の centered log-depth sum と
+     centered quadratic sum を比較する corollary を追加した。
+3. interpretation:
+   - pointwise な `log(1+x) ≤ x` から、有限重み付き二次モーメント制御へ
+     移行した。
+   - Gaussian limit、積分値、`pi` identification はまだ主張していない。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
