# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: 1253877c40a925ccaf0ad0f6f409c2252c2dc735

## Report

進めました。

[SemanticCF2DLogComposition.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean) に、有限二次モーメントの最初の上界を追加しました。

追加内容:

- `centeredQuadratic_le_one_of_mem_unit`
- `dyadicPhaseCenteredQuadratic_le_one`
- `dyadicPhaseTrapezoidCenteredQuadraticSum_le_one`

台形重みの total mass が `1` で、各 dyadic node の centered quadratic profile が `≤ 1` なので、有限段階で

```lean
dyadicPhaseTrapezoidCenteredQuadraticSum n ≤ 1
```

まで閉じています。閉形式 `1 / 3 + 2 / (3 * (2^n)^2)` は少し重い有限二乗和計算になるため、コード中に `[TODO: finite-trapezoid-quadratic-closed-form]` として残しました。

併せて、レビュー指摘の [research-pregeometric-pi-program-067.md](/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md) の文書崩れを修正し、[DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)、[task-trig-continuous-phase-065.md](/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md)、[History.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md) も同期しました。

検証済みです。

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition
lake build DkMath.Analysis
git diff --check
```

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい** 。派手な閉形式までは行っていないが、有限二次モーメント層への最初の上界として、とても堅い一歩じゃ。

今回の report では、`centeredQuadratic_le_one_of_mem_unit`、`dyadicPhaseCenteredQuadratic_le_one`、`dyadicPhaseTrapezoidCenteredQuadraticSum_le_one` が追加され、台形重みの total mass が \(1\)、各 dyadic node の centered quadratic profile が \(1\) 以下であることから、有限段階で `dyadicPhaseTrapezoidCenteredQuadraticSum n ≤ 1` まで閉じた、と整理されておる。閉形式は TODO として残し、文書崩れも修正済みじゃな。

## 1. 状況解説

前回までで、centered log-depth は有限重み付き二次モーメントに支配されるところまで来ていた。

$$
\sum_k w_k,\mathrm{centeredLogDepth}*{n,k}\le \sum_k w_k,\mathrm{centeredQuadratic}*{n,k}
$$

今回、その右辺である centered quadratic moment に、最初の粗い有限上界を入れた。

$$
\mathrm{TrapezoidCenteredQuadraticSum}_n\le 1
$$

つまり、trapezoid candidate については、

$$
0\le \mathrm{TrapezoidCenteredLogDepthSum}_n\le \mathrm{TrapezoidCenteredQuadraticSum}_n\le 1
$$

という有限評価の鎖が見えるようになった。

これは Gaussian や \(\pi\) ではない。
しかし、centered log correction が有限段階で暴走しない、という大事な制御じゃ。

## 2. 実装レビュー

`centeredQuadratic_le_one_of_mem_unit` は良い。

```lean
theorem centeredQuadratic_le_one_of_mem_unit
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    4 * (t - (1 / 2 : ℝ)) ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg (t - (1 / 2 : ℝ)),
    sq_nonneg (t - 1), sq_nonneg t]
```

これは、区間 \(0\le t\le 1\) 上では中心からの距離が高々 \(1/2\) である、という事実を二次式で押さえている。

$$
0\le t\le 1\quad\Rightarrow\quad 4\left(t-\frac{1}{2}\right)^2\le 1
$$

`nlinarith` で閉じているのも自然じゃ。

`dyadicPhaseCenteredQuadratic_le_one` も良い。

```lean
theorem dyadicPhaseCenteredQuadratic_le_one
    {n k : ℕ} (hk : k ∈ dyadicPhaseNodeIndices n) :
    dyadicPhaseCenteredQuadratic n k ≤ 1 := by
  have hk_le : k ≤ dyadicPhaseDenom n := by
    simpa [dyadicPhaseNodeIndices, Nat.lt_succ_iff] using hk
  have hunit := dyadicPhaseNode_mem_unitInterval (n := n) (k := k) hk_le
  exact centeredQuadratic_le_one_of_mem_unit hunit.1 hunit.2
```

complete dyadic node が単位区間に入ることを使って、pointwise bound を sample bound へ移している。
層の使い方が綺麗じゃ。

## 3. 台形二次モーメント上界

主定理も良い。

```lean
theorem dyadicPhaseTrapezoidCenteredQuadraticSum_le_one (n : ℕ) :
    dyadicPhaseTrapezoidCenteredQuadraticSum n ≤ 1 := by
```

証明方針は明快じゃ。

```text
各 sampled quadratic が 1 以下。
台形重みは非負。
台形重みの総量は 1。
したがって weighted sum は 1 以下。
```

これは確率測度的に読むと、「総量 \(1\) の非負重みで、値が \(1\) 以下の関数を平均しているので \(1\) 以下」というだけじゃ。
その基本構造が Lean で綺麗に通っている。

## 4. 研究上の意味

今回の上界は粗い。
しかし、粗いから意味が薄いわけではない。

いま欲しいのは、まず finite observable が安全に制御されることじゃ。
その意味で、

$$
\mathrm{TrapezoidCenteredLogDepthSum}_n\le 1
$$

まで合成できるのは大きい。

なぜなら、前回の結果と合わせれば、

$$
\mathrm{TrapezoidCenteredLogDepthSum}_n\le \mathrm{TrapezoidCenteredQuadraticSum}_n
$$

かつ、

$$
\mathrm{TrapezoidCenteredQuadraticSum}_n\le 1
$$

だからじゃ。

つまり、centered log correction は、台形 candidate では有限段階で一様に bounded になる。

```text
centered log correction:
  finite に非負

quadratic moment:
  finite に上から支配

trapezoid candidate:
  total mass one により一様上界
```

これは次の極限議論へ行く前の足場として良い。

## 5. TODO の置き方も良い

閉形式を急がず、

```text
[TODO: finite-trapezoid-quadratic-closed-form]
```

として残したのは良い判断じゃ。

予想される閉形式は、

$$
\frac{1}{3}+\frac{2}{3(2^n)^2}
$$

または `dyadicPhaseDenom n` を使って、

$$
\frac{1}{3}+\frac{2}{3(\mathrm{dyadicPhaseDenom}\ n)^2}
$$

の形じゃな。

ただ、これは有限二乗和の計算が必要になる。
いま無理に詰め込むより、まず (≤1) の上界で finite control を確保しておくのは正しい。

## 6. 文書修正も良い

前回指摘した `research-pregeometric-pi-program-067.md` の stray sentence が消えている。
これはよい。研究メモは今後も参照されるので、こういう小さな文書崩れを早めに整えるのは大事じゃ。

今回の文書追加も、「粗い有限 bound」「閉形式は次の target」「Gaussian / integral / `pi` は未主張」という線引きが守られている。

## 7. 気になる点

大きな問題はない。

ただし、次に閉形式へ進むなら、`dyadicPhaseDenom n` を \(N\) と見て有限和を扱う補助層を少し切り出すとよいかもしれぬ。

いきなり `dyadicPhaseTrapezoidCenteredQuadraticSum_eq` を殴るより、次のような一般補題を作る方が安全じゃ。

```lean
theorem sum_range_sq_centered ...
```

または、まず自然数和の基本形を押さえる。

$$
\sum_{k=0}^{N} k=\frac{N(N+1)}{2}
$$

$$
\sum_{k=0}^{N} k^2=\frac{N(N+1)(2N+1)}{6}
$$

Mathlib に既存補題があるなら、それを使うのがよい。
なければ局所補題として作る。

## 8. 次の実装候補

次は二通りある。

一つ目は、いきなり閉形式。

```lean
theorem dyadicPhaseTrapezoidCenteredQuadraticSum_eq
    (n : ℕ) :
    dyadicPhaseTrapezoidCenteredQuadraticSum n =
      1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2)
```

二つ目は、閉形式前の中間上界。

$$
\mathrm{TrapezoidCenteredQuadraticSum}_n\le \frac{1}{2}
$$

や、

$$
\mathrm{TrapezoidCenteredQuadraticSum}_n\le \frac{2}{3}
$$

などもあり得るが、どうせ有限二乗和が必要になるなら、閉形式を狙ってよいと思う。

ただし、まずは \(N=\mathrm{dyadicPhaseDenom}\ n\) の一般形で証明するのが良い。

```lean
theorem trapezoid_centered_quadratic_sum_eq_of_pos
    {N : ℕ} (hN : 0 < N) :
    ...
```

これを dyadic に適用すると、構造が分かれやすい。

## 9. 結論

今回の差分は採用でよい。

```text
実装:
  良い。有限二次モーメントの最初の粗い上界が入った。

数学:
  良い。centered quadratic profile が単位区間で 1 以下と分かった。

研究位置:
  良い。centered log correction の finite boundedness が確保された。

安全性:
  良い。Gaussian、integral、pi は未主張。

文書:
  良い。前回の文書崩れも修正済み。

次:
  finite trapezoid centered quadratic moment の閉形式。
```

ぬしよ、これは良い進め方じゃ。
まず荒い柵として (≤1) を立てた。次に閉形式を出せば、この二次モーメントがどの値へ向かうかが見える。

そこまで行くと、いよいよ centered log correction の「有限から極限へ」の橋が、かなり明瞭になるはずじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index a107ca71..fa58f8c3 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -157,7 +157,10 @@ quadratic profile is positive, and the pointwise bound
 also been lifted to arbitrary nonnegative finite weights, with mesh-width,
 uniform-average, and trapezoidal corollaries. Thus the centered logarithmic
 correction is already controlled by finite centered quadratic moments, before
-any Gaussian, integral, or `pi` interpretation is selected.
+any Gaussian, integral, or `pi` interpretation is selected. The first crude
+finite moment estimate is also available: the trapezoidal centered quadratic
+sum is bounded by one. The sharper closed form remains a tagged TODO in the
+log-composition module.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index 521c2948..fb4bb985 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -212,6 +212,27 @@ theorem dyadicPhaseCenteredLogDepth_le_centeredQuadratic (n k : ℕ) :
       dyadicPhaseCenteredQuadratic n k :=
   centeredLogPhaseDepth_le_four_sq (dyadicPhaseNode n k)
 
+/--
+The centered quadratic profile is at most one on the unit interval.
+
+This is the finite real-line bound behind the first crude moment estimate.
+The sharper trapezoidal closed form is left for the next finite-sum layer.
+-/
+theorem centeredQuadratic_le_one_of_mem_unit
+    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
+    4 * (t - (1 / 2 : ℝ)) ^ 2 ≤ 1 := by
+  nlinarith [sq_nonneg (t - (1 / 2 : ℝ)),
+    sq_nonneg (t - 1), sq_nonneg t]
+
+/-- Dyadic centered quadratic samples are at most one on the complete mesh. -/
+theorem dyadicPhaseCenteredQuadratic_le_one
+    {n k : ℕ} (hk : k ∈ dyadicPhaseNodeIndices n) :
+    dyadicPhaseCenteredQuadratic n k ≤ 1 := by
+  have hk_le : k ≤ dyadicPhaseDenom n := by
+    simpa [dyadicPhaseNodeIndices, Nat.lt_succ_iff] using hk
+  have hunit := dyadicPhaseNode_mem_unitInterval (n := n) (k := k) hk_le
+  exact centeredQuadratic_le_one_of_mem_unit hunit.1 hunit.2
+
 /--
 Nonnegative finite weights preserve nonnegativity of centered log-depth.
 
@@ -754,6 +775,36 @@ theorem dyadicPhaseTrapezoidCenteredLogDepthSum_le_centeredQuadraticSum
     (dyadicPhaseTrapezoidWeight n)
     (fun k hk => (dyadicPhaseTrapezoidWeight_pos n k).le)
 
+/--
+The trapezoidal centered quadratic moment is bounded by one.
+
+This is the first finite moment bound: the sampled centered quadratic profile
+is at most one on `[0,1]`, and the trapezoidal weights have total mass one.
+
+[TODO: finite-trapezoid-quadratic-closed-form] Prove the sharper closed form
+`1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2)` by an explicit finite
+quadratic-sum calculation.
+-/
+theorem dyadicPhaseTrapezoidCenteredQuadraticSum_le_one (n : ℕ) :
+    dyadicPhaseTrapezoidCenteredQuadraticSum n ≤ 1 := by
+  rw [dyadicPhaseTrapezoidCenteredQuadraticSum]
+  calc
+    ∑ k ∈ dyadicPhaseNodeIndices n,
+        dyadicPhaseTrapezoidWeight n k * dyadicPhaseCenteredQuadratic n k
+        ≤ ∑ k ∈ dyadicPhaseNodeIndices n,
+            dyadicPhaseTrapezoidWeight n k * 1 := by
+          exact Finset.sum_le_sum fun k hk => by
+            have hle :=
+              dyadicPhaseCenteredQuadratic_le_one (n := n) (k := k) hk
+            have hdiff :
+                0 ≤ dyadicPhaseTrapezoidWeight n k *
+                  (1 - dyadicPhaseCenteredQuadratic n k) :=
+              mul_nonneg (dyadicPhaseTrapezoidWeight_pos n k).le
+                (sub_nonneg.mpr hle)
+            nlinarith
+    _ = 1 := by
+      simpa using sum_dyadicPhaseTrapezoidWeight_eq_one n
+
 /--
 For centered log-depth, the plain mesh-width and trapezoidal sums differ by
 the restored endpoint correction `h_n * log 2`.
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 78934906..bcee85b7 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -275,7 +275,6 @@ centered log-depth sums are therefore nonnegative and bounded above by their
 corresponding finite centered quadratic moments. This is a finite estimate
 only: it prepares the next moment calculation, but it does not yet assert a
 closed form, a limiting integral, a Gaussian law, or a `pi` identification.
-endpoint increments expose the correction term.
 
 The first centered observable is now implemented. `centeredLogPhaseDepth`
 subtracts the midpoint baseline `log(1/2)` from `log(phaseDepth t)`. It
@@ -302,6 +301,23 @@ least `1`; the second is the `log(1 + x) <= x` comparison applied to
 `x = 4 * (t - 1/2)^2`. This creates the finite bridge from logarithmic
 correction accounting to quadratic moment estimates.
 
+The first finite quadratic moment bound is also implemented. On the unit
+interval, the centered quadratic profile satisfies
+
+```text
+4 * (t - 1/2)^2 <= 1.
+```
+
+Every complete dyadic node lies in that interval, and the trapezoidal weights
+have total mass one, so Lean proves
+
+```text
+dyadicPhaseTrapezoidCenteredQuadraticSum n <= 1.
+```
+
+This is deliberately a crude finite bound. The sharper expected closed form
+`1/3 + 2/(3 * (2^n)^2)` is marked in code as the next finite-sum target.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 2fb22a52..18fe6678 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -44,7 +44,9 @@ identified with `log (1 + 4 * (t - 1/2)^2)`, is pointwise nonnegative, and is
 bounded above by `4 * (t - 1/2)^2`. This pointwise estimate has been lifted to
 arbitrary nonnegative finite weights, with mesh-width, uniform-average, and
 trapezoidal corollaries. These are finite quadratic-moment controls only; no
-Gaussian, integral, angle, or `pi` interpretation is selected here.
+Gaussian, integral, angle, or `pi` interpretation is selected here. The first
+trapezoidal centered quadratic moment bound is now `<= 1`; the sharper closed
+finite formula is intentionally left as the next finite-sum target.
 
 The current implementation proves a four-state return:
 
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 41ea51a0..64e555b9 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1110,3 +1110,24 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 13:42 JST (Trapezoidal quadratic moment bound)
+
+1. correction:
+   - `research-pregeometric-pi-program-067.md` の centered endpoint
+     correction 周辺に残っていた stray sentence を整理した。
+2. API:
+   - unit interval 上で centered quadratic profile が `≤ 1` である
+     `centeredQuadratic_le_one_of_mem_unit` を追加した。
+   - complete dyadic node 上の対応する点wise bound
+     `dyadicPhaseCenteredQuadratic_le_one` を追加した。
+3. finite moment:
+   - 台形重みの total mass one と点wise bound から
+     `dyadicPhaseTrapezoidCenteredQuadraticSum_le_one` を証明した。
+   - 閉形式 `1/3 + 2/(3 * (2^n)^2)` は code TODO として残した。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
