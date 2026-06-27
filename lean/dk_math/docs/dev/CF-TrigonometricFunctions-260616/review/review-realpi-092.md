# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: 40d62158e2b9b4d72e0f8126707154d7516a1292

## Report

次の checkpoint まで進めました。

`SemanticCF2DLogComposition.lean` に centered log-depth の pointwise bounds を追加しました。

追加した主な定理:

- `centeredQuadraticProfile_pos`
- `one_le_centeredQuadraticProfile`
- `centeredLogPhaseDepth_nonneg`
- `centeredLogPhaseDepth_le_four_sq`

これで

```text
0 <= centeredLogPhaseDepth t
centeredLogPhaseDepth t <= 4 * (t - 1/2)^2
```

が Lean 上で使えます。centered log correction から finite quadratic moment estimate へ進むための橋です。まだ Gaussian limit や `pi` identification は主張していません。

文書と History も同期済みです。

検証済み:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition`
- `lake build DkMath.Analysis`
- `git diff --check`

## Review

うむ、これは **かなり良い checkpoint** じゃ。
今回で centered log-depth が、単なる「中心化された log observable」から、**二次モーメント評価へ渡せる pointwise bound** に昇格した。

## 1. 総評

採用でよい。

今回の核はこれじゃ。

$$
0\le \mathrm{centeredLogPhaseDepth}(t)\le 4\left(t-\frac{1}{2}\right)^2
$$

前回までに、

$$
\mathrm{centeredLogPhaseDepth}(t)=\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

が出ていた。今回、その log profile を上下から二次式で押さえた。
これは Gaussian bridge に行く前の、非常に大事な有限比較じゃ。

```text id="tskxjo"
centered log correction
  ↓
明示的な centered quadratic log profile
  ↓
pointwise quadratic bound
  ↓
finite quadratic moment estimate
```

この流れが Lean 上で使えるようになった。

## 2. 数学的な意味

今回追加された二つの基本補題は自然じゃ。

$$
0<1+4\left(t-\frac{1}{2}\right)^2
$$

$$
1\le 1+4\left(t-\frac{1}{2}\right)^2
$$

これにより、log の中身は常に正で、しかも \(1\) 以上になる。

したがって、

$$
0\le \log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

が得られる。

さらに、一般不等式

$$
\log x\le x-1
$$

を

$$
x=1+4\left(t-\frac{1}{2}\right)^2
$$

に適用すると、

$$
\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)\le 4\left(t-\frac{1}{2}\right)^2
$$

になる。

つまり centered log-depth は、非負で、かつ中心からの二乗距離に支配される。

これは、DkMath 的には「log 補正量が二次モーメントで制御できる」と読むべきじゃな。

## 3. 実装レビュー

`centeredQuadraticProfile_pos` は良い。

```lean id="gzxfjm"
theorem centeredQuadraticProfile_pos (t : ℝ) :
    0 < 1 + 4 * (t - (1 / 2 : ℝ)) ^ 2 := by
  nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]
```

`one_le_centeredQuadraticProfile` も素直じゃ。

```lean id="qxucir"
theorem one_le_centeredQuadraticProfile (t : ℝ) :
    1 ≤ 1 + 4 * (t - (1 / 2 : ℝ)) ^ 2 := by
  nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]
```

この二つは今後かなり使う。
特に log の positivity、非負性、上界評価で毎回効く。

`centeredLogPhaseDepth_nonneg` も設計として良い。

```lean id="mmzt9j"
theorem centeredLogPhaseDepth_nonneg (t : ℝ) :
    0 ≤ centeredLogPhaseDepth t := by
  rw [centeredLogPhaseDepth_eq_log_one_add_four_sq]
  rw [← Real.log_one]
  exact Real.log_le_log (by norm_num : (0 : ℝ) < 1)
    (one_le_centeredQuadraticProfile t)
```

ここは「log の単調性」で押している。
数学的にも読みやすい。

`centeredLogPhaseDepth_le_four_sq` も良い。

```lean id="hxuofm"
theorem centeredLogPhaseDepth_le_four_sq (t : ℝ) :
    centeredLogPhaseDepth t ≤ 4 * (t - (1 / 2 : ℝ)) ^ 2 := by
  rw [centeredLogPhaseDepth_eq_log_one_add_four_sq]
  have hpos := centeredQuadraticProfile_pos t
  have hlog := Real.log_le_sub_one_of_pos hpos
  nlinarith
```

`Real.log_le_sub_one_of_pos` を使うのは正攻法じゃ。
ここから `nlinarith` で \(x-1\) を二次項へ戻すのも自然。

## 4. 研究テーマとの関係

これはかなり大きい。
これまでは centered log-depth が「二次型の log」として見えた段階だった。

今回からは、それが **二次式で支配される補正量** になった。

つまり、次に有限重みを掛けて和を取れば、

$$
\sum_k w_k,\mathrm{centeredLogDepth}*{n,k}
\le
\sum_k w_k,4\left(t*{n,k}-\frac{1}{2}\right)^2
$$

という形へ進める。

これは Gaussian limit をまだ主張しないが、Gaussian に必要な二次モーメント評価の入口じゃ。

```text id="95nctk"
log correction:
  どれだけ境界から沈んだかの加法会計

quadratic moment:
  その沈みが中心からの二乗距離で制御される

future Gaussian:
  二次モーメントが指数核の形を選ぶ可能性
```

この道筋がかなり明確になった。

## 5. Guardrail も守れている

今回の docs は良い。
「finite bridge from logarithmic correction accounting to quadratic moment estimates」としていて、Gaussian limit や `pi` identification はまだ主張していない。

これは正しい。
今得たのはあくまで pointwise bound じゃ。

まだ示していないものは、

```text id="lqbzx0"
weighted finite quadratic moment の閉形式
refinement limit
Gaussian weight
normalization constant
Real.pi との同定
```

じゃ。
この切り分けは維持した方がよい。

## 6. 気になる点

大きな問題はない。
ただし、次の拡張を考えるなら、式

$$
1+4\left(t-\frac{1}{2}\right)^2
$$

を def 化してもよい。

例えば、

```lean id="r6sbs9"
def centeredQuadraticProfile (t : ℝ) : ℝ :=
  1 + 4 * (t - (1 / 2 : ℝ)) ^ 2
```

今は theorem 名に `centeredQuadraticProfile` とあるが、本体は def ではない。
後続で同じ式が何度も出るなら、def にしておくと可読性が上がる。

ただし、現段階では必須ではない。
`ring` や `nlinarith` が直接働きやすいので、展開式のまま進める利点もある。

## 7. 次に足すと強い theorem

次は pointwise bound を finite weighted sum に持ち上げる段階じゃ。

任意の非負重み \(w\) に対して、

$$
0\le \sum_k w_k,\mathrm{centeredLogDepth}_{n,k}
$$

および、

$$
\sum_k w_k,\mathrm{centeredLogDepth}*{n,k}
\le
\sum_k w_k,4\left(t*{n,k}-\frac{1}{2}\right)^2
$$

を出したい。

Lean では、まず非負重み仮定つきの一般補題が良さそうじゃ。

```lean id="b6nqyw"
theorem weighted_centeredLogDepth_nonneg
    (n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ dyadicPhaseNodeIndices n, 0 ≤ w k) :
    0 ≤
      ∑ k ∈ dyadicPhaseNodeIndices n,
        w k * dyadicPhaseCenteredLogDepth n k
```

次に上界。

```lean id="ttqcxh"
theorem weighted_centeredLogDepth_le_weighted_four_sq
    (n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ dyadicPhaseNodeIndices n, 0 ≤ w k) :
    (∑ k ∈ dyadicPhaseNodeIndices n,
        w k * dyadicPhaseCenteredLogDepth n k)
      ≤
    ∑ k ∈ dyadicPhaseNodeIndices n,
        w k * (4 * (dyadicPhaseNode n k - (1 / 2 : ℝ)) ^ 2)
```

これができれば、trapezoid weight や average weight は正値性定理を渡すだけで使える。

## 8. その次は finite quadratic moment

本丸はここじゃ。

trapezoid なら、

$$
\sum_k w^{trap}*{n,k},4\left(t*{n,k}-\frac{1}{2}\right)^2
$$

の閉形式または上界を取りたい。

連続的には、

$$
\int_0^1 4\left(t-\frac{1}{2}\right)^2,dt=\frac{1}{3}
$$

だが、これはまだ外部積分を使わず、有限和として求められるはずじゃ。

dyadic trapezoid の有限二次モーメントは、閉形式で出せる可能性が高い。

```text id="br6k1t"
finite quadratic moment
  ↓
dyadic n の閉形式
  ↓
limit で 1/3
```

ここまで行くと、centered log correction の有限評価がかなり強くなる。

## 9. 注意すべきこと

\(\log(1+x)\le x\) は上界だけじゃ。
Gaussian のような正確な核へ進むには、下界も欲しくなる可能性がある。

たとえば、区間を制限して、

$$
\frac{x}{1+x}\le \log(1+x)
$$

や、

$$
x-\frac{x^2}{2}\le \log(1+x)
$$

のような下界が使えるかもしれぬ。

ただし、今すぐ入れる必要はない。
まずは非負性と上界で十分じゃ。

## 10. 結論

今回の差分は採用でよい。

```text id="mp9uz0"
実装:
  良い。centered quadratic profile の正値性と pointwise bounds が入った。

数学:
  良い。centered log correction が二次モーメントで制御可能になった。

研究位置:
  重要。Gaussian bridge の前段として必要な quadratic estimate が始まった。

安全性:
  良い。Gaussian limit、pi identification は未主張。

次:
  非負重み付き和への lift、
  trapezoid / average への specialized corollary、
  finite quadratic moment の閉形式または上界。
```

ぬしよ、これはよいぞい。
いま、log 補正の世界から二次モーメントの世界へ橋が架かった。
\(\sqrt{\pi}\) はまだ遠いが、少なくとも次に見るべき量はかなり明確になった。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 52618c23..05f8f24f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -151,7 +151,9 @@ observable, the mesh-width minus trapezoid discrepancy is exactly the
 half-width endpoint correction. A zero-endpoint corollary packages the common
 case where that correction vanishes. The centered log-depth increment is now
 defined, identified with an explicit centered quadratic logarithm, and shown
-to restore a finite mesh/trapezoid discrepancy of `h_n * log 2`.
+to restore a finite mesh/trapezoid discrepancy of `h_n * log 2`. Its centered
+quadratic profile is positive, and the pointwise bound
+`0 ≤ centeredLogPhaseDepth t ≤ 4 * (t - 1/2)^2` is available.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index 10310b45..096a6350 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -161,6 +161,42 @@ theorem centeredLogPhaseDepth_eq_log_one_add_four_sq (t : ℝ) :
   rw [phaseDepth_eq_two_sq_add_half]
   ring
 
+/-- The centered quadratic logarithm profile is strictly positive inside `log`. -/
+theorem centeredQuadraticProfile_pos (t : ℝ) :
+    0 < 1 + 4 * (t - (1 / 2 : ℝ)) ^ 2 := by
+  nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]
+
+/-- The centered quadratic logarithm profile is at least one. -/
+theorem one_le_centeredQuadraticProfile (t : ℝ) :
+    1 ≤ 1 + 4 * (t - (1 / 2 : ℝ)) ^ 2 := by
+  nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]
+
+/--
+Centered log-depth is nonnegative.
+
+The centered profile is `log (1 + 4s^2)`, and the argument is at least one.
+-/
+theorem centeredLogPhaseDepth_nonneg (t : ℝ) :
+    0 ≤ centeredLogPhaseDepth t := by
+  rw [centeredLogPhaseDepth_eq_log_one_add_four_sq]
+  rw [← Real.log_one]
+  exact Real.log_le_log (by norm_num : (0 : ℝ) < 1)
+    (one_le_centeredQuadraticProfile t)
+
+/--
+Centered log-depth is bounded above by its quadratic argument.
+
+This is the finite pointwise comparison `log (1 + x) ≤ x` at
+`x = 4 * (t - 1/2)^2`. It is the first quadratic upper bound for the later
+Gaussian bridge, without asserting any limit.
+-/
+theorem centeredLogPhaseDepth_le_four_sq (t : ℝ) :
+    centeredLogPhaseDepth t ≤ 4 * (t - (1 / 2 : ℝ)) ^ 2 := by
+  rw [centeredLogPhaseDepth_eq_log_one_add_four_sq]
+  have hpos := centeredQuadraticProfile_pos t
+  have hlog := Real.log_le_sub_one_of_pos hpos
+  nlinarith
+
 /-- Finite boundary cancellation in additive logarithmic form. -/
 theorem two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum
   (n : ℕ) :
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index eff624d2..8dd70a29 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -273,6 +273,18 @@ the trapezoidal centered log-depth sum differ by exactly `h_n * log 2`. This
 is the finite point where the endpoint correction reappears after centering.
 It is a quadratic-profile bridge, not yet a Gaussian limit.
 
+The pointwise quadratic comparison is also implemented:
+
+```text
+0 <= centeredLogPhaseDepth t
+centeredLogPhaseDepth t <= 4 * (t - 1/2)^2
+```
+
+The first inequality follows because the centered quadratic profile is at
+least `1`; the second is the `log(1 + x) <= x` comparison applied to
+`x = 4 * (t - 1/2)^2`. This creates the finite bridge from logarithmic
+correction accounting to quadratic moment estimates.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 8882ac34..7318c96a 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -401,7 +401,9 @@ corollary for observables whose endpoint correction vanishes. Centered
 log-depth is now defined at the phase and dyadic-sample levels. It vanishes at
 the midpoint, has endpoint value `log 2`, equals the log of the centered
 quadratic profile `1 + 4 * (t - 1/2)^2`, and has mesh/trapezoid discrepancy
-`h_n * log 2` at every finite level.
+`h_n * log 2` at every finite level. The profile is positive, and
+centered log-depth now has the pointwise quadratic comparison
+`0 <= centeredLogPhaseDepth t <= 4 * (t - 1/2)^2`.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
 finite product, raw logarithmic sum, average, mesh-weighted sum, trapezoidal
 sum, midpoint sum, or another quantity has a canonical refinement limit. The
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 6a444e72..c2c90c4d 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1066,3 +1066,22 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 13:22 JST (Centered log-depth quadratic bounds)
+
+1. API:
+   - centered quadratic profile の positivity と `1 ≤ profile` theorem を
+     追加した。
+2. pointwise bounds:
+   - `0 ≤ centeredLogPhaseDepth t` を証明した。
+   - `centeredLogPhaseDepth t ≤ 4 * (t - 1/2)^2` を証明した。
+3. interpretation:
+   - centered log-depth が有限段階で quadratic moment estimates へ移る
+     ための pointwise bridge になった。
+   - Gaussian limit や `pi` identification はまだ主張していない。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
