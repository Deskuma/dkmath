# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: 980e47a10c3375a63a802dc7acc84a4f42b6d6d5

## Report

次の checkpoint まで進めました。

`SemanticCF2DLogComposition.lean` に、finite candidate observables として以下を追加しました。

- complete dyadic node mesh の cardinality lemma
- uniform average weight
- mesh-width weight
- average log depth / normalization
- mesh-weighted log depth / normalization
- average 版、mesh-weighted 版の finite log cancellation

重要な点として、これらはまだ canonical limit の選択ではなく、raw log-sum cancellation を有限スカラー重みへ移送しただけ、という扱いにしています。

文書も同期しました。

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
- [task-trig-continuous-phase-065.md](/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md)
- [research-pregeometric-pi-program-067.md](/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md)
- [History.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md)

検証済みです。

- `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition`
- `lake build DkMath.Analysis`
- `git diff --check`

## Review

うむ、これは良い checkpoint じゃ。
今回の差分は、`SemanticCF2DLogComposition` を **候補 observable の比較台** に進めたものじゃな。

報告では、complete dyadic node mesh の cardinality、uniform average weight、mesh-width weight、average log depth / normalization、mesh-weighted log depth / normalization、そして average 版・mesh-weighted 版の finite log cancellation が追加されている。さらに、これらは canonical limit の選択ではなく、raw log-sum cancellation を有限スカラー重みへ移しただけ、と明記されておる。

## 1. 総評

採用でよい。

今回の主な意味は、新しい極限定理を主張したことではない。
むしろ、有限 log cancellation を保ったまま、複数の観測候補を並べ始めたことじゃ。

前回までの raw log law はこれだった。

$$
2\cdot\mathrm{LogNormalizationSum}_n+\mathrm{LogDepthSum}_n=0
$$

今回、同じ恒等式を共通スカラーで重み付けしても消えることを定理化した。

uniform average では、

$$
2\cdot\mathrm{AverageLogNormalization}_n+\mathrm{AverageLogDepth}_n=0
$$

mesh-width weighted では、

$$
2\cdot\mathrm{WeightedLogNormalization}_n+\mathrm{WeightedLogDepth}_n=0
$$

つまり、有限段階での cancellation law は、raw sum、average、mesh-width weighting のどれにも輸送できる。
これは後の limit observable selection に向けた、良い地ならしじゃ。

## 2. 数学的な意味

ここで重要なのは、三種類の量の性格が違うことじゃ。

```text id="yk69k4"
raw log sum:
  complete mesh 上の全点寄与をそのまま足す。

uniform average:
  点数で割る。有限標本の平均観測。

mesh-width weighted:
  幅 1 / 2^n を掛ける。Riemann-sum 風の候補。
```

この違いは、\(\sqrt{\pi}\) へ向かう道ではかなり重要じゃ。

raw sum は点数が増えるほど増減が激しくなりうる。
uniform average は標本分布の平均値を見る。
mesh-width weighted は積分型の量に近づく可能性がある。

ただし、今回の docs が正しく言っている通り、どれもまだ canonical ではない。
単に「有限 cancellation law が同じ形で残る」ことを確認した段階じゃ。

## 3. 実装レビュー

`dyadicPhaseNodeIndices_card` は良い。

```lean id="vukb7q"
theorem dyadicPhaseNodeIndices_card (n : ℕ) :
    (dyadicPhaseNodeIndices n).card = dyadicPhaseDenom n + 1 := by
  simp [dyadicPhaseNodeIndices]
```

complete node mesh は \(0,1,\dots,2^n\) なので、点数は \(2^n+1\)。
これは midpoint / odd-child mesh との区別に効く。

average weight も素直じゃ。

```lean id="dsjgnq"
def dyadicPhaseAverageWeight (n : ℕ) : ℝ :=
  1 / ((dyadicPhaseNodeIndices n).card : ℝ)
```

正値性も、card が正であることから綺麗に出ている。

mesh weight もよい。

```lean id="gy5plj"
def dyadicPhaseMeshWeight (n : ℕ) : ℝ :=
  1 / (dyadicPhaseDenom n : ℝ)
```

こちらは subdivision width として自然じゃ。
ただし complete mesh は点数が \(2^n+1\) なので、単純に全点へ mesh weight を掛けると、総重みは \(1+1/2^n\) になる。ここは後で台形則や endpoint weighting を考える時に重要になる。

average cancellation と mesh-weighted cancellation の証明は、共通スカラーをくくって raw cancellation に戻す形で、非常に良い。

```lean id="c6jyjb"
= dyadicPhaseAverageWeight n *
    (2 * dyadicPhaseLogNormalizationSum n +
      dyadicPhaseLogDepthSum n)
```

この設計は明快じゃ。
「新しい cancellation を発見した」のではなく、「既存 cancellation を finite scalar transport した」と Lean の形にも表れている。

## 4. 研究テーマとの関係

これは \(\sqrt{\pi}\) へ向けたかなり重要な段階じゃ。

いまの研究テーマでは、円や角度を先に仮定せず、CF2D の affine transition と normalization から独立な normalization constant を作り、あとで `Real.pi` と比較する。
そのためには、どの有限観測量を極限対象にするかを選ばねばならぬ。

今回、その候補が明示的に増えた。

```text id="b0ofsh"
候補 1:
  raw log sum

候補 2:
  uniform average log sum

候補 3:
  mesh-width weighted log sum
```

これは良い。
候補を定義して、同じ finite cancellation law がどう輸送されるかを見る。
その後で、どれが Gaussian weight に近づくかを選ぶ。順番が正しい。

## 5. 注意点

大きな問題はない。
ただし、次の点はかなり重要じゃ。

### 5.1. mesh-width weighted complete sum はまだ積分近似として不完全

complete mesh の全点に同じ \(1/2^n\) を掛けると、端点を二重気味に扱う。

通常の台形則なら、端点は半重みになる。

```text id="jqh2z4"
k = 0 と k = 2^n:
  weight = 1 / (2 * 2^n)

interior:
  weight = 1 / 2^n
```

なので、mesh-width weighted sum は「Riemann-style candidate」ではあるが、標準的な閉区間積分近似としてはまだ未選択の候補じゃ。
docs で endpoint weights を deliberate に選んでいないと書いているのは正しい判断じゃな。

### 5.2. average と mesh-weighted は極限で違うものを見る

uniform average は、おそらく区間上の平均値に向かう候補になる。
mesh-weighted sum は、積分値に向かう候補になる。

区間長が \(1\) なら近いが、complete mesh の端点処理で微妙に差が出る。
さらに将来、中心化やスケール変換を入れるなら、この差はもっと大きくなる。

だから、今の段階で両方を並べたのは良い。

### 5.3. Gaussian へ行くなら baseline subtraction が必要そう

`phaseDepth` は中心で最小値 \(1/2\) を持つ。

$$
\mathrm{phaseDepth}(t)=\frac{1}{2}+2\left(t-\frac{1}{2}\right)^2
$$

log depth には定数項がある。

$$
\log(\mathrm{phaseDepth}(t))
=\log\left(\frac{1}{2}\right)+\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

Gaussian 型を見るなら、この定数項をどう扱うかが重要になる。
単純な log sum では、定数項が点数分だけ積み上がる。
つまり次は、center baseline を引いた renormalized log observable が必要になる可能性が高い。

候補としては、こうじゃ。

$$
\log(\mathrm{phaseDepth}(t))-\log\left(\frac{1}{2}\right)
$$

または normalization 側なら、

$$
\log(\mathrm{phaseNormalization}(t))-\log(\sqrt{2})
$$

この「中心基準からの増分」を見ると、二次型が取り出しやすくなる。

## 6. 次に足すと強い定義

次は候補 observable の比較台をさらに増やすとよい。

### 6.1. trapezoidal log sums

台形則型。

```lean id="fe2inn"
def dyadicPhaseTrapezoidWeight (n k : ℕ) : ℝ := ...
```

端点だけ半重み、内部は mesh weight。
これは積分候補としてかなり自然じゃ。

### 6.2. midpoint / odd-child log sums

defect は odd child midpoint に出ていた。
ならば complete node mesh ではなく、midpoint mesh の log observable も必要じゃ。

```text id="uqg604"
complete node mesh:
  境界復元の観測点

midpoint / odd-child mesh:
  refinement defect の発生点
```

この二つを比べるのが大事じゃな。

### 6.3. centered log-depth increment

Gaussian へ行くならこれが本命候補に近い。

$$
\Delta\log\mathrm{depth}(t)
=\log(\mathrm{phaseDepth}(t))-\log\left(\frac{1}{2}\right)
$$

中心付近では、これは二次型を持つ。

$$
\Delta\log\mathrm{depth}(t)=\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

小さい \(s=t-1/2\) では、

$$
\log(1+4s^2)\approx 4s^2
$$

ここから Gaussian の指数核へつながる可能性がある。

## 7. Lean 的な改善候補

現状は十分良い。
ただし、同じ pattern が増え始めているので、次に候補 observable が増えるなら、共通 lemma があると楽じゃ。

例えば、

```lean id="d5uo1b"
theorem scalar_transport_log_cancellation
    (n : ℕ) (w : ℝ) :
    2 * (w * dyadicPhaseLogNormalizationSum n) +
        (w * dyadicPhaseLogDepthSum n) = 0 := by
  ...
```

これを作ると、average 版も mesh-weighted 版も一行で出せる。
今の実装でも全く問題はないが、trapezoidal や midpoint に進むと、汎用化したくなるかもしれぬ。

ただし、weighted sum が点ごとに異なる重みになると、この scalar lemma では足りない。
その場合は、

```lean id="tao4gm"
∑ k, w k * (2 * logNorm k + logDepth k) = 0
```

型の pointwise weighted cancellation が本命になる。

## 8. 結論

今回の差分は採用でよい。

```text id="qdr8ty"
実装:
  良い。finite log-sum から candidate observables へ自然に拡張している。

数学:
  良い。raw / average / mesh-weighted の区別が明確。

研究位置:
  重要。canonical refinement-limit observable を選ぶ前の比較面ができた。

安全性:
  良い。Gaussian、π、canonical limit はまだ主張していない。

次:
  trapezoidal、midpoint / odd-child、centered log increment、
  そして pointwise weighted cancellation の一般 lemma。
```

ぬしよ、これはよい進め方じゃ。
\(\sqrt{\pi}\) へ急がず、まず「どの有限観測量なら極限で意味を持つか」を並べている。

これは地味に見えて、かなり大事じゃ。
円を描く前に、測る物差しを選んでいる段階じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 447d8bf9..97998e3e 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -136,8 +136,10 @@ algebra.
 `DkReal.SemanticCF2DLogComposition` transfers the positive finite
 cancellation law to logarithmic sums. Each log sum is identified with the
 logarithm of its finite product, and
-`2 * logNormalizationSum + logDepthSum = 0`. No logarithmic quantity is yet
-selected as the canonical refinement-limit observable.
+`2 * logNormalizationSum + logDepthSum = 0`. Uniform-average and mesh-width
+weighted variants are exposed as finite candidate observables, and the same
+cancellation law is proved for them. No logarithmic quantity is yet selected
+as the canonical refinement-limit observable.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index c7ab945d..10681be0 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -20,7 +20,9 @@ The resulting identity
 
 is exactly equivalent to the previously proved finite product cancellation.
 This module still does not select a logarithmic sum as the canonical
-refinement-limit observable.
+refinement-limit observable. The average and mesh-weighted variants below are
+therefore recorded only as finite candidate observables: the same cancellation
+law survives scalar reweighting, but no limiting interpretation is chosen here.
 -/
 
 namespace DkMath.Analysis.DkNNRealQ
@@ -86,6 +88,107 @@ theorem two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum
   exact Finset.sum_eq_zero fun k hk =>
     two_mul_log_dyadicPhaseNormalization_add_log_depth n k
 
+/--
+The complete dyadic mesh has one more node than its dyadic denominator.
+
+This is the finite bookkeeping distinction between complete node meshes and
+midpoint or odd-child meshes.
+-/
+theorem dyadicPhaseNodeIndices_card (n : ℕ) :
+    (dyadicPhaseNodeIndices n).card = dyadicPhaseDenom n + 1 := by
+  simp [dyadicPhaseNodeIndices]
+
+/--
+Uniform average weight on the complete finite dyadic node mesh.
+
+This is a finite candidate observable. It does not assert that the uniform
+average is the canonical refinement-limit quantity.
+-/
+def dyadicPhaseAverageWeight (n : ℕ) : ℝ :=
+  1 / ((dyadicPhaseNodeIndices n).card : ℝ)
+
+/-- The complete finite dyadic mesh has a positive averaging weight. -/
+theorem dyadicPhaseAverageWeight_pos (n : ℕ) :
+    0 < dyadicPhaseAverageWeight n := by
+  have hcard : 0 < (dyadicPhaseNodeIndices n).card := by
+    rw [dyadicPhaseNodeIndices_card]
+    exact Nat.succ_pos _
+  exact one_div_pos.2 (by exact_mod_cast hcard)
+
+/-- Uniform average of logarithmic depth observations on the complete mesh. -/
+def dyadicPhaseAverageLogDepth (n : ℕ) : ℝ :=
+  dyadicPhaseAverageWeight n * dyadicPhaseLogDepthSum n
+
+/--
+Uniform average of logarithmic normalization observations on the complete
+mesh.
+-/
+def dyadicPhaseAverageLogNormalization (n : ℕ) : ℝ :=
+  dyadicPhaseAverageWeight n * dyadicPhaseLogNormalizationSum n
+
+/-- Finite logarithmic cancellation survives uniform averaging. -/
+theorem two_mul_dyadicPhaseAverageLogNormalization_add_averageLogDepth
+    (n : ℕ) :
+    2 * dyadicPhaseAverageLogNormalization n +
+        dyadicPhaseAverageLogDepth n = 0 := by
+  calc
+    2 * dyadicPhaseAverageLogNormalization n +
+        dyadicPhaseAverageLogDepth n
+        = dyadicPhaseAverageWeight n *
+            (2 * dyadicPhaseLogNormalizationSum n +
+              dyadicPhaseLogDepthSum n) := by
+          rw [dyadicPhaseAverageLogNormalization,
+            dyadicPhaseAverageLogDepth]
+          ring
+    _ = 0 := by
+      rw [two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum]
+      simp
+
+/--
+Mesh width of the dyadic subdivision.
+
+This is the natural scalar for finite Riemann-style candidates on the complete
+node mesh. Endpoint weights are deliberately not chosen here.
+-/
+def dyadicPhaseMeshWeight (n : ℕ) : ℝ :=
+  1 / (dyadicPhaseDenom n : ℝ)
+
+/-- The dyadic mesh width is positive. -/
+theorem dyadicPhaseMeshWeight_pos (n : ℕ) :
+    0 < dyadicPhaseMeshWeight n := by
+  exact one_div_pos.2 (by exact_mod_cast dyadicPhaseDenom_pos n)
+
+/-- Mesh-weighted finite log-depth sum. -/
+def dyadicPhaseWeightedLogDepthSum (n : ℕ) : ℝ :=
+  dyadicPhaseMeshWeight n * dyadicPhaseLogDepthSum n
+
+/-- Mesh-weighted finite log-normalization sum. -/
+def dyadicPhaseWeightedLogNormalizationSum (n : ℕ) : ℝ :=
+  dyadicPhaseMeshWeight n * dyadicPhaseLogNormalizationSum n
+
+/--
+Finite logarithmic cancellation survives mesh-width weighting.
+
+This is only a finite scalar transport of the log-sum identity; it does not
+assert that the mesh-weighted quantity is the canonical limit observable.
+-/
+theorem two_mul_dyadicPhaseWeightedLogNormalizationSum_add_weightedLogDepthSum
+    (n : ℕ) :
+    2 * dyadicPhaseWeightedLogNormalizationSum n +
+        dyadicPhaseWeightedLogDepthSum n = 0 := by
+  calc
+    2 * dyadicPhaseWeightedLogNormalizationSum n +
+        dyadicPhaseWeightedLogDepthSum n
+        = dyadicPhaseMeshWeight n *
+            (2 * dyadicPhaseLogNormalizationSum n +
+              dyadicPhaseLogDepthSum n) := by
+          rw [dyadicPhaseWeightedLogNormalizationSum,
+            dyadicPhaseWeightedLogDepthSum]
+          ring
+    _ = 0 := by
+      rw [two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum]
+      simp
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index fcce9113..ced68f27 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -208,6 +208,14 @@ products. This equivalence supplies a comparison surface for later limit
 selection; it does not select the raw sum, an average, or a weighted sum as
 canonical.
 
+The same module also records two scalar reweightings as finite candidate
+observables. The uniform average divides by the number of complete-mesh nodes,
+and the mesh-width version multiplies by `1 / 2^n`. In both cases, the
+logarithmic cancellation law is transported exactly. These are not yet
+canonical limit choices; they only make the candidate comparison surface
+explicit before trapezoidal, midpoint, or other weighted observables are
+tested.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 4df85cc8..4d444145 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -385,10 +385,13 @@ both reciprocal forms.
 [IMPLEMENTED: semantic-cf2d-phase/finite-log-composition] Positivity permits
 the same finite law to be expressed as logarithmic sums:
 `2 * logNormalizationSum + logDepthSum = 0`. Each sum is also proved equal
-to the logarithm of its corresponding finite product.
+to the logarithm of its corresponding finite product. Uniform-average and
+mesh-width weighted log sums are now recorded as finite candidate observables,
+with the same cancellation law transported by scalar multiplication.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
-finite product, logarithmic sum, or another quantity has a canonical
-refinement limit. The finite cancellation theorem alone does not select one.
+finite product, raw logarithmic sum, average, mesh-weighted sum, trapezoidal
+sum, midpoint sum, or another quantity has a canonical refinement limit. The
+finite cancellation theorem alone does not select one.
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
 ```
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 75a91eb2..848f6ad4 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -918,3 +918,25 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 06:01 JST (Finite logarithmic candidate observables)
+
+1. API:
+   - complete dyadic node mesh の cardinality lemma
+     `dyadicPhaseNodeIndices_card` を追加した。
+   - uniform-average weight と mesh-width weight を定義した。
+   - average / mesh-weighted log depth と log normalization の finite
+     candidate observables を追加した。
+2. finite laws:
+   - raw log-sum cancellation を scalar multiplication で移送し、
+     average 版と mesh-weighted 版の cancellation を証明した。
+3. boundary:
+   - 追加した量はいずれも finite candidate observable に留めた。
+     canonical limit、Gaussian weight、`pi` identification はまだ選択して
+     いない。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
