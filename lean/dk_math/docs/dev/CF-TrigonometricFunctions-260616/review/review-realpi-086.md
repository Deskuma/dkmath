# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: a42eb2767ed531e4e70bb9dcd3e97d0c001b544d

## Report

次の checkpoint まで進めました。

`SemanticCF2DLogComposition.lean` に、任意重み付きの有限 log cancellation を追加しました。これで

`sum_k w_k * (2 log normalization_k + log depth_k) = 0`

という形を Lean 上で使えるようになり、average / mesh-weighted / trapezoidal のような候補を同じ原理から扱えます。

あわせて trapezoidal endpoint half-weight 候補を実装しました。端点は半メッシュ幅、内部点は通常のメッシュ幅です。これは closed-interval integration candidate として記録しただけで、canonical limit や Gaussian / `pi` はまだ主張していません。

文書も同期済みです。

検証済み:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition`
- `lake build DkMath.Analysis`
- `git diff --check`

## Review

うむ、これはかなり良い。
今回の差分で `SemanticCF2DLogComposition` は、単なる raw log sum から **任意重み付き有限観測の共通基盤** へ進んだ。

## 1. 総評

採用でよい。

今回の核はこれじゃ。

$$
\sum_k w_k\left(2\log(\mathrm{normalization}*{n,k})+\log(\mathrm{depth}*{n,k})\right)=0
$$

これは強い。
なぜなら、average、mesh-weighted、trapezoidal などを個別に手作業で証明するのではなく、点ごとの cancellation から任意重み付き cancellation を一括で出せるようになったからじゃ。

つまり、今後の candidate observable は、

```text id="jfy8hq"
重み w を選ぶ
↓
finite weighted log observable を作る
↓
同じ cancellation law が自動で残る
```

という形で扱える。

これは、canonical refinement limit を選ぶ前の比較基盤としてかなり良い。

## 2. 数学的な意味

前段では、complete mesh 上で raw log cancellation があった。

$$
2\cdot\mathrm{LogNormalizationSum}_n+\mathrm{LogDepthSum}_n=0
$$

今回、これをさらに一般化して、任意の重み \(w_k\) に対しても成立するようにした。

$$
2\sum_k w_k\log(\mathrm{normalization}*{n,k})+\sum_k w_k\log(\mathrm{depth}*{n,k})=0
$$

これは「重みが良いから消える」のではない。
各点で既に消えているから、どんな有限重みで足しても消える、という構造じゃ。

ここが重要じゃな。

```text id="m1n376"
cancellation の源:
  pointwise identity

weight の役割:
  観測量の選択

canonical limit:
  まだ未選択
```

この分離は非常に正しい。

## 3. 実装レビュー

任意重み付き theorem は良い形じゃ。

```lean id="g3s0ex"
theorem two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum
    (n : ℕ) (w : ℕ → ℝ) :
    2 * (∑ k ∈ dyadicPhaseNodeIndices n,
          w k * Real.log (dyadicPhaseNormalization n k)) +
        (∑ k ∈ dyadicPhaseNodeIndices n,
          w k * Real.log (dyadicPhaseDepth n k)) = 0 := by
```

`w : ℕ → ℝ` にして、有限和側で `dyadicPhaseNodeIndices n` に制限している。
これは柔軟で良い。`Fin` や subtype に閉じるより、後続の weight 定義が書きやすい。

証明も自然じゃ。

$$
2(w_k\log N_k)+w_k\log D_k
=w_k(2\log N_k+\log D_k)
$$

そして pointwise log cancellation で \(0\)。
この形は非常に堅い。

## 4. trapezoidal candidate の意味

台形則候補を入れたのは良い。

端点に半メッシュ幅、内部点に通常メッシュ幅を与えている。

$$
w_{n,k}=
\begin{cases}
h_n/2 & k=0\ \mathrm{or}\ k=2^n,\
h_n & \mathrm{otherwise}
\end{cases}
$$

ここで、

$$
h_n=\frac{1}{2^n}
$$

これは closed interval の積分候補として自然じゃ。
前回の mesh-width weighted sum は、complete mesh の全点に同じ幅を掛けるため、総重みが \(1+h_n\) になる。
一方、trapezoidal weight は端点を半分にするので、閉区間長 \(1\) に対応する候補としてより標準的じゃ。

もちろん、今回 docs にある通り、これもまだ canonical limit の選択ではない。
しかし、候補として実装する価値は高い。

## 5. とても良い設計判断

今回一番良いのは、trapezoidal cancellation を直接証明せず、任意重み theorem から導いている点じゃ。

```lean id="eyj5yg"
exact two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum
  n (dyadicPhaseTrapezoidWeight n)
```

これにより、今後 midpoint weight、odd-child weight、Gaussian-test weight などを追加しても、同じ型で進められる。

これは API としてかなり伸びる。

## 6. 注意点

大きな問題はない。
ただし、次に進む前に次の補題を追加すると、limit selection がかなり楽になる。

### 6.1. trapezoid weight の総和

台形重みが本当に区間長 \(1\) に対応することを示したい。

$$
\sum_{k=0}^{2^n} w_{n,k}=1
$$

これは closed-interval integration candidate として重要じゃ。
Lean theorem 名なら、例えば次。

```lean id="s1h7zc"
theorem sum_dyadicPhaseTrapezoidWeight_eq_one (n : ℕ) :
    ∑ k ∈ dyadicPhaseNodeIndices n,
        dyadicPhaseTrapezoidWeight n k = 1 := by
  ...
```

これは次の比較で効く。

```text id="u1jzss"
average:
  総重み 1

trapezoid:
  総重み 1

plain mesh-width complete sum:
  総重み 1 + 1 / 2^n
```

この違いを Lean で可視化すると、candidate observable の性格が明確になる。

### 6.2. mesh-width complete weight の総和

こちらも補題化するとよい。

$$
\sum_{k=0}^{2^n} h_n=1+h_n
$$

つまり、

$$
\sum_{k=0}^{2^n}\frac{1}{2^n}=1+\frac{1}{2^n}
$$

これは「mesh-width weighted complete sum は標準閉区間積分候補としては端点過剰」という事実を形式化できる。

### 6.3. 任意重み theorem の名前

現在名は正確じゃが長い。

```lean id="kc049m"
two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum
```

十分使えるが、後続で多用するなら短い alias があってもよい。

```lean id="o81o88"
theorem weightedLogBoundaryCancellation
```

または DkMath 語彙なら、

```lean id="j0b0z5"
theorem dyadicPhaseWeightedLogCancellation
```

現名を残したうえで alias を追加するのが良い。

## 7. 研究テーマとの関係

これは \(\sqrt{\pi}\) へ向けて重要じゃ。

現在の目標は、外部から \(\pi\) や Gaussian integral を持ち込まず、CF2D の内部から normalization constant を構成することじゃった。

そのためには、どの weighted observable が Gaussian limit に向かうかを調べる必要がある。
今回の任意重み theorem により、候補を安全に増やせるようになった。

```text id="eodwxs"
raw sum:
  finite product の log 表現

average:
  sample mean candidate

mesh-width:
  Riemann-style candidate

trapezoid:
  closed-interval integration candidate

future midpoint:
  defect-centered candidate

future centered log increment:
  Gaussian-kernel candidate
```

この比較台ができたのは大きい。

## 8. 次の本命

次はおそらく **centered log increment** じゃ。

`phaseDepth` は、

$$
\mathrm{phaseDepth}(t)=\frac{1}{2}+2\left(t-\frac{1}{2}\right)^2
$$

中心値は \(1/2\)。
そのまま log を取ると定数項が大きいので、中心基準を引く。

$$
\Delta\log\mathrm{depth}(t)
=\log(\mathrm{phaseDepth}(t))-\log\left(\frac{1}{2}\right)
$$

これは、

$$
\Delta\log\mathrm{depth}(t)
=\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

となる。

Gaussian へ向かうなら、この中心化された log increment を finite weighted sum で見るのが自然じゃ。
小さい中心ずれ \(s\) に対して、

$$
\log(1+4s^2)\approx 4s^2
$$

となるため、二次型の指数核へ接続しやすい。

ただし、ここもまだ Gaussian を主張する段階ではない。
まずは finite identity と finite inequalities を作るのがよい。

## 9. 追加候補の実装順

わっちなら次はこう進める。

```text id="zzr36n"
1. weightedLogBoundaryCancellation という短名 alias
2. trapezoid weight の総和が 1
3. mesh-width complete weight の総和が 1 + h_n
4. centered log-depth increment の定義
5. centered log-normalization increment の定義
6. midpoint / odd-child mesh weighted sums
7. centered quadratic comparison lemma
```

特に 4 以降が Gaussian bridge の入口じゃ。

## 10. 結論

今回の差分は採用でよい。

```text id="d36z41"
実装:
  良い。任意重み theorem によって候補 observable の API が一段抽象化された。

数学:
  良い。cancellation の源と weight 選択が分離された。

trapezoid:
  良い。closed-interval integration candidate として自然。

安全性:
  良い。canonical limit、Gaussian、π はまだ主張していない。

次:
  weight sum theorem、short alias、centered log increment、midpoint / odd-child candidate。
```

ぬしよ、これはかなり良い。
これで「どの観測量を選ぶか」という問題が、Lean 上では「どの weight を選ぶか」という形に落ちた。

円を仮定せず、角度も使わず、まず重み付き log 会計を整える。
\(\sqrt{\pi}\) へ行くには、この慎重さが効くぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 97998e3e..10f11512 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -138,8 +138,10 @@ cancellation law to logarithmic sums. Each log sum is identified with the
 logarithm of its finite product, and
 `2 * logNormalizationSum + logDepthSum = 0`. Uniform-average and mesh-width
 weighted variants are exposed as finite candidate observables, and the same
-cancellation law is proved for them. No logarithmic quantity is yet selected
-as the canonical refinement-limit observable.
+cancellation law is proved for them. A pointwise weighted cancellation lemma
+then supplies the standard trapezoidal endpoint half-weight candidate. No
+logarithmic quantity is yet selected as the canonical refinement-limit
+observable.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index 10681be0..80e0b866 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -23,6 +23,9 @@ This module still does not select a logarithmic sum as the canonical
 refinement-limit observable. The average and mesh-weighted variants below are
 therefore recorded only as finite candidate observables: the same cancellation
 law survives scalar reweighting, but no limiting interpretation is chosen here.
+The trapezoidal candidate records the standard closed-interval endpoint
+half-weight pattern as another finite observable, again without selecting a
+limit.
 -/
 
 namespace DkMath.Analysis.DkNNRealQ
@@ -88,6 +91,33 @@ theorem two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum
   exact Finset.sum_eq_zero fun k hk =>
     two_mul_log_dyadicPhaseNormalization_add_log_depth n k
 
+/--
+Pointwise weighted finite logarithmic cancellation.
+
+Every weight function on the complete finite mesh preserves the cancellation
+law because the cancellation already holds at each sampled node. This is the
+finite algebraic form needed before choosing any particular observable such as
+an average, a mesh-width sum, or a trapezoidal sum.
+-/
+theorem two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum
+    (n : ℕ) (w : ℕ → ℝ) :
+    2 * (∑ k ∈ dyadicPhaseNodeIndices n,
+          w k * Real.log (dyadicPhaseNormalization n k)) +
+        (∑ k ∈ dyadicPhaseNodeIndices n,
+          w k * Real.log (dyadicPhaseDepth n k)) = 0 := by
+  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
+  exact Finset.sum_eq_zero fun k hk => by
+    calc
+      2 * (w k * Real.log (dyadicPhaseNormalization n k)) +
+          w k * Real.log (dyadicPhaseDepth n k)
+          = w k *
+              (2 * Real.log (dyadicPhaseNormalization n k) +
+                Real.log (dyadicPhaseDepth n k)) := by
+            ring
+      _ = 0 := by
+        rw [two_mul_log_dyadicPhaseNormalization_add_log_depth n k]
+        simp
+
 /--
 The complete dyadic mesh has one more node than its dyadic denominator.
 
@@ -189,6 +219,56 @@ theorem two_mul_dyadicPhaseWeightedLogNormalizationSum_add_weightedLogDepthSum
       rw [two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum]
       simp
 
+/--
+Trapezoidal weight on the complete finite dyadic node mesh.
+
+The endpoints receive half a mesh width and every interior node receives one
+mesh width. This is a finite closed-interval integration candidate only; no
+convergence or canonical-observable statement is made here.
+-/
+def dyadicPhaseTrapezoidWeight (n k : ℕ) : ℝ :=
+  if k = 0 ∨ k = dyadicPhaseDenom n then
+    dyadicPhaseMeshWeight n / 2
+  else
+    dyadicPhaseMeshWeight n
+
+/-- Every trapezoidal mesh weight is positive. -/
+theorem dyadicPhaseTrapezoidWeight_pos (n k : ℕ) :
+    0 < dyadicPhaseTrapezoidWeight n k := by
+  unfold dyadicPhaseTrapezoidWeight
+  split_ifs
+  · exact div_pos (dyadicPhaseMeshWeight_pos n) (by norm_num)
+  · exact dyadicPhaseMeshWeight_pos n
+
+/-- Trapezoidal finite log-depth sum on the complete dyadic node mesh. -/
+def dyadicPhaseTrapezoidLogDepthSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n,
+    dyadicPhaseTrapezoidWeight n k * Real.log (dyadicPhaseDepth n k)
+
+/--
+Trapezoidal finite log-normalization sum on the complete dyadic node mesh.
+-/
+def dyadicPhaseTrapezoidLogNormalizationSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n,
+    dyadicPhaseTrapezoidWeight n k *
+      Real.log (dyadicPhaseNormalization n k)
+
+/--
+Finite logarithmic cancellation survives trapezoidal endpoint weighting.
+
+This is an application of pointwise weighted cancellation. It records a
+standard closed-interval finite candidate without asserting that this is the
+canonical refinement limit.
+-/
+theorem two_mul_dyadicPhaseTrapezoidLogNormalizationSum_add_trapezoidLogDepthSum
+    (n : ℕ) :
+    2 * dyadicPhaseTrapezoidLogNormalizationSum n +
+        dyadicPhaseTrapezoidLogDepthSum n = 0 := by
+  rw [dyadicPhaseTrapezoidLogNormalizationSum,
+    dyadicPhaseTrapezoidLogDepthSum]
+  exact two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum
+    n (dyadicPhaseTrapezoidWeight n)
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index ced68f27..9ec437cb 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -216,6 +216,19 @@ canonical limit choices; they only make the candidate comparison surface
 explicit before trapezoidal, midpoint, or other weighted observables are
 tested.
 
+The finite comparison surface now also contains the pointwise weighted
+cancellation principle
+
+```text
+sum_k w_k * (2 log normalization_k + log depth_k) = 0.
+```
+
+This theorem separates the algebraic cancellation mechanism from the choice of
+weights. The standard trapezoidal candidate is then implemented by giving the
+two endpoints half a mesh width and every interior node one mesh width. This
+is still a finite observable; it does not by itself prove convergence or
+select the Gaussian-relevant normalization.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 4d444145..25654644 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -387,7 +387,10 @@ the same finite law to be expressed as logarithmic sums:
 `2 * logNormalizationSum + logDepthSum = 0`. Each sum is also proved equal
 to the logarithm of its corresponding finite product. Uniform-average and
 mesh-width weighted log sums are now recorded as finite candidate observables,
-with the same cancellation law transported by scalar multiplication.
+with the same cancellation law transported by scalar multiplication. A
+pointwise weighted cancellation lemma now covers arbitrary finite weights on
+the complete mesh, and the trapezoidal endpoint half-weight candidate is
+implemented from it.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
 finite product, raw logarithmic sum, average, mesh-weighted sum, trapezoidal
 sum, midpoint sum, or another quantity has a canonical refinement limit. The
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 848f6ad4..91221301 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -940,3 +940,24 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 06:13 JST (Weighted logarithmic cancellation)
+
+1. API:
+   - complete finite mesh 上の任意重み `w : ℕ → ℝ` に対する
+     pointwise weighted log cancellation を追加した。
+   - trapezoidal endpoint half-weight
+     `dyadicPhaseTrapezoidWeight` を定義し、positivity を証明した。
+   - trapezoidal log depth / log normalization sum を追加した。
+2. finite laws:
+   - 任意重み補題から、trapezoidal log cancellation を導出した。
+3. boundary:
+   - 台形則は closed-interval integration candidate として記録しただけで、
+     canonical refinement limit、Gaussian weight、`pi` identification は
+     まだ選択していない。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
