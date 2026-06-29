# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: de744a1cec2347ce0c5435f6cd11e808803ca05d

## Report

次の checkpoint まで進めました。

`SemanticCF2DLogComposition.lean` に、任意の sampled observable `f : ℕ → ℝ` についての一般比較補題を追加しました。

```lean
dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half
```

内容は、plain complete mesh-width sum と trapezoidal sum の差が、ちょうど

```text
h_n / 2 * (f 0 + f (2^n))
```

になるという有限段階の端点補正です。

これで、前回の「log-depth / log-normalization では mesh-width と trapezoid が一致する」は、端点 log 値が `0` になる特殊例として整理できます。次の centered log increment では端点値が消えないので、この一般補題がそのまま効くはずです。

文書と History も同期済みです。

検証済み:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition`
- `lake build DkMath.Analysis`
- `git diff --check`

## Review

うむ、これは良い。
今回の差分で、前回までの「plain mesh-width と trapezoid は log observable では一致する」という個別事実が、きれいに **一般補題の特殊例** として整理された。

## 1. 総評

採用でよい。

今回の主定理はこれじゃな。

$$
\sum_k h_n f(k)-\sum_k w^{\mathrm{trap}}_{n,k}f(k)
=\frac{h_n}{2}\left(f(0)+f(2^n)\right)
$$

ここで \(h_n=1/2^n\)。
つまり、plain complete mesh-width sum と trapezoidal sum の違いは、常に **端点半幅補正** だけである、という有限恒等式じゃ。

これはかなり良い。
前回の log-depth / log-normalization の一致は、端点で \(f=0\) になる特殊ケースとして説明できるようになった。

## 2. 数学的な意味

前回までの状況はこうだった。

```text id="tt527e"
plain mesh-width:
  total mass = 1 + h_n

trapezoid:
  total mass = 1

boundary log-depth / log-normalization:
  endpoint values = 0
```

だから、総重みは違うのに、log observable の値は同じだった。

今回の一般補題により、その理由が完全に見えた。

$$
\mathrm{MeshSum}(f)-\mathrm{TrapSum}(f)
=\frac{h_n}{2}\left(f(0)+f(2^n)\right)
$$

したがって、端点値が \(0\) なら差は消える。

$$
f(0)=0,\quad f(2^n)=0
$$

ならば、

$$
\mathrm{MeshSum}(f)=\mathrm{TrapSum}(f)
$$

これは、有限観測量の比較として非常に強い。
単に「今回たまたま一致した」ではなく、「何が一致条件なのか」が定理になった。

## 3. 実装レビュー

主定理の型は良い。

```lean
theorem dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half
    (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) -
        (∑ k ∈ dyadicPhaseNodeIndices n,
          dyadicPhaseTrapezoidWeight n k * f k) =
      dyadicPhaseMeshWeight n / 2 *
        (f 0 + f (dyadicPhaseDenom n))
```

`f : ℕ → ℝ` にしているので、log-depth でも、log-normalization でも、centered log increment でも、そのまま入れられる。
これは良い抽象度じゃ。

証明構造も自然じゃな。

```text id="o0c15i"
1. sum の差を項ごとの差に移す。
2. endpoint なら h_n/2 * f k が残る。
3. interior なら差は 0。
4. endpoint filter を {0, 2^n} に畳む。
```

前回入れた `dyadicPhaseEndpointFilter_eq` がきちんと効いている。
補助定理が次の定理を支えているので、API の流れも美しい。

## 4. 研究上の意味

これは、\(\sqrt{\pi}\) に向かう前段として重要じゃ。

Gaussian bridge で本当に必要になるのは、単なる boundary log ではなく、たぶん centered log increment じゃろう。

たとえば、

$$
\Delta\log D(t)=\log(\mathrm{phaseDepth}(t))-\log\left(\frac{1}{2}\right)
$$

この場合、端点では値が消えない。

$$
\Delta\log D(0)=\log 2
$$

$$
\Delta\log D(1)=\log 2
$$

だから、今回の一般補題を使うと、plain mesh-width と trapezoid の差が有限段階で明示できる。

$$
\mathrm{MeshSum}(\Delta\log D)-\mathrm{TrapSum}(\Delta\log D)
=h_n\log 2
$$

このような形が出るはずじゃ。
これはかなり大事で、centered observable に進んだ瞬間、前回までは消えていた端点補正が復活する。

## 5. よい設計判断

今回の差分で一番良いのは、「log-depth 専用」「normalization 専用」の比較を増やすのではなく、任意の sampled observable \(f\) に対して一般化した点じゃ。

これにより、次の候補が全部同じ補題で扱える。

```text id="zc4ofe"
boundary log depth
boundary log normalization
centered log depth
centered log normalization
quadratic comparison observable
future Gaussian-test observable
```

つまり、次からは「新しい observable を作るたびに mesh-vs-trapezoid 比較を再証明する」必要がない。
これは Lean 実装としてかなり良い。

## 6. 気になる点

大きな問題はない。
ただし、前回の個別 theorem、

```lean
dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum
```

と、

```lean
dyadicPhaseWeightedLogNormalizationSum_eq_trapezoidLogNormalizationSum
```

は、今後リファクタすると、この一般補題から導く形にしてもよい。

今のままでも問題ない。
ただ、数学的説明としては一般補題からの corollary にした方が、構造がさらに明瞭になる。

例えば depth 側は概念的にはこうじゃ。

```lean
have h :=
  dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half
    n (fun k => Real.log (dyadicPhaseDepth n k))
```

端点 log が `simp` で \(0\) になり、差が \(0\)。
この形にすれば、「前回の一致は端点補正公式の特殊例」という構造がコード上にも表れる。

ただし、ビルド済みなら今すぐ直す必要はない。
次に触るときで十分じゃ。

## 7. 次に進むなら

次はかなり自然に、centered log increment へ進める。

定義候補はこうじゃ。

```lean
def dyadicPhaseCenteredLogDepth (n k : ℕ) : ℝ :=
  Real.log (dyadicPhaseDepth n k) - Real.log (1 / 2 : ℝ)
```

または phase parameter 版を先に置くなら、

```lean
def centeredLogPhaseDepth (t : ℝ) : ℝ :=
  Real.log (phaseDepth t) - Real.log (1 / 2 : ℝ)
```

中心化した形は、

$$
\Delta\log D(t)=\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

ここから次の有限補題が狙える。

$$
0\le \Delta\log D(t)
$$

$$
\Delta\log D(t)\le 4\left(t-\frac{1}{2}\right)^2
$$

後者は \(\log(1+x)\le x\) を使う形じゃな。

この二次上界が、Gaussian へ向かう次の橋になる。

## 8. 追加すると強い corollary

今回の一般補題から、すぐに次が欲しくなる。

```text id="is51e6"
端点値が 0 なら mesh sum と trapezoid sum は一致する
```

Lean なら、

```lean
theorem dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero
    (n : ℕ) (f : ℕ → ℝ)
    (h0 : f 0 = 0)
    (h1 : f (dyadicPhaseDenom n) = 0) :
    (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) =
      ∑ k ∈ dyadicPhaseNodeIndices n,
        dyadicPhaseTrapezoidWeight n k * f k
```

これがあると、log-depth / log-normalization の一致がさらに短く書ける。
また今後、他の endpoint-zero observable にも使える。

## 9. 結論

今回の差分は採用でよい。

```text id="kdxvfh"
実装:
  良い。mesh-width と trapezoid の差分を任意 observable で一般化した。

数学:
  良い。差分の正体が half-width endpoint correction として明確になった。

研究位置:
  非常に良い。centered log increment で端点補正が復活する準備ができた。

安全性:
  良い。Gaussian、π、canonical limit は未主張。

次:
  endpoint-zero corollary、
  centered log increment、
  centered endpoint correction、
  quadratic bound。
```

ぬしよ、これはよい。
ついに「重みの違い」が、ただの感覚ではなく、有限公式として捕まった。

次の centered log で、この補題は効くぞい。
今まで端点で消えていた差が、中心化によって姿を現す。そこに、Gaussian へ向かう道の輪郭が出てくるはずじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 8061069f..37be77b2 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -146,6 +146,9 @@ trapezoidal weights are also exposed to distinguish sample-mean,
 endpoint-overcounted complete-mesh, and closed-interval candidates. The
 endpoint logarithms vanish, so the plain mesh-width and trapezoidal log-depth
 and log-normalization observables agree despite their different total masses.
+The underlying general comparison theorem states that, for any finite
+observable, the mesh-width minus trapezoid discrepancy is exactly the
+half-width endpoint correction.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index 3770ad4a..bd30669c 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -377,6 +377,52 @@ theorem sum_dyadicPhaseTrapezoidWeight_eq_one (n : ℕ) :
       rw [hmesh, hend]
       ring
 
+/--
+Plain mesh-width and trapezoidal finite sums differ only by the half-width
+endpoint correction.
+
+This theorem separates the choice of finite weights from the sampled
+observable `f`. It is the general bookkeeping identity behind the later
+special cases where endpoint logarithms vanish.
+-/
+theorem dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half
+    (n : ℕ) (f : ℕ → ℝ) :
+    (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) -
+        (∑ k ∈ dyadicPhaseNodeIndices n,
+          dyadicPhaseTrapezoidWeight n k * f k) =
+      dyadicPhaseMeshWeight n / 2 *
+        (f 0 + f (dyadicPhaseDenom n)) := by
+  calc
+    (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) -
+        (∑ k ∈ dyadicPhaseNodeIndices n,
+          dyadicPhaseTrapezoidWeight n k * f k)
+        = ∑ k ∈ dyadicPhaseNodeIndices n,
+            (dyadicPhaseMeshWeight n * f k -
+              dyadicPhaseTrapezoidWeight n k * f k) := by
+          rw [Finset.sum_sub_distrib]
+    _ = ∑ k ∈ dyadicPhaseNodeIndices n,
+          (if k = 0 ∨ k = dyadicPhaseDenom n then
+            dyadicPhaseMeshWeight n / 2 * f k
+          else
+            0) := by
+        apply Finset.sum_congr rfl
+        intro k hk
+        unfold dyadicPhaseTrapezoidWeight
+        by_cases hendpoint : k = 0 ∨ k = dyadicPhaseDenom n
+        · rw [if_pos hendpoint]
+          simp [hendpoint]
+          ring_nf
+        · rw [if_neg hendpoint]
+          simp [hendpoint]
+    _ = dyadicPhaseMeshWeight n / 2 *
+        (f 0 + f (dyadicPhaseDenom n)) := by
+        rw [← Finset.sum_filter]
+        rw [dyadicPhaseEndpointFilter_eq]
+        have hdistinct : (0 : ℕ) ≠ dyadicPhaseDenom n :=
+          (dyadicPhaseDenom_pos n).ne
+        simp [hdistinct]
+        ring
+
 /-- Trapezoidal finite log-depth sum on the complete dyadic node mesh. -/
 def dyadicPhaseTrapezoidLogDepthSum (n : ℕ) : ℝ :=
   ∑ k ∈ dyadicPhaseNodeIndices n,
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 699cb844..ca518856 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -243,6 +243,18 @@ Thus the two candidates differ as measures, but not on these particular
 boundary-log observables. This distinction keeps the finite bookkeeping sharp
 without prematurely selecting a canonical limit.
 
+The general finite comparison is now explicit: for any sampled observable
+`f`, the difference between the plain mesh-width complete-node sum and the
+trapezoidal sum is
+
+```text
+h_n / 2 * (f 0 + f (2^n)).
+```
+
+The log-depth and log-normalization equalities are therefore special cases
+where the endpoint values vanish. This theorem is intentionally finite; it
+does not identify which weighted observable should survive refinement.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 9d9f9b3f..22e5b843 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -394,7 +394,9 @@ implemented from it. The weight masses are formalized: average and trapezoid
 weights have total mass `1`, while the plain complete mesh-width weights have
 total mass `1 + h_n`. The endpoint logarithms of depth and normalization are
 zero, so the plain mesh-width and trapezoidal log observables are proved equal
-at every finite level despite their different total masses.
+at every finite level despite their different total masses. The general
+mesh-width minus trapezoid comparison is also formalized for arbitrary finite
+observables as a half-width endpoint correction.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
 finite product, raw logarithmic sum, average, mesh-weighted sum, trapezoidal
 sum, midpoint sum, or another quantity has a canonical refinement limit. The
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 89a04f48..adf0f7bd 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1004,3 +1004,21 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 06:47 JST (Mesh-trapezoid endpoint correction)
+
+1. finite comparison:
+   - 任意の sampled observable `f : ℕ → ℝ` について、plain mesh-width
+     complete-node sum と trapezoidal sum の差が
+     `h_n / 2 * (f 0 + f (2^n))` になる theorem を追加した。
+2. interpretation:
+   - 前回の log-depth / log-normalization 一致は、端点 log 値が `0`
+     になるための特殊例として見えるようになった。
+   - centered log increment では端点値が一般に `0` ではなくなるため、
+     この一般補題が次段の比較面になる。
+3. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+4. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
