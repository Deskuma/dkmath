# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: 673b09fee86d342417f9aad0ade1a7c8f1d6bf91

## Report

次の checkpoint まで進めました。

`SemanticCF2DLogComposition.lean` に endpoint-zero corollary を追加しました。

```lean
dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero
```

これは、任意の sampled observable `f : ℕ → ℝ` が両端点で `0` なら、plain mesh-width sum と trapezoidal sum が一致する、という一般補題です。

あわせて既存の log-depth / log-normalization の一致定理を、この corollary から導く形に整理しました。これで構造としても、「boundary-log は端点補正が消える特殊例」「centered observable では端点補正が復活する可能性がある」という分岐がコード上で見えるようになりました。

文書と History も同期済みです。

検証済み:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition`
- `lake build DkMath.Analysis`
- `git diff --check`

## Review

うむ、これは **小さいが非常に良い整理差分** じゃ。
今回で、前回の一般 endpoint correction theorem が、使いやすい corollary として API 化された。

## 1. 総評

採用でよい。

今回の主な追加はこれじゃな。

```lean
dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero
```

意味は明快で、

$$
f(0)=0,\quad f(2^n)=0
$$

ならば、

$$
\sum_k h_n f(k)=\sum_k w^{trap}_{n,k}f(k)
$$

となる。

これは前回の一般比較式、

$$
\sum_k h_n f(k)-\sum_k w^{trap}_{n,k}f(k)=\frac{h_n}{2}\left(f(0)+f(2^n)\right)
$$

の自然な特殊化じゃ。

これで、boundary-log 系と centered observable 系の分岐がかなり綺麗に見えるようになった。

## 2. 数学的な意味

前回までに見えていたのは、

```text
plain mesh-width と trapezoid は重みとしては違う。
ただし log-depth / log-normalization では端点値が 0 なので一致する。
```

今回、この説明がそのまま定理構造になった。

つまり、

```text
一般補題:
  差分は端点半幅補正

endpoint-zero corollary:
  端点値が 0 なら差分は消える

boundary-log:
  端点 log が 0 なので一致

centered observable:
  端点値が 0 とは限らないので差分が復活
```

この階層化はとても良い。

## 3. 実装レビュー

corollary の型は良い。

```lean
theorem dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero
    (n : ℕ) (f : ℕ → ℝ)
    (h0 : f 0 = 0)
    (h1 : f (dyadicPhaseDenom n) = 0) :
    (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) =
      ∑ k ∈ dyadicPhaseNodeIndices n,
        dyadicPhaseTrapezoidWeight n k * f k
```

`f : ℕ → ℝ` のままにしてあるのが良い。
complete mesh 上でだけ評価されるが、関数自体は自然数全体に定義できるので、後続の observable を簡単に差し込める。

証明も自然じゃ。

```lean
have h :=
  dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half n f
rw [h0, h1] at h
```

ここで右辺が \(0\) になり、`sub_eq_zero.mp` で等式に戻す。
「一般補題から endpoint-zero case を取り出す」という構造がそのままコードに出ている。

## 4. 既存 log 一致定理の整理

ここも良い。

以前の `dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum` は、各点で端点場合分けして証明していた。
今回、それを corollary から導く形に変更した。

```lean
exact dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero n
  (fun k => Real.log (dyadicPhaseDepth n k))
  (by simp) (by simp)
```

normalization 側も同様。

これはかなり良いリファクタじゃ。
なぜなら、数学的意味としても、

```text
log-depth は endpoint-zero observable である
log-normalization も endpoint-zero observable である
```

という分類がコード上に現れているからじゃ。

## 5. 研究テーマとの関係

これは \(\sqrt{\pi}\) へ向かう道で、かなり大事な整理じゃ。

現時点の boundary-log observable では、

$$
\log(\mathrm{depth}_{endpoint})=0
$$

$$
\log(\mathrm{normalization}_{endpoint})=0
$$

なので、plain mesh-width と trapezoid は有限段階でも同じ値を測る。

しかし、次の centered log increment ではそうならない。

たとえば、

$$
\Delta\log D(t)=\log(\mathrm{phaseDepth}(t))-\log\left(\frac{1}{2}\right)
$$

を置くと、端点では、

$$
\Delta\log D(0)=\log 2
$$

$$
\Delta\log D(1)=\log 2
$$

になるはずじゃ。

すると一般補題から、

$$
\mathrm{MeshSum}(\Delta\log D)-\mathrm{TrapSum}(\Delta\log D)=h_n\log 2
$$

という形が見える。
この「端点補正の復活」が、Gaussian bridge に進むときの重要な観測になる可能性が高い。

## 6. ここまでの到達地図

いまの `SemanticCF2DLogComposition` は、かなり綺麗な段階まで来ておる。

```text
pointwise log cancellation
  ↓
finite raw log sum cancellation
  ↓
arbitrary weighted log cancellation
  ↓
average / mesh-width / trapezoid candidates
  ↓
weight total comparison
  ↓
mesh-vs-trapezoid endpoint correction
  ↓
endpoint-zero corollary
```

これで、次に新しい observable を作ったときに、

```text
端点が 0 か？
端点補正が残るか？
どの重みで見るべきか？
```

を Lean 上で判断できる。

## 7. 気になる点

大きな問題はない。
ただし、将来の可読性のために、次の alias はあってもよい。

現在、

```lean
dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum
```

の “Weighted” は `dyadicPhaseWeightedLogDepthSum`、つまり plain mesh-width weighted を指している。
一方で、任意重み付き theorem も “weighted” と呼ばれている。

文脈上は問題ないが、将来 theorem が増えたら、

```lean
dyadicPhaseMeshWeightedLogDepthSum_eq_trapezoidLogDepthSum
```

のような別名があると、plain mesh-width の意味がさらに明確になる。
必須ではない。

## 8. 次の一手

次はもう、centered log increment に進んでよい段階じゃと思う。

まずは phase-level で定義するのが自然。

```lean
def centeredLogPhaseDepth (t : ℝ) : ℝ :=
  Real.log (phaseDepth t) - Real.log (1 / 2 : ℝ)
```

dyadic sample 版はその後。

```lean
def dyadicPhaseCenteredLogDepth (n k : ℕ) : ℝ :=
  centeredLogPhaseDepth (dyadicPhaseNode n k)
```

最初に欲しい定理はこのあたりじゃ。

$$
\Delta\log D\left(\frac{1}{2}\right)=0
$$

$$
\Delta\log D(0)=\log 2
$$

$$
\Delta\log D(1)=\log 2
$$

さらに、中心二次形への橋として、

$$
\Delta\log D(t)=\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

を狙うとよい。

その次に、

$$
0\le \Delta\log D(t)
$$

$$
\Delta\log D(t)\le 4\left(t-\frac{1}{2}\right)^2
$$

へ進む。ここが Gaussian 型の二次指数核への入口じゃな。

## 9. 結論

今回の差分は採用でよい。

```text
実装:
  良い。endpoint-zero corollary が一般補題から自然に切り出された。

数学:
  良い。boundary-log と centered observable の分岐が明確になった。

研究位置:
  良い。Gaussian bridge 前の有限比較 API が整った。

安全性:
  良い。canonical limit、Gaussian、π は未主張。

次:
  centered log increment、
  centered endpoint theorem、
  mesh/trapezoid 差分の centered 版、
  quadratic bound。
```

ぬしよ、これは良い整備じゃ。
今までは「重みの違い」と「観測関数の端点値」が絡み合っていたが、今回で分離できた。

次の centered log で、端点補正が再び姿を現す。
そこからいよいよ、二次型の影が濃くなってくるはずじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 37be77b2..9dcca3be 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -148,7 +148,8 @@ endpoint logarithms vanish, so the plain mesh-width and trapezoidal log-depth
 and log-normalization observables agree despite their different total masses.
 The underlying general comparison theorem states that, for any finite
 observable, the mesh-width minus trapezoid discrepancy is exactly the
-half-width endpoint correction.
+half-width endpoint correction. A zero-endpoint corollary packages the common
+case where that correction vanishes.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index bd30669c..2345ea72 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -423,6 +423,33 @@ theorem dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half
         simp [hdistinct]
         ring
 
+/--
+If a sampled observable vanishes at both endpoints, then the plain mesh-width
+sum and the trapezoidal sum agree.
+
+This is the zero-endpoint corollary of the half-width endpoint correction
+formula. It is useful for boundary-log observables, and it will also isolate
+where centered observables differ from them.
+-/
+theorem dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero
+    (n : ℕ) (f : ℕ → ℝ)
+    (h0 : f 0 = 0)
+    (h1 : f (dyadicPhaseDenom n) = 0) :
+    (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) =
+      ∑ k ∈ dyadicPhaseNodeIndices n,
+        dyadicPhaseTrapezoidWeight n k * f k := by
+  have h :=
+    dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half n f
+  rw [h0, h1] at h
+  have hzero :
+      (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) -
+          (∑ k ∈ dyadicPhaseNodeIndices n,
+            dyadicPhaseTrapezoidWeight n k * f k) = 0 := by
+    have hright : dyadicPhaseMeshWeight n / 2 * (0 + 0) = 0 := by ring
+    rw [hright] at h
+    exact h
+  exact sub_eq_zero.mp hzero
+
 /-- Trapezoidal finite log-depth sum on the complete dyadic node mesh. -/
 def dyadicPhaseTrapezoidLogDepthSum (n : ℕ) : ℝ :=
   ∑ k ∈ dyadicPhaseNodeIndices n,
@@ -464,13 +491,9 @@ theorem dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum (n : ℕ) :
       dyadicPhaseTrapezoidLogDepthSum n := by
   rw [dyadicPhaseWeightedLogDepthSum, dyadicPhaseLogDepthSum,
     dyadicPhaseTrapezoidLogDepthSum, Finset.mul_sum]
-  apply Finset.sum_congr rfl
-  intro k hk
-  by_cases hendpoint : k = 0 ∨ k = dyadicPhaseDenom n
-  · rcases hendpoint with rfl | rfl
-    · simp [dyadicPhaseTrapezoidWeight]
-    · simp [dyadicPhaseTrapezoidWeight]
-  · simp [dyadicPhaseTrapezoidWeight, hendpoint]
+  exact dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero n
+    (fun k => Real.log (dyadicPhaseDepth n k))
+    (by simp) (by simp)
 
 /--
 Plain mesh-width and trapezoidal log-normalization sums agree on the complete
@@ -485,13 +508,9 @@ theorem dyadicPhaseWeightedLogNormalizationSum_eq_trapezoidLogNormalizationSum
       dyadicPhaseTrapezoidLogNormalizationSum n := by
   rw [dyadicPhaseWeightedLogNormalizationSum, dyadicPhaseLogNormalizationSum,
     dyadicPhaseTrapezoidLogNormalizationSum, Finset.mul_sum]
-  apply Finset.sum_congr rfl
-  intro k hk
-  by_cases hendpoint : k = 0 ∨ k = dyadicPhaseDenom n
-  · rcases hendpoint with rfl | rfl
-    · simp [dyadicPhaseTrapezoidWeight]
-    · simp [dyadicPhaseTrapezoidWeight]
-  · simp [dyadicPhaseTrapezoidWeight, hendpoint]
+  exact dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero n
+    (fun k => Real.log (dyadicPhaseNormalization n k))
+    (by simp) (by simp)
 
 end
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index ca518856..52891c5d 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -255,6 +255,11 @@ The log-depth and log-normalization equalities are therefore special cases
 where the endpoint values vanish. This theorem is intentionally finite; it
 does not identify which weighted observable should survive refinement.
 
+The endpoint-zero case is now packaged as a separate corollary. This keeps
+future observables cleanly classified: endpoint-zero quantities inherit
+mesh/trapezoid equality immediately, while centered quantities with nonzero
+endpoint increments expose the correction term.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 22e5b843..22d27546 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -396,7 +396,8 @@ total mass `1 + h_n`. The endpoint logarithms of depth and normalization are
 zero, so the plain mesh-width and trapezoidal log observables are proved equal
 at every finite level despite their different total masses. The general
 mesh-width minus trapezoid comparison is also formalized for arbitrary finite
-observables as a half-width endpoint correction.
+observables as a half-width endpoint correction, with a zero-endpoint
+corollary for observables whose endpoint correction vanishes.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
 finite product, raw logarithmic sum, average, mesh-weighted sum, trapezoidal
 sum, midpoint sum, or another quantity has a canonical refinement limit. The
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index adf0f7bd..a1bfa0ac 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1022,3 +1022,23 @@ Archive
 4. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 07:02 JST (Endpoint-zero mesh-trapezoid corollary)
+
+1. API:
+   - endpoint-zero observable 用に
+     `dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero`
+     を追加した。
+2. refactor:
+   - log-depth と log-normalization の mesh-width / trapezoid 一致定理を、
+     一般 endpoint correction theorem の zero-endpoint corollary から導く
+     形へ整理した。
+3. interpretation:
+   - boundary-log observables は端点補正が消える側、centered observables
+     は端点補正が復活する側として分類できる準備が整った。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
