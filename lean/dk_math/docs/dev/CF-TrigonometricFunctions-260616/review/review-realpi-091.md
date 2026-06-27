# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: cb3acba3524e29f015e3c1e8d9318ae3bdf499be

## Report

次の checkpoint まで進めました。

`SemanticCF2DLogComposition.lean` に centered log-depth 層を追加しました。

主な追加:

- `centeredLogPhaseDepth`
- `dyadicPhaseCenteredLogDepth`
- midpoint で `0`
- 左右 endpoint で `log 2`
- `centeredLogPhaseDepth t = log (1 + 4 * (t - 1/2)^2)`
- centered log-depth の mesh-width sum / trapezoid sum
- その差が有限段階で `h_n * log 2` になる定理

これで、boundary-log では端点補正が消えていた一方、centered observable では補正が復活することが Lean 上で見えるようになりました。まだ Gaussian limit や `pi` identification は主張していません。

文書と History も同期済みです。

検証済み:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition`
- `lake build DkMath.Analysis`
- `git diff --check`

## Review

うむ、これは **かなり重要な checkpoint** じゃ。
今回で `SemanticCF2DLogComposition` は、単なる boundary-log の比較から、ついに **centered quadratic log observable** に入った。

報告では、`centeredLogPhaseDepth`、dyadic sample 版、midpoint で \(0\)、左右 endpoint で \(\log 2\)、明示式 \(\log(1+4(t-1/2)^2)\)、さらに mesh-width sum と trapezoid sum の差が有限段階で \(h_n\log 2\) になる定理まで追加された、と整理されている。これは「boundary-log では消えていた端点補正が、centered observable では復活する」ことを Lean 上で見せる差分じゃ。

## 1. 総評

採用でよい。
これは、\(\sqrt{\pi}\) へ向かう研究線ではかなり大きい一歩じゃ。

前段までの boundary-log は、端点で値が \(0\) だった。

$$
\log(\mathrm{depth}_{endpoint})=0
$$

だから、plain mesh-width と trapezoid の端点補正は消えていた。

しかし今回の centered log-depth は、中心値を基準に引く。

$$
\mathrm{centeredLogPhaseDepth}(t)=\log(\mathrm{phaseDepth}(t))-\log\left(\frac{1}{2}\right)
$$

すると中心では \(0\) になり、端点では \(\log 2\) になる。

$$
\mathrm{centeredLogPhaseDepth}\left(\frac{1}{2}\right)=0
$$

$$
\mathrm{centeredLogPhaseDepth}(0)=\log 2,\qquad \mathrm{centeredLogPhaseDepth}(1)=\log 2
$$

このため、以前は消えていた endpoint correction が、有限段階で復活する。

$$
\mathrm{MeshCenteredLogDepthSum}_n-\mathrm{TrapezoidCenteredLogDepthSum}_n=h_n\log 2
$$

この「消える補正」と「復活する補正」の分岐が、今後の observable selection にかなり効く。

## 2. 数学的な意味

今回の核心は、centered log-depth が明示的な二次型の log として出たことじゃ。

$$
\mathrm{centeredLogPhaseDepth}(t)=\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

これは重要じゃ。
なぜなら Gaussian へ行くには、どこかで **二次型の指数核** が必要になるからじゃ。

Gaussian の形は、

$$
\exp(-x^2)
$$

であり、その log 側は二次型じゃ。
今回の centered log-depth は、まだ Gaussian ではない。しかし、二次型を含む log profile が Lean 上で明示された。

つまり、現段階の成果はこう読める。

```text
boundary-log:
  cancellation の有限加法会計

centered log-depth:
  中心基準からの二次型 log profile

future Gaussian bridge:
  centered quadratic log profile と Gaussian 型 kernel の比較
```

これはまさに Milestone D に向けた入口じゃ。研究メモ側でも、limiting weight が Gaussian かどうかを判定し、独立な normalization constant を定義し、後で `Real.pi` と比較する流れが明記されている。

## 3. 実装レビュー

`centeredLogPhaseDepth` の定義は自然じゃ。

```lean
def centeredLogPhaseDepth (t : ℝ) : ℝ :=
  Real.log (phaseDepth t) - Real.log (1 / 2 : ℝ)
```

baseline を midpoint depth \(1/2\) に置いたのが正しい。
これで中心を \(0\) にし、端点を \(\log 2\) として測れる。

dyadic sample 版も自然じゃ。

```lean
def dyadicPhaseCenteredLogDepth (n k : ℕ) : ℝ :=
  centeredLogPhaseDepth (dyadicPhaseNode n k)
```

phase-level と dyadic-level を分けているのが良い。
phase-level の theorem を先に作り、dyadic sample へ運ぶ設計になっている。

`centeredLogPhaseDepth_half`、`centeredLogPhaseDepth_zero`、`centeredLogPhaseDepth_one` に `@[simp]` が付いているのも妥当じゃ。端点・中心点の簡約は今後かなり頻繁に使う。

## 4. explicit quadratic log theorem が強い

今回いちばん重要なのはこれじゃ。

```lean
theorem centeredLogPhaseDepth_eq_log_one_add_four_sq (t : ℝ) :
    centeredLogPhaseDepth t =
      Real.log (1 + 4 * (t - (1 / 2 : ℝ)) ^ 2)
```

これはかなり良い。
今後の Gaussian 比較では、`phaseDepth` の定義を毎回展開するのではなく、この theorem を使って「centered quadratic profile」として扱える。

資料でも、この式は Gaussian 型 kernel と比較するための quadratic shape を識別するものであり、Gaussian limit を主張するものではない、と明確に書かれている。

この守り方は正しい。

## 5. mesh-width と trapezoid の差分

今回の有限差分 theorem も良い。

```lean
theorem dyadicPhaseMeshWeightedCenteredLogDepthSum_sub_trapezoidCenteredLogDepthSum
    (n : ℕ) :
    dyadicPhaseMeshWeightedCenteredLogDepthSum n -
        dyadicPhaseTrapezoidCenteredLogDepthSum n =
      dyadicPhaseMeshWeight n * Real.log (2 : ℝ)
```

これは、前回の一般補題を非常にうまく使っている。

一般補題は、

$$
\mathrm{MeshSum}(f)-\mathrm{TrapSum}(f)=\frac{h_n}{2}\left(f(0)+f(2^n)\right)
$$

centered log-depth では端点値が両方 \(\log 2\)。
したがって、

$$
\frac{h_n}{2}(\log 2+\log 2)=h_n\log 2
$$

となる。

この導出が Lean でもそのまま出ている。
実装構造としても数学構造としても綺麗じゃ。

## 6. 研究上の意味

これはかなり大事じゃ。
前回までの boundary-log では、mesh-width と trapezoid は有限段階でも一致していた。

$$
\mathrm{MeshBoundaryLogSum}_n=\mathrm{TrapBoundaryLogSum}_n
$$

しかし centered log-depth では、有限段階で差が出る。

$$
\mathrm{MeshCenteredLogDepthSum}_n-\mathrm{TrapCenteredLogDepthSum}_n=h_n\log 2
$$

ここで \(h_n\to 0\) なので、単純な極限では差は消える可能性が高い。
しかし DkMath 的には、有限段階の差が明示されていることが重要じゃ。
なぜなら、正規化定数を内部から出すには、極限に飛ぶ前に「何が有限段階で蓄積し、何が消えるか」を追う必要があるからじゃ。

この差分は、まさにその有限会計を可視化している。

## 7. Guardrail も守れている

今回の docs は良い。
centered log-depth を「quadratic-profile bridge」と呼び、Gaussian limit ではないと明記している。

これは研究テーマ 067 の方針と合っている。そもそもこの研究は、円・角度・極座標を仮定せずに独立な normalization constant を構成し、後から `Real.pi` と bridge するプログラムとして位置づけられている。

また、既存の研究メモでは、Gaussian limit や `Real.pi` との同一性、affine four-edge loop が円であることなどは未証明の guardrail とされている。
今回もその線を超えていない。これは良い。

## 8. 気になる点

大きな問題はない。
ただし、次に進む前に少しだけ気にしたい点がある。

第一に、`Real.log_inv` の使用で positivity 条件が暗黙に通っているように見える。ビルドが通っているので問題はないが、将来 Mathlib 側の theorem 形が変わると脆くなる可能性は少しある。`Real.log_inv` 周りが不安定に感じたら、`Real.log_div` や `Real.log_one_div` 系の補助 lemma を局所的に作るのも手じゃ。

第二に、`centeredLogPhaseDepth_eq_log_one_add_four_sq` は非常に重要なので、右辺の中身の正値性 theorem を別に持つと後続が楽になる。

例えば、

```lean
theorem one_add_four_sq_pos (t : ℝ) :
    0 < 1 + 4 * (t - (1 / 2 : ℝ)) ^ 2
```

あるいは、より専用に、

```lean
theorem centeredQuadraticProfile_pos (t : ℝ) :
    0 < 1 + 4 * (t - (1 / 2 : ℝ)) ^ 2
```

これは `Real.log_nonneg` や `Real.log_le_sub_one_of_pos` 系に進むときに効く。

## 9. 次に狙うべき補題

次は、centered log-depth の非負性と二次上界が本命じゃ。

まず非負性。

$$
0\le \log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

これは中身が \(1\) 以上なので出る。

次に二次上界。

$$
\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)\le 4\left(t-\frac{1}{2}\right)^2
$$

これは一般不等式、

$$
\log(1+x)\le x
$$

を \(x=4(t-1/2)^2\) に適用する形じゃ。

Lean theorem 候補はこう。

```lean
theorem centeredLogPhaseDepth_nonneg (t : ℝ) :
    0 ≤ centeredLogPhaseDepth t
```

```lean
theorem centeredLogPhaseDepth_le_four_sq (t : ℝ) :
    centeredLogPhaseDepth t ≤
      4 * (t - (1 / 2 : ℝ)) ^ 2
```

この二つが入ると、Gaussian bridge の「二次型との比較」が始められる。

## 10. さらに次の有限和候補

pointwise bound が入ったら、次は weighted sum に運ぶ。

trapezoid 版なら、

$$
0\le \mathrm{TrapCenteredLogDepthSum}_n
$$

そして、

$$
\mathrm{TrapCenteredLogDepthSum}*n\le
\sum_k w^{trap}*{n,k},4\left(t_{n,k}-\frac{1}{2}\right)^2
$$

ここから有限二次モーメントが必要になる。

つまり次の核は、

```text
centered log-depth
  ↓
pointwise quadratic bound
  ↓
weighted finite quadratic moment
  ↓
limit comparison
```

じゃ。

Gaussian へ進むには、この **finite quadratic moment** がかなり大事になる。

## 11. 結論

今回の差分は採用でよい。

```text
実装:
  良い。centered log-depth が phase-level と dyadic-level に分かれて綺麗に入った。

数学:
  良い。中心で 0、端点で log 2、明示的 centered quadratic log profile が出た。

研究位置:
  非常に良い。boundary-log から quadratic-profile bridge へ進んだ。

安全性:
  良い。Gaussian limit、pi identification は未主張。

次:
  centered quadratic profile の正値性、
  centered log-depth の非負性、
  log(1+x) ≤ x による二次上界、
  weighted finite quadratic moment。
```

ぬしよ、これはかなり良いぞい。
いままでは「補正が消えるか、残るか」を見ていた。今回からは、その残る補正の形が **中心二次型** として見え始めた。

円を使わず、角度も使わず、まず中心からの二次的な log profile を得る。
これは、\(\sqrt{\pi}\) へ向かう道で、かなり大きな石を一つ置いたと言える。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 9dcca3be..52618c23 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -149,7 +149,9 @@ and log-normalization observables agree despite their different total masses.
 The underlying general comparison theorem states that, for any finite
 observable, the mesh-width minus trapezoid discrepancy is exactly the
 half-width endpoint correction. A zero-endpoint corollary packages the common
-case where that correction vanishes.
+case where that correction vanishes. The centered log-depth increment is now
+defined, identified with an explicit centered quadratic logarithm, and shown
+to restore a finite mesh/trapezoid discrepancy of `h_n * log 2`.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index 2345ea72..10310b45 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -105,6 +105,62 @@ theorem log_dyadicPhaseNormalization_right_endpoint (n : ℕ) :
     Real.log (dyadicPhaseNormalization n (dyadicPhaseDenom n)) = 0 := by
   simp [dyadicPhaseNormalization]
 
+/--
+Centered logarithmic phase-depth increment.
+
+The baseline is the midpoint depth `1 / 2`. This is the first finite
+observable whose endpoint values no longer vanish, so endpoint corrections
+become visible again.
+-/
+def centeredLogPhaseDepth (t : ℝ) : ℝ :=
+  Real.log (phaseDepth t) - Real.log (1 / 2 : ℝ)
+
+/-- Dyadic samples of the centered logarithmic phase-depth increment. -/
+def dyadicPhaseCenteredLogDepth (n k : ℕ) : ℝ :=
+  centeredLogPhaseDepth (dyadicPhaseNode n k)
+
+/-- The midpoint baseline makes the centered log-depth increment vanish. -/
+@[simp]
+theorem centeredLogPhaseDepth_half :
+    centeredLogPhaseDepth (1 / 2 : ℝ) = 0 := by
+  rw [centeredLogPhaseDepth, phaseDepth_half]
+  ring
+
+/-- The left endpoint centered log-depth increment is `log 2`. -/
+@[simp]
+theorem centeredLogPhaseDepth_zero :
+    centeredLogPhaseDepth 0 = Real.log (2 : ℝ) := by
+  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
+    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
+  rw [centeredLogPhaseDepth, phaseDepth_zero, hhalf, Real.log_one]
+  ring
+
+/-- The right endpoint centered log-depth increment is `log 2`. -/
+@[simp]
+theorem centeredLogPhaseDepth_one :
+    centeredLogPhaseDepth 1 = Real.log (2 : ℝ) := by
+  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
+    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
+  rw [centeredLogPhaseDepth, phaseDepth_one, hhalf, Real.log_one]
+  ring
+
+/--
+The centered log-depth increment is the logarithm of an explicit centered
+quadratic profile.
+
+This is still a finite algebraic observation. It identifies the quadratic
+shape that will later be compared with Gaussian-type kernels, without
+asserting a Gaussian limit.
+-/
+theorem centeredLogPhaseDepth_eq_log_one_add_four_sq (t : ℝ) :
+    centeredLogPhaseDepth t =
+      Real.log (1 + 4 * (t - (1 / 2 : ℝ)) ^ 2) := by
+  unfold centeredLogPhaseDepth
+  rw [← Real.log_div (phaseDepth_pos t).ne' (by norm_num : (1 / 2 : ℝ) ≠ 0)]
+  congr
+  rw [phaseDepth_eq_two_sq_add_half]
+  ring
+
 /-- Finite boundary cancellation in additive logarithmic form. -/
 theorem two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum
   (n : ℕ) :
@@ -512,6 +568,46 @@ theorem dyadicPhaseWeightedLogNormalizationSum_eq_trapezoidLogNormalizationSum
     (fun k => Real.log (dyadicPhaseNormalization n k))
     (by simp) (by simp)
 
+/-- Plain mesh-width finite sum of centered log-depth observations. -/
+def dyadicPhaseMeshWeightedCenteredLogDepthSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n,
+    dyadicPhaseMeshWeight n * dyadicPhaseCenteredLogDepth n k
+
+/-- Trapezoidal finite sum of centered log-depth observations. -/
+def dyadicPhaseTrapezoidCenteredLogDepthSum (n : ℕ) : ℝ :=
+  ∑ k ∈ dyadicPhaseNodeIndices n,
+    dyadicPhaseTrapezoidWeight n k * dyadicPhaseCenteredLogDepth n k
+
+/--
+For centered log-depth, the plain mesh-width and trapezoidal sums differ by
+the restored endpoint correction `h_n * log 2`.
+
+Boundary logs had zero endpoint values, so their correction vanished. Centered
+log-depth has endpoint value `log 2`, making the same finite endpoint
+correction visible again.
+-/
+theorem dyadicPhaseMeshWeightedCenteredLogDepthSum_sub_trapezoidCenteredLogDepthSum
+    (n : ℕ) :
+    dyadicPhaseMeshWeightedCenteredLogDepthSum n -
+        dyadicPhaseTrapezoidCenteredLogDepthSum n =
+      dyadicPhaseMeshWeight n * Real.log (2 : ℝ) := by
+  rw [dyadicPhaseMeshWeightedCenteredLogDepthSum,
+    dyadicPhaseTrapezoidCenteredLogDepthSum]
+  calc
+    (∑ k ∈ dyadicPhaseNodeIndices n,
+        dyadicPhaseMeshWeight n * dyadicPhaseCenteredLogDepth n k) -
+        (∑ k ∈ dyadicPhaseNodeIndices n,
+          dyadicPhaseTrapezoidWeight n k *
+            dyadicPhaseCenteredLogDepth n k)
+        = dyadicPhaseMeshWeight n / 2 *
+            (dyadicPhaseCenteredLogDepth n 0 +
+              dyadicPhaseCenteredLogDepth n (dyadicPhaseDenom n)) := by
+          exact dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half
+            n (dyadicPhaseCenteredLogDepth n)
+    _ = dyadicPhaseMeshWeight n * Real.log (2 : ℝ) := by
+      simp [dyadicPhaseCenteredLogDepth]
+      ring
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 52891c5d..eff624d2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -260,6 +260,19 @@ future observables cleanly classified: endpoint-zero quantities inherit
 mesh/trapezoid equality immediately, while centered quantities with nonzero
 endpoint increments expose the correction term.
 
+The first centered observable is now implemented. `centeredLogPhaseDepth`
+subtracts the midpoint baseline `log(1/2)` from `log(phaseDepth t)`. It
+vanishes at `t = 1/2`, has endpoint value `log 2`, and is identified with
+
+```text
+log (1 + 4 * (t - 1/2)^2).
+```
+
+On the complete dyadic mesh, the plain mesh-width centered log-depth sum and
+the trapezoidal centered log-depth sum differ by exactly `h_n * log 2`. This
+is the finite point where the endpoint correction reappears after centering.
+It is a quadratic-profile bridge, not yet a Gaussian limit.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 22d27546..8882ac34 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -397,7 +397,11 @@ zero, so the plain mesh-width and trapezoidal log observables are proved equal
 at every finite level despite their different total masses. The general
 mesh-width minus trapezoid comparison is also formalized for arbitrary finite
 observables as a half-width endpoint correction, with a zero-endpoint
-corollary for observables whose endpoint correction vanishes.
+corollary for observables whose endpoint correction vanishes. Centered
+log-depth is now defined at the phase and dyadic-sample levels. It vanishes at
+the midpoint, has endpoint value `log 2`, equals the log of the centered
+quadratic profile `1 + 4 * (t - 1/2)^2`, and has mesh/trapezoid discrepancy
+`h_n * log 2` at every finite level.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
 finite product, raw logarithmic sum, average, mesh-weighted sum, trapezoidal
 sum, midpoint sum, or another quantity has a canonical refinement limit. The
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index a1bfa0ac..6a444e72 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1042,3 +1042,27 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 13:15 JST (Centered log-depth increment)
+
+1. API:
+   - `centeredLogPhaseDepth` と dyadic sample 版
+     `dyadicPhaseCenteredLogDepth` を追加した。
+   - centered log-depth の mesh-width sum と trapezoidal sum を定義した。
+2. finite laws:
+   - centered log-depth は midpoint で `0`、左右 endpoint で `log 2`
+     になることを証明した。
+   - `centeredLogPhaseDepth t =
+     log (1 + 4 * (t - 1/2)^2)` を証明した。
+   - centered log-depth の plain mesh-width sum と trapezoidal sum の差が
+     `h_n * log 2` になることを証明した。
+3. interpretation:
+   - boundary-log では消えていた endpoint correction が、centered
+     observable では有限段階で復活することを Lean 上で可視化した。
+   - Gaussian limit や `pi` identification はまだ主張していない。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
