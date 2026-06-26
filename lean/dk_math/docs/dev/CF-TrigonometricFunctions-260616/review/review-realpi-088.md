# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: 4b235c3f5c9f4a46367b94001b1bb0770cee6564

## Report

次の checkpoint まで進めました。

`SemanticCF2DLogComposition.lean` に端点 log 補題と、plain mesh-width / trapezoid の比較定理を追加しました。

追加内容:

- depth の左右端点 log が `0`
- normalization の左右端点 log が `0`
- `dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum`
- `dyadicPhaseWeightedLogNormalizationSum_eq_trapezoidLogNormalizationSum`

これで、重みの総量としては plain mesh-width が `1 + h_n`、trapezoid が `1` で違う一方、現在の boundary-log observable では端点寄与が `0` なので有限段階でも同じ値を測る、という点が Lean 上で明確になりました。

文書と History も同期済みです。

検証済み:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition`
- `lake build DkMath.Analysis`
- `git diff --check`

## Review

うむ、これはかなり良い。
今回の差分で、重みの違いと、実際に測っている boundary-log observable の違いが分離された。

## 1. 総評

採用でよい。

今回の核はこれじゃ。

$$
\mathrm{plain\ mesh\ width\ weight\ total}=1+h_n,\qquad \mathrm{trapezoid\ weight\ total}=1
$$

にもかかわらず、現在の log-depth / log-normalization observable では、

$$
\mathrm{WeightedLogDepthSum}_n=\mathrm{TrapezoidLogDepthSum}_n
$$

$$
\mathrm{WeightedLogNormalizationSum}_n=\mathrm{TrapezoidLogNormalizationSum}_n
$$

が有限段階で成立する、という点じゃ。

これはかなり面白い。
重みとしては違う。測度としては違う。けれど、今回測っている関数が端点で \(0\) なので、その違いが observable には現れない。

```text
重みは違う。
だが差分が端点だけに載る。
そして端点の log 値は 0。
ゆえに今回の observable では同じ値を測る。
```

この整理が Lean 上で固定されたのは、かなり良い checkpoint じゃ。

## 2. 数学的な意味

端点では affine transition が元の boundary 上に戻る。
だから depth は \(1\) になる。

$$
\mathrm{depth}*{n,0}=1,\qquad \mathrm{depth}*{n,2^n}=1
$$

したがって、

$$
\log(\mathrm{depth}*{n,0})=0,\qquad \log(\mathrm{depth}*{n,2^n})=0
$$

normalization も端点では \(1\) なので、

$$
\log(\mathrm{normalization}*{n,0})=0,\qquad \log(\mathrm{normalization}*{n,2^n})=0
$$

plain mesh-width と trapezoid の違いは、端点の半重み処理だけじゃ。
しかし、その端点で log observation が \(0\) なので、差が消える。

これは、有限観測量として非常に良い分類じゃな。

```text
weight mass:
  plain mesh-width と trapezoid は異なる。

boundary-log observable:
  plain mesh-width と trapezoid は一致する。
```

この二層を分けたのが今回の成果じゃ。

## 3. 実装レビュー

端点 log 補題は良い。

```lean
@[simp]
theorem log_dyadicPhaseDepth_left_endpoint (n : ℕ) :
    Real.log (dyadicPhaseDepth n 0) = 0 := by
  simp [dyadicPhaseDepth]
```

右端点、normalization 側も同様に入っている。
`@[simp]` を付けたのも自然じゃ。端点評価で頻繁に消えてほしい式だからな。

ただし、今後 simp が強くなりすぎる場合だけ注意じゃ。
現状では端点 log の消去として素直なので問題ない。

plain mesh-width と trapezoid の比較定理も良い。

```lean
theorem dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum (n : ℕ) :
    dyadicPhaseWeightedLogDepthSum n =
      dyadicPhaseTrapezoidLogDepthSum n := by
```

証明構造も明快じゃ。

```text
各 k で端点かどうかを場合分けする。
端点なら log が 0 なので重み差が消える。
内部なら重みが同じ。
```

normalization 側も同じ構造で通している。
これは良い API じゃ。

## 4. とても重要な解釈

この差分で分かったのは、「重みの総量」だけでは observable を判断できない、ということじゃ。

plain mesh-width は総量 \(1+h_n\)。
trapezoid は総量 \(1\)。
だから普通は違う積分候補に見える。

しかし、対象関数が端点で \(0\) なら、両者は同じ有限値を返す。

これは今後の canonical observable selection に効く。

```text
測度として異なる候補でも、
対象関数の端点値によっては同じ観測値になる。
```

ここを Lean で明確にできたのは大きい。

## 5. 研究テーマとの関係

\(\sqrt{\pi}\) へ向かう道では、これは重要な足場じゃ。

最終目標では、CF2D 内部から Gaussian 型の normalization constant を出したい。
そのためには、どの finite observable を極限対象にするか選ぶ必要がある。

今回の結果は、次のように読める。

```text
boundary-log observable だけを見るなら、
plain complete mesh-width と trapezoid は有限段階でも同値。

しかし、
weight measure としては異なるので、
別の observable を入れると差が出る可能性がある。
```

特に次に来るであろう centered log increment では、この差が復活する可能性が高い。

## 6. 次で特に注意すべき点

次に中心基準を引くと、端点値はもう \(0\) ではなくなる。

例えば depth 側で、

$$
\Delta\log D(t)=\log(\mathrm{phaseDepth}(t))-\log\left(\frac{1}{2}\right)
$$

と定義すると、端点では \(\mathrm{phaseDepth}=1\) なので、

$$
\Delta\log D(0)=\log(1)-\log\left(\frac{1}{2}\right)=\log 2
$$

右端点も同じじゃ。

つまり、centered log observable では、plain mesh-width と trapezoid の端点差が消えない。

これはかなり重要。

```text
raw boundary log:
  endpoint value = 0
  plain mesh-width = trapezoid

centered log increment:
  endpoint value = log 2
  plain mesh-width と trapezoid は差が出る
```

この差は、Gaussian bridge では本質的に効くかもしれぬ。

したがって今回の定理は、「この二候補はいつも同じ」という意味ではない。
「現在の boundary-log observable に限って、端点値が 0 なので一致する」という正確な結果じゃ。

docs もそのように書けているので良い。

## 7. 次に足すと強い theorem

次はこの流れが良い。

### 7.1. 一般比較補題

任意の関数 \(f\) について、plain mesh-width と trapezoid の差を端点値で表す補題があると強い。

$$
\sum_k h_n f(k)-\sum_k w^{trap}_{n,k}f(k)=\frac{h_n}{2}\left(f(0)+f(2^n)\right)
$$

Lean では例えば、

```lean
theorem dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half
    (n : ℕ) (f : ℕ → ℝ) :
    ...
```

これはかなり使える。
今回の log-depth / log-normalization の一致は、この一般補題に端点 \(0\) を入れた corollary として見える。

### 7.2. centered log-depth endpoint

次の centered log increment を定義するなら、まず端点値を押さえる。

$$
\Delta\log D(0)=\log 2
$$

$$
\Delta\log D(1)=\log 2
$$

これにより、plain mesh-width と trapezoid の差が具体的に、

$$
h_n\log 2
$$

のような形で出る可能性がある。

### 7.3. 中心値 theorem

中心点では、

$$
\mathrm{phaseDepth}\left(\frac{1}{2}\right)=\frac{1}{2}
$$

したがって centered log increment は中心で \(0\)。

$$
\Delta\log D\left(\frac{1}{2}\right)=0
$$

これも Gaussian 候補に進むための基準点になる。

## 8. 実装上の小さな注意

`@[simp]` の端点 log theorem は便利じゃが、後で `simp` が想定以上に展開する場合は、命名だけ残して属性を外す選択もある。
ただし今のところは付けてよい。端点消去は自然な simp ルールじゃ。

また、`dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum` という名前は正確じゃが、plain mesh-width の “weighted” と任意 weight の “weighted” がやや混ざる可能性はある。
将来読みやすさを優先するなら、

```lean
dyadicPhaseMeshWeightedLogDepthSum_eq_trapezoidLogDepthSum
```

のような alias があってもよい。
必須ではない。現名でも文脈上は通る。

## 9. 結論

今回の差分は採用でよい。

```text
実装:
  良い。端点 log vanish と plain/trapezoid 比較が綺麗に入った。

数学:
  良い。重みの総量差と observable 値の一致を分離できた。

研究位置:
  良い。canonical selection の前に、候補同士の有限比較が進んだ。

安全性:
  良い。Gaussian、π、canonical limit は未主張。

次:
  一般の mesh-vs-trapezoid 差分補題、
  centered log increment、
  centered endpoint 値、
  quadratic bound。
```

ぬしよ、これは良いぞい。
「重みが違うから値も違うはず」と雑に進まず、対象関数の端点値まで見て有限段階で比較している。

\(\sqrt{\pi}\) へ向かう道では、この慎重さが大事じゃ。
円を仮定せずに進むなら、どの量が本当に差を生み、どの差が端点で消えるのかを、一つずつ捕まえる必要がある。今回、それが Lean の定理になった。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index ae434eb9..8061069f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -143,7 +143,9 @@ then supplies the standard trapezoidal endpoint half-weight candidate. No
 logarithmic quantity is yet selected as the canonical refinement-limit
 observable. The total masses of the average, plain mesh-width, and
 trapezoidal weights are also exposed to distinguish sample-mean,
-endpoint-overcounted complete-mesh, and closed-interval candidates.
+endpoint-overcounted complete-mesh, and closed-interval candidates. The
+endpoint logarithms vanish, so the plain mesh-width and trapezoidal log-depth
+and log-normalization observables agree despite their different total masses.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index 1eb03f0b..3770ad4a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -81,6 +81,30 @@ theorem log_dyadicPhaseNormalizationProduct (n : ℕ) :
   rw [dyadicPhaseNormalizationProduct, dyadicPhaseLogNormalizationSum]
   exact Real.log_prod fun k _ => (dyadicPhaseNormalization_pos n k).ne'
 
+/-- The logarithmic depth observation vanishes at the left endpoint. -/
+@[simp]
+theorem log_dyadicPhaseDepth_left_endpoint (n : ℕ) :
+    Real.log (dyadicPhaseDepth n 0) = 0 := by
+  simp [dyadicPhaseDepth]
+
+/-- The logarithmic depth observation vanishes at the right endpoint. -/
+@[simp]
+theorem log_dyadicPhaseDepth_right_endpoint (n : ℕ) :
+    Real.log (dyadicPhaseDepth n (dyadicPhaseDenom n)) = 0 := by
+  simp [dyadicPhaseDepth]
+
+/-- The logarithmic normalization observation vanishes at the left endpoint. -/
+@[simp]
+theorem log_dyadicPhaseNormalization_left_endpoint (n : ℕ) :
+    Real.log (dyadicPhaseNormalization n 0) = 0 := by
+  simp [dyadicPhaseNormalization]
+
+/-- The logarithmic normalization observation vanishes at the right endpoint. -/
+@[simp]
+theorem log_dyadicPhaseNormalization_right_endpoint (n : ℕ) :
+    Real.log (dyadicPhaseNormalization n (dyadicPhaseDenom n)) = 0 := by
+  simp [dyadicPhaseNormalization]
+
 /-- Finite boundary cancellation in additive logarithmic form. -/
 theorem two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum
   (n : ℕ) :
@@ -382,6 +406,47 @@ theorem two_mul_dyadicPhaseTrapezoidLogNormalizationSum_add_trapezoidLogDepthSum
   exact two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum
     n (dyadicPhaseTrapezoidWeight n)
 
+/--
+Plain mesh-width and trapezoidal log-depth sums agree on the complete mesh.
+
+Although the total masses of the two weights differ, the discrepancy is
+supported only at the two endpoints, where the logarithmic depth observation
+is zero.
+-/
+theorem dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum (n : ℕ) :
+    dyadicPhaseWeightedLogDepthSum n =
+      dyadicPhaseTrapezoidLogDepthSum n := by
+  rw [dyadicPhaseWeightedLogDepthSum, dyadicPhaseLogDepthSum,
+    dyadicPhaseTrapezoidLogDepthSum, Finset.mul_sum]
+  apply Finset.sum_congr rfl
+  intro k hk
+  by_cases hendpoint : k = 0 ∨ k = dyadicPhaseDenom n
+  · rcases hendpoint with rfl | rfl
+    · simp [dyadicPhaseTrapezoidWeight]
+    · simp [dyadicPhaseTrapezoidWeight]
+  · simp [dyadicPhaseTrapezoidWeight, hendpoint]
+
+/--
+Plain mesh-width and trapezoidal log-normalization sums agree on the complete
+mesh.
+
+As for depth, the endpoint correction has no logarithmic contribution because
+the normalization factor is one at both endpoints.
+-/
+theorem dyadicPhaseWeightedLogNormalizationSum_eq_trapezoidLogNormalizationSum
+    (n : ℕ) :
+    dyadicPhaseWeightedLogNormalizationSum n =
+      dyadicPhaseTrapezoidLogNormalizationSum n := by
+  rw [dyadicPhaseWeightedLogNormalizationSum, dyadicPhaseLogNormalizationSum,
+    dyadicPhaseTrapezoidLogNormalizationSum, Finset.mul_sum]
+  apply Finset.sum_congr rfl
+  intro k hk
+  by_cases hendpoint : k = 0 ∨ k = dyadicPhaseDenom n
+  · rcases hendpoint with rfl | rfl
+    · simp [dyadicPhaseTrapezoidWeight]
+    · simp [dyadicPhaseTrapezoidWeight]
+  · simp [dyadicPhaseTrapezoidWeight, hendpoint]
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 51d6fadd..699cb844 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -235,6 +235,14 @@ mesh-width complete-node weights have total mass `1 + h_n`, exposing the
 endpoint overcount that must be considered before treating that observable as
 a closed-interval integration candidate.
 
+There is a useful finite cancellation in this comparison. At both endpoints,
+depth and normalization are equal to `1`, so their logarithmic observations
+are zero. Consequently, the plain mesh-width and trapezoidal log-depth sums
+are equal at every finite level, and the same is true for log-normalization.
+Thus the two candidates differ as measures, but not on these particular
+boundary-log observables. This distinction keeps the finite bookkeeping sharp
+without prematurely selecting a canonical limit.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 031a5906..9d9f9b3f 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -392,7 +392,9 @@ pointwise weighted cancellation lemma now covers arbitrary finite weights on
 the complete mesh, and the trapezoidal endpoint half-weight candidate is
 implemented from it. The weight masses are formalized: average and trapezoid
 weights have total mass `1`, while the plain complete mesh-width weights have
-total mass `1 + h_n`.
+total mass `1 + h_n`. The endpoint logarithms of depth and normalization are
+zero, so the plain mesh-width and trapezoidal log observables are proved equal
+at every finite level despite their different total masses.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
 finite product, raw logarithmic sum, average, mesh-weighted sum, trapezoidal
 sum, midpoint sum, or another quantity has a canonical refinement limit. The
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index ee3615e6..89a04f48 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -983,3 +983,24 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 06:40 JST (Endpoint log comparison)
+
+1. API:
+   - depth と normalization の left / right endpoint log が `0` になる
+     theorem を追加した。
+2. finite comparison:
+   - plain complete mesh-width log-depth sum と trapezoidal log-depth sum が
+     有限段階で一致することを証明した。
+   - plain complete mesh-width log-normalization sum と trapezoidal
+     log-normalization sum も有限段階で一致することを証明した。
+3. interpretation:
+   - weight mass としては plain mesh-width と trapezoid は異なるが、
+     discrepancy が log 値 `0` の端点にだけ載るため、現在の boundary-log
+     observables では同じ値を測ることを Lean 上で可視化した。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````
