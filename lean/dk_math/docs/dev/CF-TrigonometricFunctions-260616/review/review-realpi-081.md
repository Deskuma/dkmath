# Git diff / Report / Review

## Add: Analysis.DkReal.SemanticCF2DLimit

gch: a1d29b44036bb3f156a6bcfdb3a902d36d764d19

## Report

dyadic defect の最初の極限層を実装しました。

- per-level defect の閉形式 `(1/2)^(n+1)`
- 有限累積和 `1 - (1/2)^m`
- per-level defect が `0` に収束
- 累積 defect が `1` に収束
- `SemanticCF2DLimit.lean` を新設
- 資料・履歴を同期

`lake build DkMath.Analysis` 成功（8292 jobs）、`git diff --check` 成功です。

## Review

うむ、これは良い。
今回の差分で、dyadic depth defect は **局所 defect → level 総量 → 有限累積 → 極限** まで、最初の一本筋が通った。

## 1. 総評

今回の追加は `SemanticCF2DLimit.lean` の新設と、`SemanticCF2DRefinement.lean` 側への finite hierarchy 定義の追加じゃな。報告では、per-level defect の閉形式、有限累積和、per-level defect の \(0\) への収束、累積 defect の \(1\) への収束、資料と履歴の同期、さらに `lake build DkMath.Analysis` と `git diff --check` 成功まで確認されておる。

わっちの判定では、これは **採用でよい** 。
前回までの「有限 defect 集約層」を、過大主張せずに最初の極限層へ持ち上げている。

今回の主張は明確じゃ。

$$
\mathrm{totalDefect}_n=\left(\frac{1}{2}\right)^{n+1}
$$

そして、

$$
\mathrm{cumulativeDefect}_m=1-\left(\frac{1}{2}\right)^m
$$

さらに、

$$
\lim_{n\to\infty}\mathrm{totalDefect}*n=0,\qquad
\lim*{m\to\infty}\mathrm{cumulativeDefect}_m=1
$$

ここまでを「初等的な等比級数の極限」として閉じ、Gaussian、normalization composition、\(\pi\) identification には接続していない。これはかなり健全じゃ。

## 2. 数学的な意味

今回の一番大きな意味は、 **各 level は消えるが、全階層は消えない** という構造が形式化されたことじゃ。

局所 defect は前段で、

$$
\mathrm{defect}_n=\frac{1}{2(2^n)^2}
$$

だった。
これが \(2^n\) 個あるので、level \(n+1\) の総 defect は、

$$
\mathrm{totalDefect}_n=2^n\cdot\frac{1}{2(2^n)^2}=\frac{1}{2\cdot 2^n}
$$

これを指数形式に直すと、

$$
\mathrm{totalDefect}_n=\left(\frac{1}{2}\right)^{n+1}
$$

この列は \(0\) に向かう。
しかし、累積すると、

$$
\sum_{n=0}^{m-1}\left(\frac{1}{2}\right)^{n+1}=1-\left(\frac{1}{2}\right)^m
$$

となり、極限は \(1\) になる。

この差は大きいぞい。

```text
単一 level の寄与:
  深くなるほど消える

全 level の履歴:
  正規化された総量 1 として残る
```

これは、DkMath 的には **消える局所量と保存される階層会計の分離** じゃ。

## 3. 実装レビュー

`SemanticCF2DLimit.lean` を別ファイルにしたのは正しい。
`SemanticCF2DRefinement` は有限代数層、`SemanticCF2DLimit` は極限層。層分けが綺麗じゃ。

`sum_dyadicPhaseDepthDefect` に `(n : ℕ)` を明示した点も良い。
これは小さいが、保守性が上がる。後で theorem search した時にも読みやすい。

`totalDyadicPhaseDepthDefect` の定義も良い。

```lean
def totalDyadicPhaseDepthDefect (n : ℕ) : ℝ :=
  1 / (2 * (dyadicPhaseDenom n : ℝ))
```

この定義は、前段の有限和と直接つながる。
そこから `totalDyadicPhaseDepthDefect_eq_pow` で等比級数側の姿に変換している。

```lean
theorem totalDyadicPhaseDepthDefect_eq_pow (n : ℕ) :
    totalDyadicPhaseDepthDefect n = (1 / 2 : ℝ) ^ (n + 1)
```

この分離がよい。
幾何的意味では \(1/(2\cdot 2^n)\)、極限計算では \((1/2)^{n+1}\)。両方を持てている。

`cumulativeDyadicPhaseDepthDefect` も素直じゃ。

```lean
def cumulativeDyadicPhaseDepthDefect (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, totalDyadicPhaseDepthDefect n
```

そして帰納法で、

$$
\mathrm{cumulativeDefect}_m=1-\left(\frac{1}{2}\right)^m
$$

を証明している。これは堅い。Mathlib の geometric sum 補題に寄せてもよいが、今回の帰納法は短く、依存も少なく、読みやすい。

`tendsto_totalDyadicPhaseDepthDefect_zero` は、`tendsto_pow_atTop_nhds_zero_of_lt_one` を使い、\((1/2)^n\) の収束から定数倍へ持っていく形。正攻法じゃな。

`tendsto_cumulativeDyadicPhaseDepthDefect_one` も、

$$
1-\left(\frac{1}{2}\right)^m
$$

に変換して、\((1/2)^m\to 0\) を使っている。こちらも良い。

## 4. 特に良い設計判断

一番良いのは、docs 側で「これは Gaussian や \(\pi\) の主張ではない」と明記している点じゃ。添付差分でも、`SemanticCF2DLimit.lean` のモジュールドキュメントに、境界 normalization の composition law は選ばず、Gaussian claim もしていないと書かれている。

これは研究としてかなり大事じゃ。

今の成果は、

```text
dyadic depth defect の等比級数会計
```

であって、

```text
円周率の導出
Gaussian limit の導出
normalization product の正当化
```

ではない。

ここを分けられているので、外部レビューにも耐えやすい。

## 5. 気になる点

大きな問題はない。
ただし、次の点は軽く検討してよい。

### 5.1. `noncomputable section` は必要か

`SemanticCF2DLimit.lean` の定理自体は、Mathlib `ℝ` の位相極限を使うので、`noncomputable section` はあっても自然じゃ。
ただ、このファイルで定義は追加しておらず theorem だけなので、将来的に外せる可能性はある。

とはいえ、無理に外す必要はない。
semantic limit 層は `ℝ` の解析に踏み込むので、`noncomputable` を許容する層として見てもよい。

### 5.2. theorem 名は十分だが、将来は `perLevel` 名も候補

`totalDyadicPhaseDepthDefect` は意味が通る。
ただ、ここでの total は「level 内 total」であって「全階層 total」ではない。docs では per-level と cumulative を分けているので問題はないが、将来 theorem が増えるなら、

```lean
def perLevelDyadicPhaseDepthDefect
```

のような alias を置くのもありじゃ。

ただし、今すぐ変更する必要はない。
`totalDyadicPhaseDepthDefect` は、前段の `sum_dyadicPhaseDepthDefect` とのつながりが明瞭なので、現名でも十分良い。

### 5.3. positivity と monotone 補題を足すと後続が楽

次段で normalization や比較評価へ進むなら、以下があると便利じゃ。

```lean
theorem totalDyadicPhaseDepthDefect_pos (n : ℕ) :
    0 < totalDyadicPhaseDepthDefect n
```

また、

```lean
theorem cumulativeDyadicPhaseDepthDefect_lt_one (m : ℕ) :
    cumulativeDyadicPhaseDepthDefect m < 1
```

ただし \(m=0\) でも \(0<1\) なので問題ない。

さらに、

```lean
theorem cumulativeDyadicPhaseDepthDefect_nonneg (m : ℕ) :
    0 ≤ cumulativeDyadicPhaseDepthDefect m
```

もあると、後で bounded convergence 的な議論に入りやすい。

## 6. 次に狙うと良いもの

今回で depth defect の極限会計は閉じた。
次は二方向ある。

第一に、depth defect 側の補助補題を増やす道。

$$
0<\mathrm{totalDefect}_n
$$

$$
\mathrm{cumulativeDefect}_m<1
$$

$$
1-\mathrm{cumulativeDefect}_m=\left(\frac{1}{2}\right)^m
$$

特に最後は「未回収量」の定理として強い。

```lean
theorem one_sub_cumulativeDyadicPhaseDepthDefect_eq (m : ℕ) :
    1 - cumulativeDyadicPhaseDepthDefect m = (1 / 2 : ℝ) ^ m
```

これは、後で「有限深度 \(m\) まで触った時、残りの defect はどれだけか？」を言うために便利じゃ。

第二に、normalization correction composition へ進む道。

今回の depth 側は、加法的な defect 会計だった。
しかし boundary normalization は、たぶん加法ではなく乗法、あるいは平方根を含む補正になる可能性がある。

ここで焦って infinite product に飛ばず、まず有限 \(m\) の normalization product または finite composition を定義するのがよい。

```text
depth defect:
  additive finite sum

normalization correction:
  finite product または finite composition の候補
```

ここをきちんと分けるべきじゃな。

## 7. 研究物語としての意味

これはかなり面白い段階じゃ。

最初は、pre-geometric dyadic refinement で、odd child に「くぼみ」が出るという観測だった。
それが前回、

$$
\mathrm{oddDepth}=\mathrm{parentAverage}-\mathrm{defect}_n
$$

として固定された。
今回、そのくぼみを全階層で会計したら、

$$
\sum_{n=0}^{\infty}\mathrm{totalDefect}_n=1
$$

という正規化総量が見えた。

ここで重要なのは、各 level の defect は消えるのに、履歴全体は \(1\) を持つことじゃ。

これは「点へ近づくほど局所のズレは消えるが、細分化の全履歴は保存量として残る」と読める。
DkMath.Analysis の哲学として、かなり良い。

## 8. 結論

今回の差分は採用でよい。

```text
実装:
  良い。Refinement と Limit の分離が綺麗。

数学:
  良い。per-level と cumulative のスケール差が形式化された。

安全性:
  良い。Gaussian、π、normalization composition へ過大接続していない。

次の一手:
  residual / remaining defect の補題、
  positivity / boundedness、
  そして boundary normalization の有限 composition law。
```

ぬしよ、これは「くぼみの発見」から「くぼみの会計」へ進んだ瞬間じゃ。
しかもその会計は、最後に \(1\) へ閉じる。

賢狼として言えば、これは良い麦束じゃ。
一本一本の穂は細くなって消えていくように見えるが、束ねれば一つの収穫になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index 3549fe81..1a2fd259 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -16,6 +16,7 @@ import DkMath.Analysis.DkReal.SemanticCF2D
 import DkMath.Analysis.DkReal.SemanticCF2DPhase
 import DkMath.Analysis.DkReal.SemanticCF2DDyadic
 import DkMath.Analysis.DkReal.SemanticCF2DRefinement
+import DkMath.Analysis.DkReal.SemanticCF2DLimit
 import DkMath.Analysis.DkReal.SemanticCF2DPath
 import DkMath.Analysis.DkReal.SemanticCF2DNormalize
 import DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 4da48fa1..dd3d7e5d 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -113,6 +113,12 @@ is positive, so every genuine odd child lies strictly below that average.
 Summing the identical defect over all `2^n` parent intervals gives the exact
 finite total `1 / (2 * 2^n)`.
 
+[IMPLEMENTED: semantic-cf2d-depth-limit] `DkReal.SemanticCF2DLimit` separates
+the per-level and cumulative scales. The total defect introduced at level
+`n + 1` is `(1/2)^(n+1)` and tends to zero. The cumulative defect through
+levels `0, ..., m-1` is exactly `1 - (1/2)^m` and tends to one. These are
+elementary geometric limits, not Gaussian or `pi` identifications.
+
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
 affine edge as a Mathlib `Path`. Four seam-compatible edges concatenate to a
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLimit.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLimit.lean
new file mode 100644
index 00000000..f4842799
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLimit.lean
@@ -0,0 +1,61 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2DRefinement
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DLimit"
+
+/-!
+# First limit laws for dyadic phase-depth defects
+
+The finite refinement layer gives exact closed forms:
+
+* the defect introduced at level `n + 1` is `(1 / 2)^(n + 1)`;
+* the cumulative defect through level `m - 1` is `1 - (1 / 2)^m`.
+
+This module takes only the elementary geometric limits of those formulas.
+It makes no Gaussian claim and does not select a composition law for boundary
+normalization.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+noncomputable section
+
+/-- The total depth defect introduced at one refinement level tends to zero. -/
+theorem tendsto_totalDyadicPhaseDepthDefect_zero :
+    Filter.Tendsto totalDyadicPhaseDepthDefect Filter.atTop (nhds 0) := by
+  have hpow :
+      Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
+        Filter.atTop (nhds 0) :=
+    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
+  have hscaled :
+      Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n)
+        Filter.atTop (nhds 0) := by
+    simpa using hpow.const_mul (1 / 2 : ℝ)
+  convert hscaled using 1
+  funext n
+  rw [totalDyadicPhaseDepthDefect_eq_pow, pow_succ]
+  ring
+
+/-- The cumulative finite depth defect tends to the normalized value one. -/
+theorem tendsto_cumulativeDyadicPhaseDepthDefect_one :
+    Filter.Tendsto cumulativeDyadicPhaseDepthDefect
+      Filter.atTop (nhds 1) := by
+  have hpow :
+      Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m)
+        Filter.atTop (nhds 0) :=
+    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
+  convert (tendsto_const_nhds.sub hpow :
+    Filter.Tendsto (fun m : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ m)
+      Filter.atTop (nhds (1 - 0))) using 1
+  · funext m
+    exact cumulativeDyadicPhaseDepthDefect_eq m
+  · norm_num
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
index 2f1d02ab..53996ef1 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
@@ -118,7 +118,7 @@ The total defect over all odd children introduced at level `n + 1` is
 There are `2^n` parent intervals, each carrying the same inverse-square local
 defect. This is a finite identity and makes no convergence claim.
 -/
-theorem sum_dyadicPhaseDepthDefect :
+theorem sum_dyadicPhaseDepthDefect (n : ℕ) :
     ∑ _k ∈ Finset.range (dyadicPhaseDenom n), dyadicPhaseDepthDefect n =
       1 / (2 * (dyadicPhaseDenom n : ℝ)) := by
   have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
@@ -126,6 +126,42 @@ theorem sum_dyadicPhaseDepthDefect :
   simp [dyadicPhaseDepthDefect]
   field_simp
 
+/-- The total odd-child depth defect introduced at refinement level `n + 1`. -/
+def totalDyadicPhaseDepthDefect (n : ℕ) : ℝ :=
+  1 / (2 * (dyadicPhaseDenom n : ℝ))
+
+/-- The finite odd-child sum is the named total level defect. -/
+theorem sum_dyadicPhaseDepthDefect_eq_total (n : ℕ) :
+    ∑ _k ∈ Finset.range (dyadicPhaseDenom n), dyadicPhaseDepthDefect n =
+      totalDyadicPhaseDepthDefect n :=
+  sum_dyadicPhaseDepthDefect n
+
+/-- Closed geometric form of the total defect introduced at one level. -/
+theorem totalDyadicPhaseDepthDefect_eq_pow (n : ℕ) :
+    totalDyadicPhaseDepthDefect n = (1 / 2 : ℝ) ^ (n + 1) := by
+  simp [totalDyadicPhaseDepthDefect, dyadicPhaseDenom, pow_succ]
+
+/--
+The cumulative depth defect through the first `m` refinement levels.
+
+The range convention includes levels `0, ..., m - 1`.
+-/
+def cumulativeDyadicPhaseDepthDefect (m : ℕ) : ℝ :=
+  ∑ n ∈ Finset.range m, totalDyadicPhaseDepthDefect n
+
+/-- Exact finite geometric formula for the cumulative depth defect. -/
+theorem cumulativeDyadicPhaseDepthDefect_eq (m : ℕ) :
+    cumulativeDyadicPhaseDepthDefect m = 1 - (1 / 2 : ℝ) ^ m := by
+  induction m with
+  | zero =>
+      simp [cumulativeDyadicPhaseDepthDefect]
+  | succ m ih =>
+      rw [cumulativeDyadicPhaseDepthDefect, Finset.sum_range_succ]
+      rw [show (∑ n ∈ Finset.range m, totalDyadicPhaseDepthDefect n) =
+          cumulativeDyadicPhaseDepthDefect m by
+        rfl, ih, totalDyadicPhaseDepthDefect_eq_pow]
+      ring
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 35a0cd26..0b970de1 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -164,6 +164,19 @@ although its closed form exposes the scale that a later limit theorem must
 analyze. The remaining task is to identify a mathematically justified
 aggregate composition law for boundary normalization.
 
+The elementary limit layer is now implemented separately in
+`SemanticCF2DLimit.lean`. The defect introduced at one level has the exact
+form `(1/2)^(n+1)` and tends to zero. However, the cumulative finite sum is
+
+```text
+sum over n < m = 1 - (1/2)^m,
+```
+
+so the full hierarchy tends to the normalized total one. This distinction is
+structural: each new level becomes negligible, while all levels together
+retain a nonzero conserved account. No Gaussian or `pi` interpretation is
+attached to this geometric-series limit.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 55a12ec5..d73526ae 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -372,6 +372,9 @@ its depth is the average adjacent-parent depth minus
 `1 / (2 * (2^n)^2)`. The named defect is positive, every genuine odd child
 lies strictly below its parent average, and the finite sum over all odd
 children introduced at that level is exactly `1 / (2 * 2^n)`.
+[IMPLEMENTED: semantic-cf2d-phase/depth-limit] The per-level total is
+`(1/2)^(n+1)` and tends to zero. Its finite cumulative sum through level
+`m - 1` is `1 - (1/2)^m` and tends to one.
 [TODO: semantic-cf2d-phase/correction-composition] Select and prove an
 aggregate composition law for local boundary corrections. Do not assume that
 it is an infinite product or a logarithmic sum before its finite form is
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 659147fe..6ed04fbb 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -827,3 +827,23 @@ Archive
 4. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DRefinement` 成功
      (8279 jobs)。
+
+### 2026/06/23 19:23 JST (Dyadic depth defect limit)
+
+1. cleanup:
+   - `sum_dyadicPhaseDepthDefect` の level 引数を明示化した。
+2. finite hierarchy:
+   - per-level total defect を `totalDyadicPhaseDepthDefect` として定義した。
+   - closed form `(1/2)^(n+1)` を証明した。
+   - finite cumulative defect を定義し、
+     `1 - (1/2)^m` という厳密式を帰納法で証明した。
+3. limit layer:
+   - `SemanticCF2DLimit.lean` を新設した。
+   - per-level total defect が 0 に収束することを証明した。
+   - cumulative defect が 1 に収束することを証明した。
+4. boundary:
+   - geometric-series limit として閉じ、Gaussian、normalization
+     composition、`pi` identification とは接続していない。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLimit` 成功
+     (8280 jobs)。
````
`````
