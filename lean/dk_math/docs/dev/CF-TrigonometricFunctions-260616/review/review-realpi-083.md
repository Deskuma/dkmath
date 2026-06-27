# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DComposition

gch: 6bee544b27d6dad9d8f5c3e8a34336033183ffd4

## Report

finite composition API を補強しました。

- depth / normalization product の非零性
- 双方向の reciprocal equation
- 短い別名 `dyadicPhaseFiniteBoundaryCancellation`
- 文書と履歴を同期

`lake build DkMath.Analysis` 成功（8293 jobs）、警告なし、`git diff --check` 成功です。

## Review

うむ、これは **finite composition API の整備差分** として良い。
新しい数学的主張を増やしたというより、既に証明済みの有限 cancellation law を、後続で使いやすい形に展開した差分じゃな。

## 1. 総評

今回の差分は採用でよい。

前回の主定理はこれだった。

$$
\mathrm{NormalizationProduct}(n)^2\cdot\mathrm{DepthProduct}(n)=1
$$

今回追加されたのは、この有限恒等式を後続の代数操作で使いやすくする API じゃ。

```text id="vdolcb"
追加内容:
  product の nonzero theorem
  reciprocal equation 2 方向
  短名 theorem
  docs / history 同期
```

これは、次の `LogComposition` や `correction-limit-selection` へ進む前の下ごしらえとしてかなり良い。

## 2. 数学的な意味

正値性はすでにあった。

$$
0<\mathrm{NormalizationProduct}(n)
$$

$$
0<\mathrm{DepthProduct}(n)
$$

そこから今回、非零性を明示した。

$$
\mathrm{NormalizationProduct}(n)\ne 0
$$

$$
\mathrm{DepthProduct}(n)\ne 0
$$

これは逆数変形や `Real.log` の導入で効く。

そして cancellation law から、双方向の reciprocal equation が出た。

$$
\mathrm{NormalizationProduct}(n)^2=\mathrm{DepthProduct}(n)^{-1}
$$

$$
\mathrm{DepthProduct}(n)=\left(\mathrm{NormalizationProduct}(n)^2\right)^{-1}
$$

これにより、finite boundary restoration が「積で 1 になる」だけでなく、「互いが逆数として釣り合う」と読めるようになった。

## 3. 実装レビュー

`dyadicPhaseNormalizationProduct_ne_zero` と `dyadicPhaseDepthProduct_ne_zero` は素直で良い。

```lean id="wnbdt0"
theorem dyadicPhaseNormalizationProduct_ne_zero (n : ℕ) :
    dyadicPhaseNormalizationProduct n ≠ 0 :=
  (dyadicPhaseNormalizationProduct_pos n).ne'
```

この形は短く、後続で `field_simp` や inverse 変形を使うときにも便利じゃ。

reciprocal theorem も良い。

```lean id="2t4yj8"
theorem dyadicPhaseNormalizationProduct_sq_eq_inv_depthProduct (n : ℕ) :
    dyadicPhaseNormalizationProduct n ^ 2 =
      (dyadicPhaseDepthProduct n)⁻¹ := by
  exact eq_inv_of_mul_eq_one_left
    (dyadicPhaseNormalizationProduct_sq_mul_depthProduct n)
```

```lean id="1skcuv"
theorem dyadicPhaseDepthProduct_eq_inv_normalizationProduct_sq (n : ℕ) :
    dyadicPhaseDepthProduct n =
      (dyadicPhaseNormalizationProduct n ^ 2)⁻¹ := by
  exact eq_inv_of_mul_eq_one_right
    (dyadicPhaseNormalizationProduct_sq_mul_depthProduct n)
```

ビルド成功しているので方向も問題なし。
証明も既存 cancellation law から直接導いており、余計な仮定を足していない。

短名 theorem も良い。

```lean id="irz6gd"
theorem dyadicPhaseFiniteBoundaryCancellation (n : ℕ) :
    dyadicPhaseNormalizationProduct n ^ 2 *
        dyadicPhaseDepthProduct n = 1 :=
  dyadicPhaseNormalizationProduct_sq_mul_depthProduct n
```

これは docs や後続ファイルで読みやすくなる。
長い theorem 名は実装上正確で、短名は研究文脈で使いやすい。両方あるのは良い判断じゃ。

## 4. 研究テーマとの関係

今回の差分は、直接 Gaussian limit や \(\sqrt{\pi}\) に進んだわけではない。
しかし、そこへ向かう準備として重要じゃ。

最終目標は、外部から Gaussian integral を借りて \(\sqrt{\pi}\) を置くのではなく、CF2D 内部の normalization composition から独立な正規化定数を作り、後で `Real.pi` と同定することじゃったな。

その観点では、今回の API は次に効く。

```text id="q2ltl6"
nonzero:
  逆数操作に必要

positivity:
  log を取るために必要

reciprocal form:
  depth 側と normalization 側のどちらを主観測量にするか選べる

short alias:
  後続の finite / limit theorem で読みやすい
```

特に log-sum へ進むなら、正値性と非零性は必須になる。

各点の関係を log に移すと、目標形はこうなる。

$$
2\log(\mathrm{NormalizationProduct}(n))+\log(\mathrm{DepthProduct}(n))=0
$$

これはまだ今回の差分では証明していない。
だが、そのための前提 API が揃いつつある。

## 5. 気になる点

大きな問題はない。
ただし、今後の拡張で気をつけるべき点はある。

### 5.1. reciprocal form は canonical observable を選んでいない

docs にもある通り、今回も新しい limit observable は選択していない。これは正しい。

finite cancellation law があるからといって、

```text id="jb0q9e"
raw product が canonical limit である
```

とはまだ言えぬ。

今の段階では、単に有限 mesh 上で pointwise restoration law を掛け合わせたもの。
この慎重さは維持した方がよい。

### 5.2. log 導入時は product positivity より pointwise positivity が重要

product の正値性は便利じゃが、log sum を項ごとに定義するなら必要なのは各項の正値性じゃ。

すでに `phaseDepth_pos` と `phaseNormalization_pos` があるので問題はないはず。
ただ、次に `LogComposition` を作るなら、次のような theorem があると使いやすい。

```lean id="k5s7zx"
theorem dyadicPhaseDepth_pos (n k : ℕ) :
    0 < dyadicPhaseDepth n k
```

```lean id="h4yaj7"
theorem dyadicPhaseNormalization_pos (n k : ℕ) :
    0 < dyadicPhaseNormalization n k
```

既存の `phaseDepth_pos (dyadicPhaseNode n k)` を直接使えば済むが、dyadic 名で包んでおくと後続が読みやすくなる。

## 6. 次に足すと強いもの

次の小補題としては、平方 product の正値性が便利じゃ。

$$
0<\mathrm{NormalizationProduct}(n)^2
$$

Lean なら、

```lean id="u0ku2k"
theorem dyadicPhaseNormalizationProduct_sq_pos (n : ℕ) :
    0 < dyadicPhaseNormalizationProduct n ^ 2 := by
  positivity
```

また、逆数の正値性もあるとよい。

$$
0<\mathrm{DepthProduct}(n)^{-1}
$$

$$
0<\left(\mathrm{NormalizationProduct}(n)^2\right)^{-1}
$$

ただし、これは必要になってからでよい。

本命は次の `LogComposition` じゃな。

```lean id="sfigyx"
def dyadicPhaseLogDepthSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n, Real.log (dyadicPhaseDepth n k)

def dyadicPhaseLogNormalizationSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n, Real.log (dyadicPhaseNormalization n k)
```

最初の主定理候補はこれ。

$$
2\cdot\mathrm{LogNormalizationSum}_n+\mathrm{LogDepthSum}_n=0
$$

ただし、Lean では `Real.log_mul`、`Real.log_pow`、正値性の仮定処理が少し面倒になる。
今回の nonzero / positivity API は、その前準備として効く。

## 7. 結論

この差分は良い。

```text id="n9j277"
実装:
  良い。既存 finite cancellation law の利用形を増やしている。

数学:
  良い。finite boundary restoration を reciprocal balance として読める。

安全性:
  良い。新しい limit observable は選んでいない。

次:
  dyadic pointwise positivity wrappers、
  log-depth / log-normalization finite sums、
  log cancellation law。
```

ぬしよ、これは派手な一歩ではないが、重要な舗装じゃ。
\(\sqrt{\pi}\) へ向かう道では、いきなり Gaussian を叫ぶより、こういう nonzero、reciprocal、log 前提を固める方が強い。

有限積の「戻し」が、逆数として扱えるようになった。
次はその逆数関係を log の加法会計へ移す段階じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index f7b87c48..c8d10ce4 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -129,6 +129,8 @@ noncomputable.
 complete finite dyadic mesh. The squared normalization product exactly
 cancels the depth product, and both products are strictly positive. This is a
 finite pointwise-composition theorem, not a selected infinite-product limit.
+Nonvanishing and reciprocal forms are also exposed for downstream finite
+algebra.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DComposition.lean
index 4d7fe237..4dd42101 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DComposition.lean
@@ -68,6 +68,42 @@ theorem dyadicPhaseDepthProduct_pos (n : ℕ) :
   intro k hk
   exact phaseDepth_pos (dyadicPhaseNode n k)
 
+/-- The finite normalization product never vanishes. -/
+theorem dyadicPhaseNormalizationProduct_ne_zero (n : ℕ) :
+    dyadicPhaseNormalizationProduct n ≠ 0 :=
+  (dyadicPhaseNormalizationProduct_pos n).ne'
+
+/-- The finite depth product never vanishes. -/
+theorem dyadicPhaseDepthProduct_ne_zero (n : ℕ) :
+    dyadicPhaseDepthProduct n ≠ 0 :=
+  (dyadicPhaseDepthProduct_pos n).ne'
+
+/--
+The squared finite normalization product is the reciprocal of the finite
+depth product.
+-/
+theorem dyadicPhaseNormalizationProduct_sq_eq_inv_depthProduct (n : ℕ) :
+    dyadicPhaseNormalizationProduct n ^ 2 =
+      (dyadicPhaseDepthProduct n)⁻¹ := by
+  exact eq_inv_of_mul_eq_one_left
+    (dyadicPhaseNormalizationProduct_sq_mul_depthProduct n)
+
+/--
+The finite depth product is the reciprocal of the squared finite
+normalization product.
+-/
+theorem dyadicPhaseDepthProduct_eq_inv_normalizationProduct_sq (n : ℕ) :
+    dyadicPhaseDepthProduct n =
+      (dyadicPhaseNormalizationProduct n ^ 2)⁻¹ := by
+  exact eq_inv_of_mul_eq_one_right
+    (dyadicPhaseNormalizationProduct_sq_mul_depthProduct n)
+
+/-- Short name for the finite boundary-cancellation law. -/
+theorem dyadicPhaseFiniteBoundaryCancellation (n : ℕ) :
+    dyadicPhaseNormalizationProduct n ^ 2 *
+        dyadicPhaseDepthProduct n = 1 :=
+  dyadicPhaseNormalizationProduct_sq_mul_depthProduct n
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index a62881b6..70e87139 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -380,7 +380,8 @@ children introduced at that level is exactly `1 / (2 * 2^n)`.
 [IMPLEMENTED: semantic-cf2d-phase/finite-correction-composition]
 On the complete finite dyadic mesh, the squared product of sampled
 normalizations exactly cancels the product of sampled depths. Both products
-are strictly positive.
+are strictly positive and nonzero, and the cancellation law is available in
+both reciprocal forms.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
 finite product, logarithmic sum, or another quantity has a canonical
 refinement limit. The finite cancellation theorem alone does not select one.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index c597e674..bac4143c 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -883,3 +883,17 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DComposition` 成功
      (8280 jobs)。
+
+### 2026/06/23 20:32 JST (Finite composition reciprocal API)
+
+1. API:
+   - depth product と normalization product の nonzero theorem を追加した。
+   - finite cancellation law を双方の reciprocal equation に変換した。
+   - 後続文書向けに `dyadicPhaseFiniteBoundaryCancellation` という短い
+     theorem 名を追加した。
+2. boundary:
+   - 新たな limit observable は選択していない。既存 finite identity の
+     利用形のみを整備した。
+3. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DComposition` 成功
+     (8280 jobs)。
````
`````
