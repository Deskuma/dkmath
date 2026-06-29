# Git diff / Report / Review

## Add: Analysis.DkReal.SemanticCF2DComposition

gch: 9caa2bce92f49f2b6c46b1abc49a57e08c415d21

## Report

次の checkpoint を完了しました。

- `SemanticCF2DComposition.lean` を新設
- 完全な有限 dyadic mesh を定義
- depth product・normalization product を定義
- `(normalization product)² * depth product = 1` を証明
- 両積の厳密正値性を証明
- 無限積や canonical limit は未選択として明記

`lake build DkMath.Analysis` 成功（8293 jobs）、警告なし、`git diff --check` 成功です。

p.s. D.: 一部、警告の修正も含む。

```txt
warning: DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean:313:2:
'simp [euclideanPlaneComplexIsometry, quarterTurnLinearIsometry, quarterTurnLinearEquiv,
 pairToEuclideanPlane, euclideanPlaneToPair, OrthonormalBasis.equiv]' is a flexible tactic modifying '⊢'.
Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.
```

## Review

うむ、これはかなり良い checkpoint じゃ。
今回で `SemanticCF2D*` 系の流れは、次の段階まで到達しておる。

```text
Dyadic mesh
  ↓
finite depth refinement
  ↓
finite defect aggregation
  ↓
elementary depth limit
  ↓
finite normalization composition
```

報告では、`SemanticCF2DComposition.lean` を新設し、完全な有限 dyadic mesh、depth product、normalization product、有限積での cancellation、両積の正値性を証明し、無限積や canonical limit は未選択として明記している。さらに `lake build DkMath.Analysis` 成功、警告なし、`git diff --check` 成功とのことじゃ。

## 1. 総評

今回の差分は **採用でよい** 。

特に強いのは、depth 側の加法的 defect 会計とは別に、normalization 側を **乗法的な有限 composition** として分離した点じゃ。

depth 側では、すでにこういう加法会計ができていた。

$$
\mathrm{totalDefect}_n=\left(\frac{1}{2}\right)^{n+1}
$$

$$
\mathrm{cumulativeDefect}_m=1-\left(\frac{1}{2}\right)^m
$$

一方、normalization 側では各点で、

$$
\mathrm{normalization}(t)^2\cdot\mathrm{depth}(t)=1
$$

これを有限 mesh 全体へ積として運び、

$$
\mathrm{NormalizationProduct}(n)^2\cdot\mathrm{DepthProduct}(n)=1
$$

まで閉じた。

これは、非常に自然な分離じゃ。

```text
depth defect:
  加法的に集約する

boundary normalization:
  乗法的に合成する
```

この二本が同じ dyadic mesh 上で並び始めた。これは解析層としてかなり良い形じゃよ。

## 2. 数学的な意味

今回の新定理の核はこれじゃ。

$$
\left(\prod_{k=0}^{2^n}\mathrm{normalization}*{n,k}\right)^2
\cdot
\left(\prod*{k=0}^{2^n}\mathrm{depth}_{n,k}\right)=1
$$

ここで mesh は両端点を含むので、index は \(0\) から \(2^n\) まで。
つまり、点数は \(2^n+1\) 個じゃ。

これは各 node の点wise identity を有限積へ持ち上げただけ、と言えばそれまでじゃ。
しかし、形式化上はかなり大事じゃ。

なぜなら、ここで初めて **boundary-restoration law が有限 mesh 全体で閉じる** と言えるようになったからじゃ。

前段までの depth defect は、odd child の局所平均との差や、level ごとの加法的な会計だった。
今回の composition は、各点の depth を normalization が正確に戻すという形で、mesh 全体に transport される。

つまり、

```text
局所:
  normalization² が depth を打ち消す

有限 mesh:
  normalization product² が depth product を打ち消す
```

という綺麗な持ち上げになっておる。

## 3. 実装レビュー

`dyadicPhaseNodeIndices` は良い。

```lean
def dyadicPhaseNodeIndices (n : ℕ) : Finset ℕ :=
  Finset.range (dyadicPhaseDenom n + 1)
```

両端点込みの complete mesh として明確じゃ。
Refinement 側の odd-child 集約では parent interval が \(2^n\) 個だったので `range (dyadicPhaseDenom n)`。
Composition 側では sampled node が \(2^n+1\) 個なので `range (dyadicPhaseDenom n + 1)`。

この違いがちゃんと出ているのは良い。

`dyadicPhaseDepthProduct` と `dyadicPhaseNormalizationProduct` も素直じゃ。

```lean
def dyadicPhaseDepthProduct (n : ℕ) : ℝ :=
  ∏ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseDepth n k
```

```lean
def dyadicPhaseNormalizationProduct (n : ℕ) : ℝ :=
  ∏ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseNormalization n k
```

`dyadicPhaseNormalization_sq_mul_depth` は点wise theorem の dyadic sample 版。
ここを明示したのは、後続で使いやすい。

有限積の theorem も良い。

```lean
theorem dyadicPhaseNormalizationProduct_sq_mul_depthProduct (n : ℕ) :
    dyadicPhaseNormalizationProduct n ^ 2 *
        dyadicPhaseDepthProduct n = 1 := by
  rw [dyadicPhaseNormalizationProduct, dyadicPhaseDepthProduct,
    ← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib]
  simp [dyadicPhaseNormalization_sq_mul_depth]
```

この証明は短く、狙いが明確じゃ。
`prod_pow` と `prod_mul_distrib` で、点wise law を積へ押し上げている。

正値性 theorem も良い。

```lean
theorem dyadicPhaseNormalizationProduct_pos (n : ℕ) :
    0 < dyadicPhaseNormalizationProduct n
```

```lean
theorem dyadicPhaseDepthProduct_pos (n : ℕ) :
    0 < dyadicPhaseDepthProduct n
```

これは後で log を取りたくなる場合にも重要になる。
もちろん今は log sum を選択していないが、正値性があることで、その道を安全に開いた状態になる。

## 4. computability boundary の整理も良い

今回、`dyadicPhaseNode` を `noncomputable def` にしたのは良い判断じゃ。

差分では、`SemanticCF2DDyadic` の module comment に「mesh indices と denominator は computable naturals だが、node は `Real` division を使うので semantic-real module は noncomputable」と明記されている。さらに、計算可能 mesh が必要なら rational nodes を保持し、別 bridge で `Real` へ移す設計だと整理されている。

これは DkReal 設計としてかなり大事じゃ。

```text
semantic-real mesh:
  Real division を使うので noncomputable

future computable mesh:
  rational node を保持してから Real bridge へ渡す
```

この分離は正しい。

`SemanticCF2DLimit` の `noncomputable section` を外したのも良い。
定理だけで新しい noncomputable definition を導入しないなら、section を外せる。
一方、import 先の real-valued definitions は noncomputable のまま。ここも docs で説明できている。

## 5. 警告修正について

`EuclideanPhase.lean` の flexible tactic warning を `simp only` へ展開して潰したのは、ビルド衛生として良い。
ただし、この種の `simp only` はリストが長くなりがちで、将来 Mathlib 側の内部名や simp lemma の変化にやや弱くなる。

現在の変更は警告を消す目的として妥当じゃ。
ただ、将来的にはこの theorem の証明を小さな補助補題に分けると、さらに安定する可能性がある。

例えば、`pairToEuclideanPlane` / `euclideanPlaneToPair` の評価補題を別に置く。
あるいは、`quarterTurnLinearIsometry` の complex map を直接計算する補助 theorem を作る。

今すぐ修正必須ではない。
警告なしビルドを優先した今回の対応は十分よい。

## 6. 気になる点

大きな問題はない。
ただし、次の注意点はある。

### 6.1. complete mesh product は canonical observable ではまだない

docs でも明記されている通り、今回の product は「同じ有限 mesh 上で点wise identity を掛け合わせたもの」じゃ。
これ自体は正しいが、これが refinement の canonical observable かどうかは、まだ別問題じゃ。

なぜなら、mesh が細かくなるほど点数が増えるため、単純な product は sampling density に強く依存する。
つまり、次に問うべきはこれじゃ。

```text
何を refinement limit の対象にするのか？
```

候補は複数ある。

```text
1. raw product
2. normalized product
3. log average
4. weighted product
5. endpoint を半重みにする台形則型 product
6. odd-child だけの correction product
7. depth defect と対応する局所 normalization product
```

今回の theorem は、そのどれも選ばずに「有限積 cancellation だけ」を証明している。
これは正しい。

### 6.2. endpoint の扱いは次で効く

`dyadicPhaseNodeIndices` は両端点込みじゃ。
点wise identity の product ならこれで問題ない。

しかし、将来 log sum や Riemann-sum 的なものへ行くなら、endpoint の重みが問題になる。
台形則なら端点は半重み、midpoint rule なら endpoint は入らない。
depth defect の odd-child 集約は interval 中心寄りだった。

ゆえに次の段階では、mesh type を複数定義してもよい。

```lean
def dyadicPhaseClosedNodeIndices
def dyadicPhaseInteriorNodeIndices
def dyadicPhaseOddChildIndices
def dyadicPhaseParentIntervalIndices
```

今すぐ必要ではないが、composition-limit selection へ進むなら効いてくる。

### 6.3. theorem 名は良いが、alias があると読みやすい

現在の主定理名は、

```lean
dyadicPhaseNormalizationProduct_sq_mul_depthProduct
```

十分に明確じゃ。
ただ、後続の文脈では「finite cancellation law」と呼びたいはずなので、alias theorem を置くのもありじゃ。

```lean
theorem dyadicPhaseFiniteBoundaryCancellation (n : ℕ) :
    dyadicPhaseNormalizationProduct n ^ 2 *
        dyadicPhaseDepthProduct n = 1 :=
  dyadicPhaseNormalizationProduct_sq_mul_depthProduct n
```

これは必須ではない。
ただ、docs や後続ファイルで読みやすくなる。

## 7. 次に足すと強い theorem

まずは今回の product の逆関係があると便利じゃ。
正値性があるので、次が出せる。

$$
\mathrm{DepthProduct}(n)=\left(\mathrm{NormalizationProduct}(n)^2\right)^{-1}
$$

Lean なら例えば、

```lean
theorem dyadicPhaseDepthProduct_eq_inv_normProduct_sq (n : ℕ) :
    dyadicPhaseDepthProduct n =
      (dyadicPhaseNormalizationProduct n ^ 2)⁻¹ := by
  ...
```

または、

$$
\mathrm{NormalizationProduct}(n)^2=\mathrm{DepthProduct}(n)^{-1}
$$

の形も良い。

```lean
theorem dyadicPhaseNormalizationProduct_sq_eq_inv_depthProduct (n : ℕ) :
    dyadicPhaseNormalizationProduct n ^ 2 =
      (dyadicPhaseDepthProduct n)⁻¹ := by
  ...
```

正値性があるので、順序付きの形も作れる。

$$
0<\mathrm{DepthProduct}(n)
$$

$$
0<\mathrm{NormalizationProduct}(n)
$$

これはすでにある。次は非ゼロ版が便利じゃ。

```lean
theorem dyadicPhaseDepthProduct_ne_zero (n : ℕ) :
    dyadicPhaseDepthProduct n ≠ 0
```

```lean
theorem dyadicPhaseNormalizationProduct_ne_zero (n : ℕ) :
    dyadicPhaseNormalizationProduct n ≠ 0
```

これらは逆数変形で効く。

## 8. 次の研究課題

今回で finite composition は閉じた。
次は「limit selection」じゃ。

ここは焦らず、候補を並べて finite theorem を比較するべきじゃな。

わっちなら、次の順で進める。

```text
1. raw product の挙動を数値観測
2. log product を finite sum として定義
3. log average を定義
4. endpoint weighting の有無を比較
5. odd-child correction product を別定義
6. depth additive defect との対応を探す
```

特に重要なのは、pointwise law を log にすると、

$$
2\log(\mathrm{normalization}(t))+\log(\mathrm{depth}(t))=0
$$

となることじゃ。

ただし、log を導入するには正値性が必要。
今回、両 product の正値性を入れたのは、その準備として非常に良い。

まだ log sum を選んではいない。
だが、選べる条件は整え始めている。ここが賢い。

## 9. 研究物語としての意味

これはかなり面白い。

これまで見えていたものは、depth 側の「くぼみ」だった。
odd child は親平均との差として、有限 defect を持つ。

今回、normalization 側では、その depth を点ごとに回復する係数があって、それを finite mesh 全体で掛けても、完全に cancellation することがわかった。

つまり物語としてはこうじゃ。

```text
Depth:
  境界から沈む。くぼみが現れる。

Normalization:
  沈みを戻す。境界を復元する。

Finite mesh:
  その復元は各点だけでなく、有限観測全体でも閉じる。
```

これは良い。
pre-geometric な「手で形を探る観測過程」が、ついに有限 mesh 全体の保存会計に入った。

ただし、まだ「どの finite product を極限対象として採用するか」は決まっていない。
この未決定性を docs に残しているのは、非常に良い研究態度じゃ。

## 10. 結論

今回の差分は採用でよい。

```text
実装:
  良い。Finite composition が独立モジュールとして綺麗に切れている。

数学:
  良い。点wise normalization law を finite mesh product へ運んだ。

設計:
  良い。noncomputable semantic mesh と future rational mesh の境界が整理された。

安全性:
  良い。infinite product、log sum、canonical limit を未選択としている。

次:
  inverse 形、nonzero 補題、mesh variants、log/weighted/normalized product 候補の比較。
```

ぬしよ、これはかなり良い進捗じゃ。
depth 側では「くぼみの加法会計」が閉じ、normalization 側では「復元の乗法会計」が閉じた。

この二つがそろったことで、次はいよいよ「どの会計が真に幾何へ収束するのか」を選ぶ段階じゃな。
ここは急がず、有限法則を並べて、嘘をつかぬ候補だけを残すのがよい。賢狼の鼻は、ここで役に立つはずじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index 1a2fd259..8ef8383d 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -17,6 +17,7 @@ import DkMath.Analysis.DkReal.SemanticCF2DPhase
 import DkMath.Analysis.DkReal.SemanticCF2DDyadic
 import DkMath.Analysis.DkReal.SemanticCF2DRefinement
 import DkMath.Analysis.DkReal.SemanticCF2DLimit
+import DkMath.Analysis.DkReal.SemanticCF2DComposition
 import DkMath.Analysis.DkReal.SemanticCF2DPath
 import DkMath.Analysis.DkReal.SemanticCF2DNormalize
 import DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index dd3d7e5d..f7b87c48 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -102,7 +102,9 @@ half-fold symmetry without introducing circles or angles.
 [IMPLEMENTED: semantic-cf2d-dyadic] `DkReal.SemanticCF2DDyadic` samples one
 phase at the finite nodes `k / 2^n`. Endpoint, unit-interval, reflection,
 even-child, odd-child midpoint, and reflected phase-depth laws are proved
-without selecting a correction product or taking a limit.
+without selecting a correction product or taking a limit. This semantic-real
+mesh is noncomputable because its nodes use division in `Real`; a future
+computable variant should retain rational nodes before crossing the bridge.
 
 [IMPLEMENTED: semantic-cf2d-finite-refinement]
 `DkReal.SemanticCF2DRefinement` evaluates depth and normalization on the
@@ -118,6 +120,15 @@ the per-level and cumulative scales. The total defect introduced at level
 `n + 1` is `(1/2)^(n+1)` and tends to zero. The cumulative defect through
 levels `0, ..., m-1` is exactly `1 - (1/2)^m` and tends to one. These are
 elementary geometric limits, not Gaussian or `pi` identifications.
+The limit module itself introduces only theorems and therefore needs no
+`noncomputable section`, while its imported real-valued definitions remain
+noncomputable.
+
+[IMPLEMENTED: semantic-cf2d-finite-composition]
+`DkReal.SemanticCF2DComposition` samples depth and normalization on the same
+complete finite dyadic mesh. The squared normalization product exactly
+cancels the depth product, and both products are strictly positive. This is a
+finite pointwise-composition theorem, not a selected infinite-product limit.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DComposition.lean
new file mode 100644
index 00000000..4d7fe237
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DComposition.lean
@@ -0,0 +1,73 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2DRefinement
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DComposition"
+
+/-!
+# Finite composition of dyadic boundary corrections
+
+At every real phase parameter, normalization satisfies
+
+`phaseNormalization t ^ 2 * phaseDepth t = 1`.
+
+This module restricts that identity to a finite dyadic mesh and composes it
+multiplicatively. The resulting theorem is a finite cancellation law. It
+does not assert that this product is the canonical refinement limit, and it
+does not introduce an infinite product, logarithmic sum, or Gaussian weight.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+noncomputable section
+
+/-- All dyadic phase-node indices at level `n`, including both endpoints. -/
+def dyadicPhaseNodeIndices (n : ℕ) : Finset ℕ :=
+  Finset.range (dyadicPhaseDenom n + 1)
+
+/-- Product of the sampled phase depths over the complete finite mesh. -/
+def dyadicPhaseDepthProduct (n : ℕ) : ℝ :=
+  ∏ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseDepth n k
+
+/-- Product of the sampled boundary normalizations over the complete mesh. -/
+def dyadicPhaseNormalizationProduct (n : ℕ) : ℝ :=
+  ∏ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseNormalization n k
+
+/-- Pointwise dyadic normalization cancels the corresponding sampled depth. -/
+theorem dyadicPhaseNormalization_sq_mul_depth (n k : ℕ) :
+    dyadicPhaseNormalization n k ^ 2 * dyadicPhaseDepth n k = 1 := by
+  exact phaseNormalization_sq_mul_phaseDepth (dyadicPhaseNode n k)
+
+/--
+The squared finite normalization product exactly cancels the finite depth
+product on the same dyadic mesh.
+-/
+theorem dyadicPhaseNormalizationProduct_sq_mul_depthProduct (n : ℕ) :
+    dyadicPhaseNormalizationProduct n ^ 2 *
+        dyadicPhaseDepthProduct n = 1 := by
+  rw [dyadicPhaseNormalizationProduct, dyadicPhaseDepthProduct,
+    ← Finset.prod_pow]
+  rw [← Finset.prod_mul_distrib]
+  simp [dyadicPhaseNormalization_sq_mul_depth]
+
+/-- The finite normalization product is strictly positive. -/
+theorem dyadicPhaseNormalizationProduct_pos (n : ℕ) :
+    0 < dyadicPhaseNormalizationProduct n := by
+  apply Finset.prod_pos
+  intro k hk
+  exact phaseNormalization_pos (dyadicPhaseNode n k)
+
+/-- The finite depth product is strictly positive. -/
+theorem dyadicPhaseDepthProduct_pos (n : ℕ) :
+    0 < dyadicPhaseDepthProduct n := by
+  apply Finset.prod_pos
+  intro k hk
+  exact phaseDepth_pos (dyadicPhaseNode n k)
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean
index 6c382e86..677dd3be 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean
@@ -20,18 +20,23 @@ at
 The endpoint, reflection, and parent-child laws are exact algebraic
 identities. No infinite product, logarithmic correction, Gaussian weight, or
 identification with `pi` is assumed here.
+
+Although the mesh indices and denominator are computable naturals, the node
+is valued in `Real` and uses real division. Consequently this semantic-real
+module is noncomputable. A computable mesh should instead retain rational
+nodes and cross to `Real` through a separate bridge.
 -/
 
 namespace DkMath.Analysis.DkNNRealQ
 
-noncomputable section
+-- noncomputable section
 
 /-- The number of equal subintervals in the `n`th dyadic phase partition. -/
 def dyadicPhaseDenom (n : ℕ) : ℕ :=
   2 ^ n
 
 /-- The `k`th real node of the `n`th dyadic phase partition. -/
-def dyadicPhaseNode (n k : ℕ) : ℝ :=
+noncomputable def dyadicPhaseNode (n k : ℕ) : ℝ :=
   (k : ℝ) / (dyadicPhaseDenom n : ℝ)
 
 /-- Every dyadic phase denominator is strictly positive. -/
@@ -108,6 +113,6 @@ theorem phaseDepth_dyadic_reflect
       phaseDepth (dyadicPhaseNode n k) := by
   rw [dyadicPhaseNode_reflect hk, phaseDepth_one_sub]
 
-end
+-- end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLimit.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLimit.lean
index f4842799..f9dc9e30 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLimit.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLimit.lean
@@ -23,8 +23,6 @@ normalization.
 
 namespace DkMath.Analysis.DkNNRealQ
 
-noncomputable section
-
 /-- The total depth defect introduced at one refinement level tends to zero. -/
 theorem tendsto_totalDyadicPhaseDepthDefect_zero :
     Filter.Tendsto totalDyadicPhaseDepthDefect Filter.atTop (nhds 0) := by
@@ -56,6 +54,4 @@ theorem tendsto_cumulativeDyadicPhaseDepthDefect_one :
     exact cumulativeDyadicPhaseDepthDefect_eq m
   · norm_num
 
-end
-
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
index 53996ef1..d9519388 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DRefinement.lean
@@ -20,6 +20,10 @@ The key new identity concerns an odd child. Since `phaseDepth` is quadratic,
 its value at the midpoint of adjacent parent nodes is their average depth
 minus an explicit positive mesh correction. This is a finite algebraic
 refinement law, not an asymptotic or Gaussian statement.
+
+These observations inherit noncomputability from the real-valued dyadic node
+and, for normalization, from real square root. Their formulas remain exact;
+computability requires a separate rational observation layer.
 -/
 
 namespace DkMath.Analysis.DkNNRealQ
@@ -141,6 +145,12 @@ theorem totalDyadicPhaseDepthDefect_eq_pow (n : ℕ) :
     totalDyadicPhaseDepthDefect n = (1 / 2 : ℝ) ^ (n + 1) := by
   simp [totalDyadicPhaseDepthDefect, dyadicPhaseDenom, pow_succ]
 
+/-- Every per-level total depth defect is strictly positive. -/
+theorem totalDyadicPhaseDepthDefect_pos (n : ℕ) :
+    0 < totalDyadicPhaseDepthDefect n := by
+  rw [totalDyadicPhaseDepthDefect_eq_pow]
+  positivity
+
 /--
 The cumulative depth defect through the first `m` refinement levels.
 
@@ -162,6 +172,26 @@ theorem cumulativeDyadicPhaseDepthDefect_eq (m : ℕ) :
         rfl, ih, totalDyadicPhaseDepthDefect_eq_pow]
       ring
 
+/-- The unrecovered depth after `m` levels is exactly the dyadic tail. -/
+theorem one_sub_cumulativeDyadicPhaseDepthDefect_eq (m : ℕ) :
+    1 - cumulativeDyadicPhaseDepthDefect m = (1 / 2 : ℝ) ^ m := by
+  rw [cumulativeDyadicPhaseDepthDefect_eq]
+  ring
+
+/-- Every finite cumulative depth defect is nonnegative. -/
+theorem cumulativeDyadicPhaseDepthDefect_nonneg (m : ℕ) :
+    0 ≤ cumulativeDyadicPhaseDepthDefect m := by
+  rw [cumulativeDyadicPhaseDepthDefect_eq]
+  have hpow : (1 / 2 : ℝ) ^ m ≤ 1 := by
+    exact pow_le_one₀ (by norm_num) (by norm_num)
+  linarith
+
+/-- Every finite cumulative depth defect remains strictly below its limit one. -/
+theorem cumulativeDyadicPhaseDepthDefect_lt_one (m : ℕ) :
+    cumulativeDyadicPhaseDepthDefect m < 1 := by
+  rw [cumulativeDyadicPhaseDepthDefect_eq]
+  exact sub_lt_self _ (by positivity)
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 0b970de1..a78f93e5 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -177,6 +177,24 @@ structural: each new level becomes negligible, while all levels together
 retain a nonzero conserved account. No Gaussian or `pi` interpretation is
 attached to this geometric-series limit.
 
+The first finite normalization-composition theorem is now implemented in
+`SemanticCF2DComposition.lean`. At every sampled node,
+
+```text
+normalization^2 * depth = 1.
+```
+
+Multiplying this identity over the complete finite dyadic mesh gives
+
+```text
+(product normalization)^2 * product depth = 1.
+```
+
+Both finite products are strictly positive. This is an exact transport of the
+pointwise boundary-restoration law through finite multiplication. It does not
+yet identify either product as the canonical refinement observable, nor does
+it justify an infinite product or logarithmic limit.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index d73526ae..a62881b6 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -364,7 +364,9 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/dyadic-refinement]
 `SemanticCF2DDyadic` defines the finite nodes `k / 2^n`, proves their endpoint,
 unit-interval, reflection, even-child, odd-child midpoint, and reflected
-phase-depth laws.
+phase-depth laws. Since the nodes use division in `Real`, this semantic mesh
+is noncomputable; a rational-node implementation remains a separate possible
+computable layer.
 [IMPLEMENTED: semantic-cf2d-phase/finite-depth-refinement]
 `SemanticCF2DRefinement` proves reflection and even-child inheritance for
 dyadic depth and normalization. Quadraticity gives the exact odd-child law:
@@ -375,10 +377,13 @@ children introduced at that level is exactly `1 / (2 * 2^n)`.
 [IMPLEMENTED: semantic-cf2d-phase/depth-limit] The per-level total is
 `(1/2)^(n+1)` and tends to zero. Its finite cumulative sum through level
 `m - 1` is `1 - (1/2)^m` and tends to one.
-[TODO: semantic-cf2d-phase/correction-composition] Select and prove an
-aggregate composition law for local boundary corrections. Do not assume that
-it is an infinite product or a logarithmic sum before its finite form is
-established.
+[IMPLEMENTED: semantic-cf2d-phase/finite-correction-composition]
+On the complete finite dyadic mesh, the squared product of sampled
+normalizations exactly cancels the product of sampled depths. Both products
+are strictly positive.
+[TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
+finite product, logarithmic sum, or another quantity has a canonical
+refinement limit. The finite cancellation theorem alone does not select one.
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
 ```
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index 2a628787..27565e4d 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -310,9 +310,20 @@ theorem euclideanPlaneOrientation_map_complex :
 theorem euclideanPlaneComplexIsometry_quarterTurn (v : EuclideanPlane) :
     euclideanPlaneComplexIsometry (quarterTurnLinearIsometry v) =
       Complex.I * euclideanPlaneComplexIsometry v := by
+  simp only [euclideanPlaneComplexIsometry, OrthonormalBasis.equiv, quarterTurnLinearIsometry,
+    quarterTurnLinearEquiv, pairToEuclideanPlane, euclideanPlaneToPair,
+    ContinuousLinearEquiv.finTwoArrow_apply, Fin.isValue, PiLp.continuousLinearEquiv_apply,
+    ContinuousLinearEquiv.finTwoArrow_symm_apply, PiLp.continuousLinearEquiv_symm_apply,
+    LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
+    LinearIsometryEquiv.trans_apply, Complex.orthonormalBasisOneI_repr_symm_apply,
+    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_refl, Equiv.refl_apply,
+    EuclideanSpace.basisFun_repr, Matrix.cons_val_zero, Complex.ofReal_neg, Matrix.cons_val_one,
+    Matrix.cons_val_fin_one]
+/- original simp
   simp [euclideanPlaneComplexIsometry, quarterTurnLinearIsometry,
     quarterTurnLinearEquiv, pairToEuclideanPlane, euclideanPlaneToPair,
     OrthonormalBasis.equiv]
+-/
   change
     (-(v 1 : ℂ) + (v 0 : ℂ) * Complex.I) =
       Complex.I * ((v 0 : ℂ) + (v 1 : ℂ) * Complex.I)
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 6ed04fbb..c597e674 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -847,3 +847,39 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLimit` 成功
      (8280 jobs)。
+
+### 2026/06/23 (Computability boundary correction)
+
+1. correction:
+   - `dyadicPhaseNode` は `Real` division を使用するため noncomputable
+     であることを再確認した。
+   - `SemanticCF2DDyadic` と、その real-valued definitions に依存する
+     `SemanticCF2DRefinement` に `noncomputable section` を維持した。
+2. boundary:
+   - `SemanticCF2DLimit` は theorem のみなので section 修飾を外しても
+     ビルド可能であることを確認した。
+   - computable mesh が必要な場合は rational nodes を保持し、別 bridge
+     で `Real` へ移す設計とする。
+3. supporting API:
+   - per-level defect の正値性、cumulative defect の非負性・1未満性、
+     および残差 `(1/2)^m` の厳密式を追加した。
+
+### 2026/06/23 19:48 JST (Finite normalization composition)
+
+1. module:
+   - `SemanticCF2DComposition.lean` を新設し、公開 Analysis entry point
+     へ追加した。
+2. finite observations:
+   - 両端点を含む complete dyadic mesh index を定義した。
+   - mesh 上の depth product と normalization product を定義した。
+3. composition:
+   - 各 node で `normalization^2 * depth = 1` を証明した。
+   - finite product 全体で
+     `(normalization product)^2 * depth product = 1` を証明した。
+   - 両 finite product の厳密正値性を証明した。
+4. boundary:
+   - この定理は pointwise cancellation の有限積版であり、canonical
+     refinement observable、infinite product、log sum を選択しない。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DComposition` 成功
+     (8280 jobs)。
````
`````
