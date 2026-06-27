# Git diff / Report / Review

## Add: Analysis.DkReal.SemanticCF2DNormalize

gch: 7cc8dd7a4e2f51f60e90e470affd6a0e58925678

## Report

境界正規化の第一段階を実装しました。

[SemanticCF2DNormalize.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean)

実装内容:

- `phaseNormalization t = 1 / sqrt (phaseDepth t)`
- 補正係数の正値性・非零性・連続性・折返し対称性
- `normalizedPhaseEdge`
- 始点・終点の保存
- core-zero における全実数パラメータでの
  `q2 (normalizedPhaseEdge r z t) = q2 z`
- normalized edge の連続性

これで一本の直線遷移を、円や角度を導入せず固定 `q2` 境界へ戻せました。次はこれを4相へ作用移送し、boundary-valued closed path を構成します。

検証:

- `lake build DkMath.Analysis`: 成功、8288 jobs
- `git diff --check`: 成功

## Review

うむ。これはかなり重要な checkpoint じゃ。
今回は「折れ線的な連続四相」から、ついに **一本の遷移を固定 \(q2\) 境界へ戻す段階** に入った。`SemanticCF2DNormalize.lean` が追加され、`phaseNormalization t = 1 / sqrt (phaseDepth t)`、正値性・非零性・連続性、`normalizedPhaseEdge`、端点則、そして core-zero での `q2` 保存まで証明されている。

## 状況解説

前段では affine edge

$$
E(z,t)=(1-t)z+tA(z)
$$

を作り、その \(q2\) profile が

$$
q2(E(z,t))=\operatorname{phaseDepth}(t),q2(z)
$$

になるところまで来ていた。

ただし、この \(E(z,t)\) は途中で固定 \(q2\) 境界を離れる。
今回の更新では、その離脱係数を平方根で補正した。

$$
\operatorname{phaseNormalization}(t)=\frac{1}{\sqrt{\operatorname{phaseDepth}(t)}}
$$

そして、

$$
N(z,t)=\operatorname{phaseNormalization}(t),E(z,t)
$$

として、正規化 edge を作った。

結果として、

$$
q2(N(z,t))=q2(z)
$$

が全実数パラメータ \(t\) で成立した。これは大きい。

## 何が強いか

ここで初めて、連続遷移が **固定 \(q2\) 境界上に戻った**。

しかも、円・角度・三角関数をまだ導入していない。

流れはこうじゃ。

```text id="4sxsz2"
離散四相
-> affine edge
-> q2 境界欠損 profile
-> positive sqrt correction
-> fixed-q2 normalized edge
```

ここで「円に沿って動く」とはまだ言っていない。
言えるのは、

```text id="ordd2x"
二次境界からの離脱を測り、
その正値 profile の平方根で補正すると、
元の q2 境界へ戻る
```

ということじゃ。

これは非常に DkMath らしい。

## 実装レビュー

`phaseNormalization_pos`、`sqrt_phaseDepth_ne_zero`、`continuous_phaseNormalization` が入ったのは正しい。

特に、`phaseDepth` はすでに

$$
\frac12\le \operatorname{phaseDepth}(t)
$$

を持っているので、平方根も割り算も安全に使える。
この「正値性を先に証明してから割る」順序がよい。

`normalizedPhaseEdge_zero` と `normalizedPhaseEdge_one` で端点が保存されるのも重要じゃ。

$$
N(z,0)=z
$$

$$
N(z,1)=A(z)
$$

なので、正規化しても seam 構造を壊さない。
これは次の四相 translate に効く。

## 数学的な意味

今回の本質は、こう言える。

```text id="lj7ql1"
直線で進むと q2 境界から沈む。
沈み方は phaseDepth で完全に分かる。
phaseDepth は常に正なので、平方根補正ができる。
その補正により、直線由来の遷移が固定 q2 境界上の連続遷移へ変わる。
```

ここに「曲線を前提にしない曲線生成」の核がある。

最初から曲線を置いたのではない。
直線遷移を作り、その欠損を測り、補正した結果として、境界上の連続遷移が出てくる。

これは「円以前」の思想に完全に沿っている。

## 気になる点

大きな問題は見えぬ。
ただ、次に進む前に、補助補題を少し足すと後が楽になる。

たとえば、

```lean id="8dlvdi"
phaseNormalization_sq_mul_phaseDepth
```

内容は、

```text id="x49zn0"
phaseNormalization t ^ 2 * phaseDepth t = 1
```

または逆向きの

```text id="ftquyd"
phaseDepth t * phaseNormalization t ^ 2 = 1
```

じゃな。

今は `normalizedPhaseEdge_q2_of_core_eq_zero` の中で直接処理しているが、この補題を外に出しておくと、四相 translate や future normalization で再利用しやすい。

また、

```lean id="06k4or"
Vec.q2_smul
```

のようなスカラー倍補題があると、今後かなり綺麗になる。

$$
q2(cz)=c^2q2(z)
$$

これを一般補題にしておけば、normalized edge の証明も構造的になる。

## 次の自然な実装

次は報告通り、

```text id="egf9ij"
normalized edge を四相へ action translate する
```

段階じゃな。

構成は affine のときと同じでよい。

```text id="tjziz0"
normalizedPhaseEdgeAt r z k t
  := (semanticAct r)^[k] (normalizedPhaseEdge r z t)
```

期待する theorem は、

```text id="17vfq1"
始点:
  normalizedPhaseEdgeAt r z k 0 = A^k z

終点:
  normalizedPhaseEdgeAt r z k 1 = A^(k+1) z

seam:
  edge k の終点 = edge k+1 の始点

q2:
  q2(normalizedPhaseEdgeAt r z k t) = q2 z

4周期:
  normalizedPhaseEdgeAt r z (k+4) t = normalizedPhaseEdgeAt r z k t
```

ここまでできれば、次に `Path` 化して、**boundary-valued closed four-phase path** が作れる。

## \(\pi\) への道としての位置

この更新は、\(\pi\) 計画にもかなり重要じゃ。

なぜなら、今回の補正係数はまさに

$$
\frac{1}{\sqrt{\operatorname{phaseDepth}(t)}}
$$

であり、平方根補正が自然に出てきたからじゃ。

ただし、まだここでは \(\pi\) は出ていない。
今あるのは、

```text id="sv3g32"
局所的な二次境界欠損
その平方根補正
固定 q2 境界への復帰
```

まで。

ここから先に、反復細分化、補正係数の積、極限、Gaussian bridge が必要になる。
`Real.pi` との握手はまだ焦らぬでよい。だが、握手へ向かう補正因子は、かなり自然に現れ始めている。

## 総評

今回の更新は非常に良い。

到達点を一言で言えば、

```text id="jd86df"
一本の直線遷移を、円や角度を使わず、固定 q2 境界上の連続遷移へ正規化した。
```

これはかなり強い。

次に四本へ移送して閉じれば、

```text id="8euq5q"
pre-geometric fixed-q2 closed path
```

が得られる。

その段階で、初めて「これは後から Euclidean circle として読める」と言える。
いまの積み方はとても堅い。焦らず、この順でよい。
うむ。これはかなり重要な checkpoint じゃ。
今回は「折れ線的な連続四相」から、ついに **一本の遷移を固定 \(q2\) 境界へ戻す段階** に入った。`SemanticCF2DNormalize.lean` が追加され、`phaseNormalization t = 1 / sqrt (phaseDepth t)`、正値性・非零性・連続性、`normalizedPhaseEdge`、端点則、そして core-zero での `q2` 保存まで証明されている。

## 状況解説

前段では affine edge

$$
E(z,t)=(1-t)z+tA(z)
$$

を作り、その \(q2\) profile が

$$
q2(E(z,t))=\operatorname{phaseDepth}(t),q2(z)
$$

になるところまで来ていた。

ただし、この \(E(z,t)\) は途中で固定 \(q2\) 境界を離れる。
今回の更新では、その離脱係数を平方根で補正した。

$$
\operatorname{phaseNormalization}(t)=\frac{1}{\sqrt{\operatorname{phaseDepth}(t)}}
$$

そして、

$$
N(z,t)=\operatorname{phaseNormalization}(t),E(z,t)
$$

として、正規化 edge を作った。

結果として、

$$
q2(N(z,t))=q2(z)
$$

が全実数パラメータ \(t\) で成立した。これは大きい。

## 何が強いか

ここで初めて、連続遷移が **固定 \(q2\) 境界上に戻った**。

しかも、円・角度・三角関数をまだ導入していない。

流れはこうじゃ。

```text id="4sxsz2"
離散四相
-> affine edge
-> q2 境界欠損 profile
-> positive sqrt correction
-> fixed-q2 normalized edge
```

ここで「円に沿って動く」とはまだ言っていない。
言えるのは、

```text id="ordd2x"
二次境界からの離脱を測り、
その正値 profile の平方根で補正すると、
元の q2 境界へ戻る
```

ということじゃ。

これは非常に DkMath らしい。

## 実装レビュー

`phaseNormalization_pos`、`sqrt_phaseDepth_ne_zero`、`continuous_phaseNormalization` が入ったのは正しい。

特に、`phaseDepth` はすでに

$$
\frac12\le \operatorname{phaseDepth}(t)
$$

を持っているので、平方根も割り算も安全に使える。
この「正値性を先に証明してから割る」順序がよい。

`normalizedPhaseEdge_zero` と `normalizedPhaseEdge_one` で端点が保存されるのも重要じゃ。

$$
N(z,0)=z
$$

$$
N(z,1)=A(z)
$$

なので、正規化しても seam 構造を壊さない。
これは次の四相 translate に効く。

## 数学的な意味

今回の本質は、こう言える。

```text id="lj7ql1"
直線で進むと q2 境界から沈む。
沈み方は phaseDepth で完全に分かる。
phaseDepth は常に正なので、平方根補正ができる。
その補正により、直線由来の遷移が固定 q2 境界上の連続遷移へ変わる。
```

ここに「曲線を前提にしない曲線生成」の核がある。

最初から曲線を置いたのではない。
直線遷移を作り、その欠損を測り、補正した結果として、境界上の連続遷移が出てくる。

これは「円以前」の思想に完全に沿っている。

## 気になる点

大きな問題は見えぬ。
ただ、次に進む前に、補助補題を少し足すと後が楽になる。

たとえば、

```lean id="8dlvdi"
phaseNormalization_sq_mul_phaseDepth
```

内容は、

```text id="x49zn0"
phaseNormalization t ^ 2 * phaseDepth t = 1
```

または逆向きの

```text id="ftquyd"
phaseDepth t * phaseNormalization t ^ 2 = 1
```

じゃな。

今は `normalizedPhaseEdge_q2_of_core_eq_zero` の中で直接処理しているが、この補題を外に出しておくと、四相 translate や future normalization で再利用しやすい。

また、

```lean id="06k4or"
Vec.q2_smul
```

のようなスカラー倍補題があると、今後かなり綺麗になる。

$$
q2(cz)=c^2q2(z)
$$

これを一般補題にしておけば、normalized edge の証明も構造的になる。

## 次の自然な実装

次は報告通り、

```text id="egf9ij"
normalized edge を四相へ action translate する
```

段階じゃな。

構成は affine のときと同じでよい。

```text id="tjziz0"
normalizedPhaseEdgeAt r z k t
  := (semanticAct r)^[k] (normalizedPhaseEdge r z t)
```

期待する theorem は、

```text id="17vfq1"
始点:
  normalizedPhaseEdgeAt r z k 0 = A^k z

終点:
  normalizedPhaseEdgeAt r z k 1 = A^(k+1) z

seam:
  edge k の終点 = edge k+1 の始点

q2:
  q2(normalizedPhaseEdgeAt r z k t) = q2 z

4周期:
  normalizedPhaseEdgeAt r z (k+4) t = normalizedPhaseEdgeAt r z k t
```

ここまでできれば、次に `Path` 化して、**boundary-valued closed four-phase path** が作れる。

## \(\pi\) への道としての位置

この更新は、\(\pi\) 計画にもかなり重要じゃ。

なぜなら、今回の補正係数はまさに

$$
\frac{1}{\sqrt{\operatorname{phaseDepth}(t)}}
$$

であり、平方根補正が自然に出てきたからじゃ。

ただし、まだここでは \(\pi\) は出ていない。
今あるのは、

```text id="sv3g32"
局所的な二次境界欠損
その平方根補正
固定 q2 境界への復帰
```

まで。

ここから先に、反復細分化、補正係数の積、極限、Gaussian bridge が必要になる。
`Real.pi` との握手はまだ焦らぬでよい。だが、握手へ向かう補正因子は、かなり自然に現れ始めている。

## 総評

今回の更新は非常に良い。

到達点を一言で言えば、

```text id="jd86df"
一本の直線遷移を、円や角度を使わず、固定 q2 境界上の連続遷移へ正規化した。
```

これはかなり強い。

次に四本へ移送して閉じれば、

```text id="8euq5q"
pre-geometric fixed-q2 closed path
```

が得られる。

その段階で、初めて「これは後から Euclidean circle として読める」と言える。
いまの積み方はとても堅い。焦らず、この順でよい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index ff4e1d2f..83664cc0 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -15,6 +15,7 @@ import DkMath.Analysis.DkReal
 import DkMath.Analysis.DkReal.SemanticCF2D
 import DkMath.Analysis.DkReal.SemanticCF2DPhase
 import DkMath.Analysis.DkReal.SemanticCF2DPath
+import DkMath.Analysis.DkReal.SemanticCF2DNormalize
 
 #print "file: DkMath.Analysis"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 2d329370..8b0d72f6 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -105,6 +105,12 @@ affine edge as a Mathlib `Path`. Four seam-compatible edges concatenate to a
 closed continuous piecewise-affine path under the core-zero action. This path
 is not yet normalized to a fixed `q2` boundary.
 
+[IMPLEMENTED: semantic-cf2d-normalized-edge]
+`DkReal.SemanticCF2DNormalize` divides one affine edge by the positive square
+root of `phaseDepth`. The resulting edge is continuous, has the same
+endpoints, and remains on the initial `q2` boundary for every real parameter
+under the core-zero action.
+
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 785f95a3..faee5cde 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1321,9 +1321,14 @@ lower bound of one half.
 packages each compatible edge as a Mathlib `Path` and concatenates four edges
 into a closed piecewise-affine loop. It is not yet a fixed-`q2` boundary path.
 
-[TODO: semantic-cf2d-phase/boundary-normalization] In a separate analytic
-module, normalize the affine edge by its positive `q2` profile and prove that
-the normalized path stays on the original boundary.
+[IMPLEMENTED: semantic-cf2d-phase/boundary-normalization]
+`SemanticCF2DNormalize` normalizes one affine edge by the positive square root
+of its `q2` profile and proves that the resulting continuous edge stays on the
+original boundary.
+
+[TODO: semantic-cf2d-phase/normalized-four-path] Transport the normalized edge
+through all four action phases and concatenate the resulting boundary-valued
+paths into a closed path.
 
 [TODO: semantic-cf2d-phase/euclidean-interpretation] Only after normalization,
 identify the fixed-`q2` path with the standard Euclidean circle model and
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
new file mode 100644
index 00000000..c0c023e9
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
@@ -0,0 +1,143 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2DPath
+import Mathlib.Analysis.SpecialFunctions.Sqrt
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DNormalize"
+
+/-!
+# Boundary normalization of one affine phase
+
+The affine phase edge is continuous but leaves its initial `q2` boundary by
+the exact positive factor `phaseDepth t`. This module removes that scalar
+defect:
+
+`normalizedPhaseEdge r z t = (1 / sqrt (phaseDepth t)) * semanticPhaseEdge r z t`.
+
+For a semantic core-zero kernel, the normalized edge has the same `q2` value
+as `z` at every real parameter. This is the first boundary-valued continuous
+transition, still without a circle, angle, or trigonometric parametrization.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+open DkMath.CosmicFormula.Rotation.CF2D
+
+noncomputable section
+
+/-- The positive scalar that returns an affine phase point to its `q2` boundary. -/
+def phaseNormalization (t : ℝ) : ℝ :=
+  1 / Real.sqrt (phaseDepth t)
+
+/-- The square root of phase depth is strictly positive. -/
+theorem sqrt_phaseDepth_pos (t : ℝ) :
+    0 < Real.sqrt (phaseDepth t) :=
+  Real.sqrt_pos.2 (phaseDepth_pos t)
+
+/-- The square root used for normalization never vanishes. -/
+theorem sqrt_phaseDepth_ne_zero (t : ℝ) :
+    Real.sqrt (phaseDepth t) ≠ 0 :=
+  (sqrt_phaseDepth_pos t).ne'
+
+/-- Phase normalization is strictly positive. -/
+theorem phaseNormalization_pos (t : ℝ) :
+    0 < phaseNormalization t :=
+  one_div_pos.mpr (sqrt_phaseDepth_pos t)
+
+/-- The normalization factor begins at one. -/
+@[simp]
+theorem phaseNormalization_zero :
+    phaseNormalization 0 = 1 := by
+  simp [phaseNormalization]
+
+/-- The normalization factor ends at one. -/
+@[simp]
+theorem phaseNormalization_one :
+    phaseNormalization 1 = 1 := by
+  simp [phaseNormalization]
+
+/-- The normalization factor inherits the midpoint reflection symmetry. -/
+@[simp]
+theorem phaseNormalization_one_sub (t : ℝ) :
+    phaseNormalization (1 - t) = phaseNormalization t := by
+  simp [phaseNormalization]
+
+/-- Phase depth is a continuous scalar profile. -/
+theorem continuous_phaseDepth :
+    Continuous phaseDepth := by
+  unfold phaseDepth
+  fun_prop
+
+/-- The positive normalization factor varies continuously. -/
+theorem continuous_phaseNormalization :
+    Continuous phaseNormalization := by
+  unfold phaseNormalization
+  exact continuous_const.div
+    (Real.continuous_sqrt.comp continuous_phaseDepth)
+    sqrt_phaseDepth_ne_zero
+
+/--
+Scale a CF2D state by the reciprocal square root of affine phase depth.
+-/
+def normalizedPhaseEdge
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
+  Vec.mk
+    (phaseNormalization t * (semanticPhaseEdge r z t).core)
+    (phaseNormalization t * (semanticPhaseEdge r z t).beam)
+
+/-- The normalized edge starts at the original state. -/
+@[simp]
+theorem normalizedPhaseEdge_zero
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    normalizedPhaseEdge r z 0 = z := by
+  cases z
+  simp [normalizedPhaseEdge]
+
+/-- The normalized edge ends at the next action state. -/
+@[simp]
+theorem normalizedPhaseEdge_one
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    normalizedPhaseEdge r z 1 = semanticAct r z := by
+  cases z
+  simp [normalizedPhaseEdge, semanticAct, UnitKernel.act, semanticUnitKernel,
+    semanticVec, Vec.star]
+
+/--
+For a core-zero kernel, normalization restores the original `q2` boundary at
+every parameter value.
+-/
+theorem normalizedPhaseEdge_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : ℝ) :
+    Vec.q2 (normalizedPhaseEdge r z t) = Vec.q2 z := by
+  have hsqrt_sq :
+      (Real.sqrt (phaseDepth t)) ^ 2 = phaseDepth t :=
+    Real.sq_sqrt (phaseDepth_nonneg t)
+  have hsqrt_ne := sqrt_phaseDepth_ne_zero t
+  rw [show Vec.q2 (normalizedPhaseEdge r z t) =
+      phaseNormalization t ^ 2 * Vec.q2 (semanticPhaseEdge r z t) by
+    simp [normalizedPhaseEdge, Vec.q2]
+    ring]
+  rw [semanticPhaseEdge_q2_of_core_eq_zero hcore]
+  unfold phaseNormalization
+  field_simp
+  rw [hsqrt_sq]
+
+/-- The normalized master edge is continuous. -/
+theorem continuous_normalizedPhaseEdge
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    Continuous (fun t : ℝ => normalizedPhaseEdge r z t) := by
+  rcases continuous_vec_iff.mp (continuous_semanticPhaseEdge r z) with
+    ⟨hcore, hbeam⟩
+  apply Continuous.vec_mk
+  · exact continuous_phaseNormalization.mul hcore
+  · exact continuous_phaseNormalization.mul hbeam
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 48d2e6db..7b1e5936 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -105,12 +105,13 @@ theorem, not inserted as notation.
 4. Core-zero exact order four closes the endpoint without Euclidean
    terminology.
 
-### Milestone B: boundary normalization
+### Milestone B: boundary normalization - one edge implemented
 
-1. Define the positive correction `1 / sqrt (phaseDepth t)`.
-2. Prove that the normalized edge preserves the original `q2` value.
-3. Prove continuity of the normalized edge.
-4. Prove compatibility of normalization with all four action translates.
+1. The positive correction `1 / sqrt (phaseDepth t)` is defined and continuous.
+2. The normalized master edge preserves the original `q2` value.
+3. The normalized master edge is continuous and has the original endpoints.
+4. Compatibility with all four action translates and their closed-path
+   concatenation remains to be implemented.
 
 ### Milestone C: refinement law
 
@@ -152,7 +153,6 @@ mechanism from which these theorem obligations can be investigated.
 
 ## Immediate Next Step
 
-The next implementation is boundary normalization of one affine edge. It must
-first prove the correction factor continuous and well-defined from the strict
-positivity of `phaseDepth`, then prove preservation of the original `q2`
-value. Refinement and limit arguments remain separate checkpoints.
+The next implementation transports the normalized edge through all four
+action phases and concatenates those boundary-valued paths into a closed path.
+Refinement and limit arguments remain separate checkpoints.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 79fb9957..242393c5 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -13,6 +13,10 @@ concatenation, and core-zero closed path are implemented in
 `DkMath.CosmicFormula.Rotation.CF2D.Topology` and
 `DkMath.Analysis.DkReal.SemanticCF2DPath`.
 
+The positive reciprocal-square-root correction, normalized master edge,
+endpoint laws, continuity, and fixed-`q2` theorem are implemented in
+`DkMath.Analysis.DkReal.SemanticCF2DNormalize`.
+
 The current implementation proves a four-state return:
 
 ```text
@@ -329,7 +333,8 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/half-fold-profile]
 [IMPLEMENTED: semantic-cf2d-phase/path-topology]
 [IMPLEMENTED: semantic-cf2d-phase/path-concatenation]
-[TODO: semantic-cf2d-phase/boundary-normalization]
+[IMPLEMENTED: semantic-cf2d-phase/boundary-normalization]
+[TODO: semantic-cf2d-phase/normalized-four-path]
 [TODO: semantic-cf2d-phase/refinement-law]
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 1e73b717..767870d7 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -609,3 +609,23 @@ Archive
    - 次段階を `phaseDepth` による boundary normalization とした。
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DPath` 成功 (8276 jobs)。
+
+### 2026/06/23 06:15 JST (Normalized boundary edge)
+
+1. 実装:
+   - `SemanticCF2DNormalize.lean` を新設した。
+   - `phaseNormalization t = 1 / sqrt (phaseDepth t)` を定義した。
+   - 平方根と補正係数の正値性、非零性、端点値、折返し対称性、連続性を
+     証明した。
+2. normalized edge:
+   - `normalizedPhaseEdge` を座標ごとのスカラー補正として定義した。
+   - affine edge と同じ始点・終点を持つことを証明した。
+   - core-zero 作用では全実数 parameter に対して
+     `q2 (normalizedPhaseEdge r z t) = q2 z` を証明した。
+   - normalized edge の連続性を証明した。
+3. 境界:
+   - 一本の edge の固定 `q2` 境界復帰までを今回の checkpoint とした。
+   - 四相 translate、seam、boundary-valued closed path は次段階とした。
+4. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DNormalize` 成功
+     (8277 jobs)。
````
`````
