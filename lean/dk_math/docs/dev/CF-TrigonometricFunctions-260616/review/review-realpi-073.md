# Git diff / Report / Review

## Add: CosmicFormula.Rotation.CF2D.EuclideanPhase

gch: a4ee9ff33d56001207b50c2b140eeb9d0273b11e

## Report

Euclidean circle 解釈の第一段階を実装しました。

[EuclideanPhase.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean)

追加内容:

- `EuclideanCircleSq rho2`
- `LevelSet ℝ rho2` との homeomorphism
- `Vec.q2_nonneg`
- `Vec.q2_eq_zero_iff`
- `Vec.q2_pos_iff_ne_zero`
- 零境界が原点一つへ退化する定理
- 既存 closed path の Euclidean coordinate-circle への写像

標準 `ℝ × ℝ` の積ノルムは L2 ではないため、安易な metric sphere 同一視は避けました。次は `EuclideanSpace ℝ (Fin 2)` の標準 sphere への橋です。

検証:

- `lake build DkMath.Analysis`: 成功、8289 jobs
- `git diff --check`: 成功

## Review

うむ。今回でついに **「これは円として読める」第一段階** に入った。
ただし、ここでも重要なのは、円を新しく作ったのではなく、すでに構成済みの `LevelSet ℝ rho2` 内部 path を、座標方程式 \(x^2+y^2=\rho2\) として解釈した、という順序じゃ。

## 状況解説

今回追加された `CF2D.EuclideanPhase.lean` は、pre-geometric 構成を Euclidean 側へ読むための第一橋じゃ。

中心はこの定義。

```lean
def EuclideanCircleSq (rho2 : ℝ) :=
  {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 = rho2}
```

ここでは半径ではなく、**半径二乗** \(\rho2\) を持っている。

これは良い判断じゃ。
なぜなら、既存の `q2` 境界は最初から

$$
q2(z)=\rho2
$$

として作られているから、平方根を先に持ち込まず、そのまま座標方程式へ写せる。

## 何が実装されたか

今回の大きな成果はこれ。

```lean
levelSetHomeomorphEuclideanCircleSq :
  LevelSet ℝ rho2 ≃ₜ EuclideanCircleSq rho2
```

つまり、CF2D の抽象的な `LevelSet ℝ rho2` と、明示的な座標方程式

$$
x^2+y^2=\rho2
$$

が homeomorphism で結ばれた。

これは「同じ点集合を別名で見る」だけではなく、連続構造も保っている。
したがって、既存の closed path をそのまま Euclidean coordinate-circle 側へ写せる。

今回追加された

```lean
normalizedClosedEuclideanCircleSqPath
```

はまさにそれじゃな。

重要なのは、path を再構成していないこと。
既存の

```lean
normalizedClosedLevelFourPhasePath
```

を homeomorphism で写している。

この順序は非常に正しい。

## zero boundary を分けたのが良い

今回、

```lean
Vec.q2_nonneg
Vec.q2_eq_zero_iff
Vec.q2_pos_iff_ne_zero
euclideanCircleSq_zero_eq_origin
```

が追加されたのも良い。

これは、次の橋で必ず効く。

$$
q2(z)=0
$$

なら境界は原点一点に退化する。

$$
q2(z)>0
$$

なら通常の正半径円として読める。

この分岐を先に持ったのは堅い。
特に「円」と言うとき、零半径の場合まで同じ言葉で扱うと混乱する。今回の実装では、zero boundary を一一点退化境界としてきちんと分けている。

## 一番良い判断

報告にもある通り、`ℝ × ℝ` の標準積ノルムを安易に L2 ノルム球と同一視していないのがよい。

ここはかなり重要じゃ。

`ℝ × ℝ` は積位相を持つが、そこで標準的に何の metric / norm を使うかは、Mathlib 側の構造に依存する。
だから、

```text
x^2 + y^2 = rho2
```

という座標方程式までは安全。
しかし、それをすぐに「metric sphere」と言うには、`EuclideanSpace ℝ (Fin 2)` への橋が必要。

この慎重さは正しい。

## 数学的な意味

今回の到達点はこう言える。

```text
pre-geometric fixed-q2 boundary path
  -> coordinate equation x^2 + y^2 = rho2
```

まで来た。

まだ、

```text
Euclidean metric sphere
angle
arc length
sin/cos parametrization
π
```

には行っていない。

しかし、初めて「円という言葉の入り口」に立った。
しかも、構成を円から始めたのではなく、既存 path を Euclidean coordinate-circle として解釈した。

この順序が美しい。

## 気になる点

一点、設計上の注意がある。

`EuclideanPhase.lean` は置き場所が `DkMath/CosmicFormula/Rotation/CF2D/` だが、中で `DkMath.Analysis.DkReal.SemanticCF2DNormalize` を import している。

これはビルド上は通っているが、層構造としては少し重い依存じゃ。
もし `CosmicFormula/Rotation/CF2D` を将来的に代数コアとして軽く保ちたいなら、`EuclideanPhase` は `Analysis/DkReal` 側、あるいは `CosmicFormula/Rotation/docs/bridge` 的な位置に分ける選択肢もある。

ただし、今回の内容は「既存 normalized path の Euclidean 解釈」なので、Analysis に依存するのは自然でもある。
今のままでも問題ではないが、公開前にモジュール階層の意図だけ明記しておくと安全じゃ。

## 次の自然な作業

次は報告通り、

```text
EuclideanCircleSq rho2
  -> EuclideanSpace ℝ (Fin 2) の metric sphere
```

への橋じゃ。

ただし、ここでも零境界と正境界を分ける。

```text
rho2 = 0:
  原点一点の退化境界

0 < rho2:
  半径 sqrt rho2 の標準 Euclidean sphere
```

ここで必要になりそうなのは、

```lean
rho2_nonneg_of_mem_euclideanCircleSq
radius := Real.sqrt rho2
radius_sq_eq_rho2
```

および、座標ペア \((x,y)\) と `EuclideanSpace ℝ (Fin 2)` の変換じゃな。

## 総評

非常によい更新じゃ。

一言で言えば、

```text
円や角度を使わず構成した fixed-q2 closed path を、
初めて x^2 + y^2 = rho2 という Euclidean coordinate-circle として解釈した。
```

しかも、zero boundary を退化境界として分け、`ℝ × ℝ` の metric sphere へ安易に飛ばない。
この慎重さが良い。

いまは「目を開けたら、どうも座標円だった」と分かった段階じゃな。
次は「標準 Euclidean 空間の円」として正式に握手する段階。ここも焦らず行くのが正解じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index 83664cc0..0bd34133 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -16,6 +16,7 @@ import DkMath.Analysis.DkReal.SemanticCF2D
 import DkMath.Analysis.DkReal.SemanticCF2DPhase
 import DkMath.Analysis.DkReal.SemanticCF2DPath
 import DkMath.Analysis.DkReal.SemanticCF2DNormalize
+import DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase
 
 #print "file: DkMath.Analysis"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 11b66ce8..fc97de55 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -113,6 +113,10 @@ under the core-zero action. Its four action translates retain this boundary,
 join at exact seams, repeat with phase index four, and concatenate to a closed
 continuous path. The final path is also packaged directly in
 `LevelSet Real (q2 z)`, so boundary membership is enforced by its codomain.
+`CF2D.EuclideanPhase` then interprets this boundary as the explicit
+two-coordinate Euclidean circle equation and maps the existing closed path
+through that homeomorphism. The zero boundary is kept as a separate
+one-point degenerate case.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 130a8451..a63bfb25 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1334,9 +1334,15 @@ have exact seams and concatenate to a closed path.
 their closed four-phase concatenation are packaged directly in
 `LevelSet Real (q2 z)`, making boundary membership part of the target type.
 
-[TODO: semantic-cf2d-phase/euclidean-levelset-bridge] Identify the positive
-real `q2` level sets with the corresponding Euclidean circle model without
-changing the pre-geometric construction.
+[IMPLEMENTED: semantic-cf2d-phase/euclidean-levelset-bridge]
+`CF2D.EuclideanPhase` identifies every real `q2` level set with the explicit
+two-coordinate Euclidean circle equation of squared radius `rho2`. It
+separates the zero one-point boundary and maps the existing closed path
+through this interpretation.
+
+[TODO: semantic-cf2d-phase/standard-euclidean-space] Relate the explicit
+coordinate circle equation to the standard `EuclideanSpace Real (Fin 2)`
+metric sphere, keeping the zero and positive-radius cases separate.
 
 [TODO: semantic-cf2d-phase/euclidean-interpretation] Only after normalization,
 identify the fixed-`q2` path with the standard Euclidean circle model and
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index f424183e..83baa50e 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -156,6 +156,8 @@ mechanism from which these theorem obligations can be investigated.
 ## Immediate Next Step
 
 The next bridge may identify positive real `q2` level sets with a standard
-Euclidean circle model. That bridge must remain an interpretation of the
+Euclidean metric sphere. The coordinate-circle homeomorphism is now
+implemented, including the degenerate zero boundary; the remaining bridge is
+to `EuclideanSpace Real (Fin 2)`. It must remain an interpretation of the
 existing boundary path, not a replacement construction. Refinement and limit
 arguments remain separate checkpoints.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index c0938864..e0a4bfcf 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -25,6 +25,10 @@ The same construction is now packaged directly in
 `LevelSet Real (Vec.q2 z)`. The level-set subtype carries its inherited
 topology, and the final closed path cannot leave the boundary by construction.
 
+`CF2D.EuclideanPhase` interprets this level set as the explicit coordinate
+equation `x^2 + y^2 = rho2` by a homeomorphism. The already-constructed closed
+path is mapped through that bridge; it is not reconstructed geometrically.
+
 The current implementation proves a four-state return:
 
 ```text
@@ -344,7 +348,8 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/boundary-normalization]
 [IMPLEMENTED: semantic-cf2d-phase/normalized-four-path]
 [IMPLEMENTED: semantic-cf2d-phase/levelset-path]
-[TODO: semantic-cf2d-phase/euclidean-levelset-bridge]
+[IMPLEMENTED: semantic-cf2d-phase/euclidean-levelset-bridge]
+[TODO: semantic-cf2d-phase/standard-euclidean-space]
 [TODO: semantic-cf2d-phase/refinement-law]
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
new file mode 100644
index 00000000..d653c0a9
--- /dev/null
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -0,0 +1,139 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2DNormalize
+import Mathlib.Topology.Homeomorph.Defs
+
+#print "file: DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase"
+
+/-!
+# Euclidean interpretation of the CF2D square-mass boundary
+
+This module does not construct a new path. It interprets the already-built
+`q2` level-set path as a path in the coordinate equation
+
+`x^2 + y^2 = rho2`.
+
+The radius is represented by its square, so the bridge remains valid for the
+degenerate zero boundary. Positive square mass later yields the ordinary
+positive-radius circle with radius `sqrt rho2`.
+
+No angle coordinate or trigonometric parametrization is introduced here.
+-/
+
+namespace DkMath.CosmicFormula.Rotation.CF2D
+
+/--
+The two-coordinate Euclidean circle equation with squared radius `rho2`.
+
+For `rho2 = 0` this is the degenerate one-point boundary.
+-/
+def EuclideanCircleSq (rho2 : ℝ) :=
+  {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 = rho2}
+
+instance (rho2 : ℝ) : TopologicalSpace (EuclideanCircleSq rho2) :=
+  inferInstanceAs
+    (TopologicalSpace {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 = rho2})
+
+namespace Vec
+
+/-- Real CF2D square mass is always nonnegative. -/
+theorem q2_nonneg (z : Vec ℝ) :
+    0 ≤ q2 z := by
+  exact add_nonneg (sq_nonneg z.core) (sq_nonneg z.beam)
+
+/-- Real square mass vanishes exactly at the zero state. -/
+theorem q2_eq_zero_iff (z : Vec ℝ) :
+    q2 z = 0 ↔ z = Vec.mk 0 0 := by
+  cases z with
+  | mk x y =>
+      simp only [q2, Vec.mk.injEq]
+      constructor
+      · intro h
+        have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
+        have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
+        exact ⟨hx, hy⟩
+      · rintro ⟨rfl, rfl⟩
+        norm_num
+
+/-- A nonzero real CF2D state has strictly positive square mass. -/
+theorem q2_pos_iff_ne_zero (z : Vec ℝ) :
+    0 < q2 z ↔ z ≠ Vec.mk 0 0 := by
+  constructor
+  · intro h hz
+    rw [hz] at h
+    norm_num [q2] at h
+  · intro hz
+    have hq : q2 z ≠ 0 := by
+      intro hzero
+      exact hz ((q2_eq_zero_iff z).1 hzero)
+    exact lt_of_le_of_ne (q2_nonneg z) hq.symm
+
+end Vec
+
+/--
+The abstract CF2D level set is homeomorphic to its explicit two-coordinate
+Euclidean circle equation.
+
+This is an interpretation theorem: both sides contain the same coordinates
+and the same quadratic boundary equation.
+-/
+def levelSetHomeomorphEuclideanCircleSq (rho2 : ℝ) :
+    LevelSet ℝ rho2 ≃ₜ EuclideanCircleSq rho2 where
+  toFun z := ⟨Vec.toProd z.1, z.2⟩
+  invFun p := ⟨Vec.ofProd p.1, by simpa [Vec.q2, Vec.ofProd] using p.2⟩
+  left_inv z := by
+    apply Subtype.ext
+    exact Vec.ofProd_toProd z.1
+  right_inv p := by
+    apply Subtype.ext
+    exact Vec.toProd_ofProd p.1
+  continuous_toFun := by
+    apply Continuous.subtype_mk
+    exact continuous_vecToProd.comp (continuous_levelSet_val rho2)
+  continuous_invFun := by
+    apply Continuous.subtype_mk
+    exact
+      (Continuous.vec_mk continuous_fst continuous_snd).comp
+        continuous_subtype_val
+
+/-- The zero squared-radius Euclidean circle contains only the origin. -/
+theorem euclideanCircleSq_zero_eq_origin
+    (p : EuclideanCircleSq 0) :
+    p = ⟨(0, 0), by norm_num⟩ := by
+  apply Subtype.ext
+  rcases p with ⟨⟨x, y⟩, h⟩
+  have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
+  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
+  simp [hx, hy]
+
+end DkMath.CosmicFormula.Rotation.CF2D
+
+namespace DkMath.Analysis.DkNNRealQ
+
+open DkMath.CosmicFormula.Rotation.CF2D
+
+noncomputable section
+
+/--
+The normalized closed level-set path interpreted in the explicit Euclidean
+circle equation with squared radius `q2 z`.
+-/
+def normalizedClosedEuclideanCircleSqPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path
+      (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)
+        (semanticPhaseLevelPoint r z 0))
+      (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)
+        (semanticPhaseLevelPoint r z 0)) :=
+  (normalizedClosedLevelFourPhasePath hcore z).map
+    (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)).continuous
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 751eae0f..bf43d30b 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -673,3 +673,27 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DNormalize` 成功
      (8277 jobs)。
+
+### 2026/06/23 06:58 JST (Euclidean coordinate-circle interpretation)
+
+1. 実装:
+   - `CF2D.EuclideanPhase.lean` を新設した。
+   - squared radius による `EuclideanCircleSq rho2` を定義した。
+   - `LevelSet Real rho2` と coordinate equation
+     `x^2 + y^2 = rho2` の homeomorphism を構成した。
+2. 境界分類:
+   - `Vec.q2_nonneg`、`Vec.q2_eq_zero_iff`、
+     `Vec.q2_pos_iff_ne_zero` を証明した。
+   - squared radius zero の circle equation が原点一つへ退化することを
+     証明した。
+3. path interpretation:
+   - 既存 `normalizedClosedLevelFourPhasePath` を homeomorphism で写し、
+     `normalizedClosedEuclideanCircleSqPath` を構成した。
+   - path は再構成せず、pre-geometric path の解釈として保持した。
+4. 境界:
+   - 標準積型の norm は L2 ではないため、単純な `Real × Real` metric sphere
+     とは同一視していない。
+   - 次候補は `EuclideanSpace Real (Fin 2)` の標準 metric sphere への bridge。
+5. 検証:
+   - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
+     (8278 jobs)。
````
`````
