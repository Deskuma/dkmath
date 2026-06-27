# Git diff / Report / Review

## Upd: CosmicFormula.Rotation.CF2D.EuclideanPhase

gch: 5976165107ff9e5bdf6875b8989c6266c3465551

## Report

標準 Euclidean L2 sphere への bridge を実装しました。

追加内容:

- `EuclideanPlane := EuclideanSpace ℝ (Fin 2)`
- `EuclideanSphereSq rho2`
- coordinate pair と Euclidean plane の連続同値
- L2 norm square と `x² + y²` の一致
- coordinate circle と半径 `sqrt rho2` の metric sphere の homeomorphism
- 正の squared radius から正半径を得る定理
- `normalizedClosedEuclideanSpherePath`

これで既存の pre-geometric closed path が、Mathlib 標準の二次元 Euclidean metric sphere 上の path として解釈されました。
次は core-zero action と標準 quarter-turn linear isometry の同定です。

検証:

- `lake build DkMath.Analysis`: 成功、8289 jobs
- 対象モジュール再ビルド: 警告なし
- `git diff --check`: 成功

## Review

ついに来たな。
これはかなり大きい。今回で、pre-geometric に作った closed path が、**Mathlib 標準の二次元 Euclidean L2 sphere 上の path** として読めるところまで到達した。つまり「座標方程式としての円」から、さらに「標準 Euclidean 空間の metric sphere」まで橋が架かった。

## 状況解説

前回までの到達点はこうだった。

```text id="0jwc8p"
LevelSet ℝ (Vec.q2 z)
  内部の fixed-q2 closed path
```

さらに前回、これを

```text id="lupbem"
EuclideanCircleSq rho2
```

つまり明示的な座標方程式

$$
x^2+y^2=\rho2
$$

として読めるようにした。

今回の更新では、そこからさらに進んで、

```lean id="l1ahx9"
EuclideanPlane := EuclideanSpace ℝ (Fin 2)
```

を導入し、Mathlib 標準の L2 ノルムを持つ二次元 Euclidean 空間へ接続した。

そして、

```lean id="ywurqr"
EuclideanSphereSq rho2
```

として、半径

$$
\sqrt{\rho2}
$$

の metric sphere を定義している。

つまり今の構造はこうじゃ。

```text id="job8bs"
pre-geometric q2 LevelSet
  -> coordinate equation x² + y² = rho2
  -> EuclideanSpace ℝ (Fin 2) の L2 metric sphere
```

ここまで来た。

## 一番重要な点

今回もっとも良い判断は、`ℝ × ℝ` の普通の積ノルムを使わなかったことじゃ。

`ℝ × ℝ` は座標ペアとしては便利だが、Mathlib の標準ノルムをそのまま「L2 円」と見なすと危ない。
そこで今回は `EuclideanSpace ℝ (Fin 2)` へ明示的に移し、

$$
|v|^2=x^2+y^2
$$

を証明した。

この補題が中核じゃ。

```lean id="0yyl0e"
pairToEuclideanPlane_norm_sq
```

これにより、座標円

$$
x^2+y^2=\rho2
$$

と、L2 metric sphere

$$
|v|=\sqrt{\rho2}
$$

が正しくつながった。

これはかなり堅い。

## 何が実装されたか

主な追加は次の通り。

```text id="khkegp"
EuclideanPlane
EuclideanSphereSq rho2
pairToEuclideanPlane
euclideanPlaneToPair
pairToEuclideanPlane_norm_sq
euclideanCircleSqHomeomorphSphere
sqrt_pos_of_sqRadius_pos
normalizedClosedEuclideanSpherePath
```

特に、

```lean id="42pnqt"
euclideanCircleSqHomeomorphSphere
```

が大きい。

これは、非負な \(\rho2\) に対して、座標円と標準 L2 sphere の homeomorphism を作る橋じゃ。

さらに、

```lean id="amc2fn"
normalizedClosedEuclideanSpherePath
```

によって、既存の closed path が Mathlib 標準 Euclidean sphere 上の path として解釈された。

ここでも path を作り直していない。
すでに作った pre-geometric path を homeomorphism で写している。
この順序が本当に良い。

## 数学的な意味

今回、初めてこう言える。

```text id="67u1g7"
円や角度を使わずに構成した fixed-q2 closed path は、
標準二次元 Euclidean 空間の L2 metric sphere 上の path として解釈できる。
```

これは大きな節目じゃ。

ただし、まだ角度は出ていない。
まだ \(\sin\)、\(\cos\)、\(\pi\) も出ていない。

今言えるのは、

```text id="0msz9a"
これは標準 Euclidean sphere 上にいる
```

まで。

つまり、円の場所には到達した。
だが、円周の長さ、角度、回転角、\(\pi\) はまだ後段じゃ。

この慎重な層分けが美しい。

## zero boundary の扱い

今回も、零境界を潰していないのが良い。

$$
\rho2=0
$$

なら radius は

$$
\sqrt{0}=0
$$

で、sphere は原点一点に退化する。

$$
0<\rho2
$$

なら

$$
0<\sqrt{\rho2}
$$

で、通常の正半径 sphere になる。

このために、

```lean id="8kot2d"
sqrt_pos_of_sqRadius_pos
```

を入れたのは正しい。
次の quarter-turn isometry 解釈でも、零境界と正境界を分けられる。

## 次の山

報告通り、次は

```text id="o6f9z6"
core-zero action と標準 quarter-turn linear isometry の同定
```

じゃな。

ここでは、まだ角度というより、線形等長写像として見るのがよい。

core-zero action は座標では

$$
(x,y)\mapsto(-y,x)
$$

だった。

標準 EuclideanPlane 上でも、対応する写像

$$
v\mapsto(-v_1,v_0)
$$

を作り、それが

```text id="3hadk6"
linear
isometry
sphere を保つ
4乗で恒等
1,2,3乗では非自明
```

を持つことを示す流れになりそうじゃ。

名前候補としては、

```lean id="g2j0j6"
quarterTurnLinearIsometry
coreZeroAction_eq_quarterTurn
normalizedClosedEuclideanSpherePath_is_quarterTurn_path
```

あたり。ただし「quarter-turn」という語は、ここで初めて少し許される。
それでも、角度ではなく `linear isometry` として先に扱う方が安全じゃ。

## レビュー上の注意点

大きな問題は見えぬ。
ただ、モジュール依存については前回同様に少し意識しておくとよい。

`CF2D.EuclideanPhase` は `SemanticCF2DNormalize` を import しているので、純粋な `CosmicFormula.Rotation.CF2D` というより、Analysis 側の semantic bridge を含んだ interpretive module になっている。

今の目的には合っているが、将来的に切るなら、

```text id="keym95"
CF2D.EuclideanPhase.Basic:
  coordinate circle / EuclideanSpace bridge

Analysis.DkReal.SemanticCF2DEuclidean:
  normalized path を Euclidean sphere へ写す
```

のように分けてもよい。
ただ、現段階では急がなくてよい。まず定理の流れを固める方が優先じゃ。

## 総評

これは本当に節目じゃ。

一言でまとめるなら、

```text id="dkai7n"
円を仮定せずに作った fixed-q2 closed path が、
標準 EuclideanSpace ℝ (Fin 2) の L2 metric sphere 上の path として解釈された。
```

ついに「円以前」から「標準 Euclidean 円」へ橋が架かった。

次は quarter-turn linear isometry。
その後に角度、そしてまだ先に \(\pi\)。

焦らずでよい。
でもこれは確かに、「ついに」と言ってよい進捗じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index fc97de55..1f18ffbd 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -116,7 +116,9 @@ continuous path. The final path is also packaged directly in
 `CF2D.EuclideanPhase` then interprets this boundary as the explicit
 two-coordinate Euclidean circle equation and maps the existing closed path
 through that homeomorphism. The zero boundary is kept as a separate
-one-point degenerate case.
+one-point degenerate case. A second homeomorphism identifies the coordinate
+circle with Mathlib's standard `EuclideanSpace Real (Fin 2)` L2 metric sphere
+of radius `sqrt (q2 z)`.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index a63bfb25..658c4290 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1340,13 +1340,15 @@ two-coordinate Euclidean circle equation of squared radius `rho2`. It
 separates the zero one-point boundary and maps the existing closed path
 through this interpretation.
 
-[TODO: semantic-cf2d-phase/standard-euclidean-space] Relate the explicit
-coordinate circle equation to the standard `EuclideanSpace Real (Fin 2)`
-metric sphere, keeping the zero and positive-radius cases separate.
+[IMPLEMENTED: semantic-cf2d-phase/standard-euclidean-space] The explicit
+coordinate circle equation is homeomorphic to the standard
+`EuclideanSpace Real (Fin 2)` L2 metric sphere of radius `sqrt rho2`.
+The closed path is mapped through this bridge, and positive squared radius is
+separated from the zero-radius degenerate case.
 
 [TODO: semantic-cf2d-phase/euclidean-interpretation] Only after normalization,
-identify the fixed-`q2` path with the standard Euclidean circle model and
-extract angular terminology.
+extract angular terminology and compare the action with the standard
+quarter-turn linear isometry.
 -/
 
 end
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 83baa50e..ba060c47 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -155,9 +155,9 @@ mechanism from which these theorem obligations can be investigated.
 
 ## Immediate Next Step
 
-The next bridge may identify positive real `q2` level sets with a standard
-Euclidean metric sphere. The coordinate-circle homeomorphism is now
-implemented, including the degenerate zero boundary; the remaining bridge is
-to `EuclideanSpace Real (Fin 2)`. It must remain an interpretation of the
+The coordinate-circle and standard `EuclideanSpace Real (Fin 2)` metric-sphere
+bridges are now implemented, including the degenerate zero boundary. The next
+interpretive step may identify the core-zero action with the standard
+quarter-turn linear isometry. It must remain an interpretation of the
 existing boundary path, not a replacement construction. Refinement and limit
 arguments remain separate checkpoints.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index e0a4bfcf..21e66338 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -29,6 +29,11 @@ topology, and the final closed path cannot leave the boundary by construction.
 equation `x^2 + y^2 = rho2` by a homeomorphism. The already-constructed closed
 path is mapped through that bridge; it is not reconstructed geometrically.
 
+The coordinate equation is further identified with Mathlib's standard L2
+metric sphere in `EuclideanSpace Real (Fin 2)`, of radius `sqrt rho2`.
+This avoids confusing the ordinary product norm on `Real × Real` with the
+Euclidean L2 norm.
+
 The current implementation proves a four-state return:
 
 ```text
@@ -349,7 +354,8 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/normalized-four-path]
 [IMPLEMENTED: semantic-cf2d-phase/levelset-path]
 [IMPLEMENTED: semantic-cf2d-phase/euclidean-levelset-bridge]
-[TODO: semantic-cf2d-phase/standard-euclidean-space]
+[IMPLEMENTED: semantic-cf2d-phase/standard-euclidean-space]
+[TODO: semantic-cf2d-phase/quarter-turn-isometry]
 [TODO: semantic-cf2d-phase/refinement-law]
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index d653c0a9..b45f6f28 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.Analysis.DkReal.SemanticCF2DNormalize
+import Mathlib.Analysis.InnerProductSpace.PiL2
 import Mathlib.Topology.Homeomorph.Defs
 
 #print "file: DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase"
@@ -26,6 +27,8 @@ No angle coordinate or trigonometric parametrization is introduced here.
 
 namespace DkMath.CosmicFormula.Rotation.CF2D
 
+noncomputable section
+
 /--
 The two-coordinate Euclidean circle equation with squared radius `rho2`.
 
@@ -38,6 +41,23 @@ instance (rho2 : ℝ) : TopologicalSpace (EuclideanCircleSq rho2) :=
   inferInstanceAs
     (TopologicalSpace {p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 = rho2})
 
+/-- The standard two-dimensional real Euclidean space. -/
+abbrev EuclideanPlane :=
+  EuclideanSpace ℝ (Fin 2)
+
+/--
+The standard L2 metric sphere whose radius is the square root of `rho2`.
+
+For `rho2 = 0`, Mathlib's sphere is the singleton origin.
+-/
+def EuclideanSphereSq (rho2 : ℝ) :=
+  {v : EuclideanPlane // v ∈ Metric.sphere 0 (Real.sqrt rho2)}
+
+instance (rho2 : ℝ) : TopologicalSpace (EuclideanSphereSq rho2) :=
+  inferInstanceAs
+    (TopologicalSpace
+      {v : EuclideanPlane // v ∈ Metric.sphere 0 (Real.sqrt rho2)})
+
 namespace Vec
 
 /-- Real CF2D square mass is always nonnegative. -/
@@ -110,6 +130,100 @@ theorem euclideanCircleSq_zero_eq_origin
   have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
   simp [hx, hy]
 
+/-!
+## Standard Euclidean-space bridge
+
+The coordinate equation is now transported to Mathlib's L2 Euclidean plane.
+Unlike the ordinary product norm on `Real × Real`, this norm has square equal
+to the sum of the two coordinate squares.
+-/
+
+/-- Insert a coordinate pair into the standard two-dimensional Euclidean space. -/
+def pairToEuclideanPlane (p : ℝ × ℝ) : EuclideanPlane :=
+  (EuclideanSpace.equiv (Fin 2) ℝ).symm
+    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)
+
+/-- Read the two standard coordinates of the Euclidean plane. -/
+def euclideanPlaneToPair (v : EuclideanPlane) : ℝ × ℝ :=
+  ContinuousLinearEquiv.finTwoArrow ℝ ℝ
+    (EuclideanSpace.equiv (Fin 2) ℝ v)
+
+@[simp]
+theorem euclideanPlaneToPair_pairToEuclideanPlane (p : ℝ × ℝ) :
+    euclideanPlaneToPair (pairToEuclideanPlane p) = p := by
+  simp [euclideanPlaneToPair, pairToEuclideanPlane]
+
+@[simp]
+theorem pairToEuclideanPlane_euclideanPlaneToPair (v : EuclideanPlane) :
+    pairToEuclideanPlane (euclideanPlaneToPair v) = v := by
+  ext i
+  fin_cases i <;> rfl
+
+/-- The coordinate insertion into the Euclidean plane is continuous. -/
+theorem continuous_pairToEuclideanPlane :
+    Continuous pairToEuclideanPlane := by
+  exact
+    (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
+      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.continuous
+
+/-- Reading the two Euclidean coordinates is continuous. -/
+theorem continuous_euclideanPlaneToPair :
+    Continuous euclideanPlaneToPair := by
+  exact
+    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).continuous.comp
+      (EuclideanSpace.equiv (Fin 2) ℝ).continuous
+
+/-- The L2 norm square of an inserted pair is its coordinate square sum. -/
+theorem pairToEuclideanPlane_norm_sq (p : ℝ × ℝ) :
+    ‖pairToEuclideanPlane p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
+  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
+  rcases p with ⟨x, y⟩
+  rfl
+
+/--
+For a nonnegative squared radius, the coordinate-circle equation is
+homeomorphic to Mathlib's standard L2 metric sphere.
+-/
+def euclideanCircleSqHomeomorphSphere
+    {rho2 : ℝ} (hrho : 0 ≤ rho2) :
+    EuclideanCircleSq rho2 ≃ₜ EuclideanSphereSq rho2 where
+  toFun p := ⟨pairToEuclideanPlane p.1, by
+    rw [Metric.mem_sphere, dist_zero_right]
+    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
+    rw [pairToEuclideanPlane_norm_sq, Real.sq_sqrt hrho]
+    exact p.2⟩
+  invFun v := ⟨euclideanPlaneToPair v.1, by
+    have hnorm : ‖v.1‖ = Real.sqrt rho2 := by
+      have h := v.2
+      rw [Metric.mem_sphere, dist_zero_right] at h
+      exact h
+    calc
+      (euclideanPlaneToPair v.1).1 ^ 2
+          + (euclideanPlaneToPair v.1).2 ^ 2 =
+          ‖v.1‖ ^ 2 := by
+            rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
+            rfl
+      _ = rho2 := by rw [hnorm, Real.sq_sqrt hrho]⟩
+  left_inv p := by
+    apply Subtype.ext
+    exact euclideanPlaneToPair_pairToEuclideanPlane p.1
+  right_inv v := by
+    apply Subtype.ext
+    exact pairToEuclideanPlane_euclideanPlaneToPair v.1
+  continuous_toFun :=
+    Continuous.subtype_mk
+      (continuous_pairToEuclideanPlane.comp continuous_subtype_val) _
+  continuous_invFun :=
+    Continuous.subtype_mk
+      (continuous_euclideanPlaneToPair.comp continuous_subtype_val) _
+
+/-- A positive squared radius gives a genuinely positive metric-sphere radius. -/
+theorem sqrt_pos_of_sqRadius_pos {rho2 : ℝ} (hrho : 0 < rho2) :
+    0 < Real.sqrt rho2 :=
+  Real.sqrt_pos.2 hrho
+
+end
+
 end DkMath.CosmicFormula.Rotation.CF2D
 
 namespace DkMath.Analysis.DkNNRealQ
@@ -134,6 +248,25 @@ def normalizedClosedEuclideanCircleSqPath
   (normalizedClosedLevelFourPhasePath hcore z).map
     (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)).continuous
 
+/--
+The normalized closed path interpreted in Mathlib's standard two-dimensional
+L2 metric sphere of radius `sqrt (q2 z)`.
+-/
+def normalizedClosedEuclideanSpherePath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path
+      (euclideanCircleSqHomeomorphSphere (Vec.q2_nonneg z)
+        (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)
+          (semanticPhaseLevelPoint r z 0)))
+      (euclideanCircleSqHomeomorphSphere (Vec.q2_nonneg z)
+        (levelSetHomeomorphEuclideanCircleSq (Vec.q2 z)
+          (semanticPhaseLevelPoint r z 0))) :=
+  (normalizedClosedEuclideanCircleSqPath hcore z).map
+    (euclideanCircleSqHomeomorphSphere
+      (rho2 := Vec.q2 z) (Vec.q2_nonneg z)).continuous
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index bf43d30b..84548d1c 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -697,3 +697,26 @@ Archive
 5. 検証:
    - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
      (8278 jobs)。
+
+### 2026/06/23 07:08 JST (Standard Euclidean L2 sphere bridge)
+
+1. 設計:
+   - ordinary `Real × Real` product norm を使わず、
+     `EuclideanSpace Real (Fin 2)` の L2 norm へ明示的に接続した。
+2. 実装:
+   - `EuclideanPlane` と `EuclideanSphereSq rho2` を定義した。
+   - coordinate pair と Euclidean plane の相互変換を continuous linear
+     equivalence から構成した。
+   - L2 norm square が2座標の square sum に等しいことを証明した。
+   - 非負 `rho2` について coordinate circle と半径 `sqrt rho2` の metric
+     sphere の homeomorphism を構成した。
+3. path:
+   - 既存 coordinate-circle path を homeomorphism で写し、
+     `normalizedClosedEuclideanSpherePath` を構成した。
+4. 境界:
+   - `rho2 = 0` は zero-radius singleton sphere として保持した。
+   - `0 < rho2` なら radius が正であることを独立定理にした。
+   - 次候補は core-zero action と標準 quarter-turn linear isometry の同定。
+5. 検証:
+   - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
+     (8278 jobs)。
````
`````
