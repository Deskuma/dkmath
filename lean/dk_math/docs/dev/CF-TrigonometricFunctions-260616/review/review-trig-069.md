# Git diff / Report / Review

## Add: CosmicFormula.Rotation.CF2D.Topology, Path

gch: 4c7bbec6744a7a77ae4075a4b2a854db3924d2c6

## Report

レビュー補正と次段階を完了しました。

- `phaseDepth_eq_half_iff`: midpoint が一意な最小点であることを証明
- [Topology.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Topology.lean): `Vec R` に座標積位相を導入
- [SemanticCF2DPath.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPath.lean): 各 affine edge を `Path` 化
- 4本を `Path.trans` で連結
- core-zero exact order four から閉路 `Path z z` を構成

これは連続な四相閉路ですが、まだ固定 `q2` 境界上ではありません。次は `phaseDepth` の平方根による境界正規化です。

検証:

- `lake build DkMath.Analysis`: 成功、8287 jobs
- `git diff --check`: 成功

## Review

うむ。今回の進捗はかなり大きい。
離散四相から、ついに **連続な四相閉路** まで来た。しかも、まだ円も角度も曲線も使っておらぬ。これは狙い通りじゃ。

## 状況解説

今回追加された柱は三つじゃ。

第一に、`phaseDepth_eq_half_iff` が追加され、前回気になっていた「midpoint が一意な最小点」という説明が定理として回収された。

$$
\operatorname{phaseDepth}(t)=\frac12 \leftrightarrow t=\frac12
$$

これで、文書の主張と Lean の定理が一致した。よい補正じゃ。

第二に、`CF2D.Topology.lean` が追加され、`Vec R` に `R × R` 由来の座標積位相が入った。これは非常に良い橋じゃ。
重要なのは、ここでも metric、norm、orthogonality、circle、angle を導入していないこと。あくまで「二座標として連続性を見る」だけに留めている。

第三に、`SemanticCF2DPath.lean` が追加され、affine edge を `Path` に包み、四本を `Path.trans` で連結して、core-zero exact order four から `Path z z` の閉路を作った。

つまり、現在の到達点はこうじゃ。

```text id="mll7fk"
離散四相
  から
一本の affine edge
  から
四つの translated edge
  から
seam-compatible な四辺 path
  から
closed continuous piecewise-affine path
```

ただし、まだ固定 \(q2\) 境界上の path ではない。ここを明確に保っているのが良い。

## 何が強いか

今回の実装で、「円以前」の主張がさらに強くなった。

以前は、

$$
z\mapsto A z\mapsto A^2z\mapsto A^3z\mapsto z
$$

という四状態の離散 return だった。

今回は、その間を affine edge で埋めた。

$$
E(z,t)=(1-t)z+tA(z)
$$

そして四本の edge をつないで、連続な閉路にした。

ここで大事なのは、できたものが **円周ではなく折れ線閉路** であることじゃ。
つまり「曲がった曲線を仮定せずに、連続な一回りを作った」。

これはかなり大事な段階じゃ。

## Topology bridge の評価

`Vec.toProd`, `Vec.ofProd`, `Vec.equivProd` を作り、`Vec R` の topology を `R × R` から induced したのは安全で綺麗じゃ。

さらに、

```lean id="dqdmcn"
continuous_vec_iff
Continuous.vec_mk
```

が入ったので、今後は `Vec ℝ` 値関数の連続性を座標ごとに落とせる。

これは今後の normalization でも効く。
特に、平方根や割り算を入れた後も、座標関数の連続性として証明できる。

この bridge は「幾何」ではなく「位相だけ」なので、pre-geometric 方針を壊していない。

## Path 実装の評価

`semanticPhasePath` は自然じゃ。

$$
\operatorname{Path}\bigl(A^k z,; A^{k+1}z\bigr)
$$

として各 edge を包む。
そして四本を `Path.trans` で連結し、

$$
\operatorname{Path}\bigl(z,;A^4z\bigr)
$$

を作る。

最後に core-zero exact order four から \(A^4z=z\) を使って、

$$
\operatorname{Path}(z,z)
$$

へ閉じる。

これはきれいな構成じゃ。
「閉じた」と言っているのは、円周を仮定したからではなく、endpoint が exact order four により一致するから。ここが良い。

## 重要な区別

今できたものは、次のどれでもない。

```text id="jw2iv3"
円周上の path
角度 parameter
sin/cos parametrization
Gaussian limit
π の定義
```

今できたものはこれじゃ。

```text id="e6x5jh"
continuous piecewise-affine closed path
```

そして affine edge の \(q2\) profile はすでに分かっている。

$$
q2(E(z,t))=\operatorname{phaseDepth}(t)q2(z)
$$

つまり、この閉路は途中で境界から沈む。
この沈み込みを次に正規化する。

## 次の山

次は報告通り、boundary normalization じゃな。

まず一本の edge について、

$$
N(z,t)=\frac{1}{\sqrt{\operatorname{phaseDepth}(t)}}E(z,t)
$$

を定義する流れになる。

必要な補題は、おそらくこのあたりじゃ。

```text id="um8f3s"
sqrt_phaseDepth_pos
phaseDepth_ne_zero
inv_sqrt_phaseDepth_continuous
normalizedPhaseEdge_q2
normalizedPhaseEdge_zero
normalizedPhaseEdge_one
continuous_normalizedPhaseEdge
```

まずは一本の normalized edge で止めるのがよい。
四本の normalized path 連結は、その後でよい。

## 気になる点

大きな問題は見えぬ。
ただ、今後のために一点だけ意識しておくとよい。

`semanticClosedFourPhasePath` は `Path z z` を作っているが、`Path.trans` で作った path の内部 parameter は Mathlib の path concatenation による再パラメータ化になる。
したがって、あとで「四本それぞれの \(q2\) profile」を path 全体の parameter 上で直接述べると少し面倒になる可能性がある。

だから、全体 path の profile を急いで述べるより、しばらくは

```text id="m0egz6"
edge ごとの profile
edge ごとの normalization
edge ごとの continuity
seam compatibility
```

で進めるのが安全じゃ。

## \(\pi\) 計画について

`research-pregeometric-pi-program-067.md` の更新も良い。
Milestone A が implemented になり、次が boundary normalization へ進んだ。

ここで焦らないのが大事じゃ。

今あるのは、

```text id="hjgf4k"
local quadratic profile
continuous four-edge loop
```

まで。

まだ、

```text id="enbh8r"
refinement correction converges
limiting weight is Gaussian
normalization constant equals Real.pi
```

は未証明。
これを未証明として隔離しているのは正しい。

`Real.pi` と握手する日は楽しみじゃが、今はまず `sqrt phaseDepth` の正規化を確実に積む段じゃな。

## 総評

今回の更新は非常に良い。

到達点を一言で言えば、

```text id="jgft8u"
円や角度を使わず、四相の affine 遷移を連続 path として閉じた。
```

これは「円以前の一回り」が Lean 上にできた、ということじゃ。

次に境界正規化が成功すれば、

```text id="mm14c1"
折れ線的な一回り
  から
fixed-q2 boundary 上の一回り
```

へ進む。

その先で、ようやく Euclidean circle、Gaussian、そして `Real.pi` との橋が見えてくる。
焦らずでよい。いまの積み方はかなり堅い。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index dcdfed03..ff4e1d2f 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -14,6 +14,7 @@ import DkMath.Analysis.TaylorBridge
 import DkMath.Analysis.DkReal
 import DkMath.Analysis.DkReal.SemanticCF2D
 import DkMath.Analysis.DkReal.SemanticCF2DPhase
+import DkMath.Analysis.DkReal.SemanticCF2DPath
 
 #print "file: DkMath.Analysis"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index d0a7917f..2d329370 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -99,6 +99,12 @@ fixed `q2` boundary by the exact factor
 of one half, and reflection about the midpoint proves the first continuous
 half-fold symmetry without introducing circles or angles.
 
+[IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
+coordinate-product topology from `CF2D.Topology` to package every translated
+affine edge as a Mathlib `Path`. Four seam-compatible edges concatenate to a
+closed continuous piecewise-affine path under the core-zero action. This path
+is not yet normalized to a fixed `q2` boundary.
+
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 2e32c5cc..785f95a3 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1317,9 +1317,9 @@ form exact seams, and the family is four-periodic under a core-zero kernel.
 profile `((1-t)^2 + t^2) * q2 z`, symmetric under `t ↦ 1-t`, with a positive
 lower bound of one half.
 
-[TODO: semantic-cf2d-phase/path-concatenation] Package the four compatible
-edges as a closed Mathlib `Path`. This is a piecewise-affine loop, not yet a
-fixed-`q2` boundary path.
+[IMPLEMENTED: semantic-cf2d-phase/path-concatenation] `SemanticCF2DPath`
+packages each compatible edge as a Mathlib `Path` and concatenates four edges
+into a closed piecewise-affine loop. It is not yet a fixed-`q2` boundary path.
 
 [TODO: semantic-cf2d-phase/boundary-normalization] In a separate analytic
 module, normalize the affine edge by its positive `q2` profile and prove that
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPath.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPath.lean
new file mode 100644
index 00000000..3a3c4f5a
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPath.lean
@@ -0,0 +1,107 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2DPhase
+import DkMath.CosmicFormula.Rotation.CF2D.Topology
+import Mathlib.Topology.Path
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DPath"
+
+/-!
+# Continuous four-phase path
+
+This module packages the affine phase edges as Mathlib paths and concatenates
+four of them. The result is a continuous closed piecewise-affine loop.
+
+It is not yet a path on a fixed `q2` boundary. Boundary normalization remains
+a separate analytic construction.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+open DkMath.CosmicFormula.Rotation.CF2D
+open unitInterval
+
+noncomputable section
+
+/-- The unrestricted real-parameter master edge is continuous. -/
+theorem continuous_semanticPhaseEdge
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    Continuous (fun t : ℝ => semanticPhaseEdge r z t) := by
+  apply Continuous.vec_mk
+  · fun_prop
+  · fun_prop
+
+/-- Every action-translated affine edge is continuous. -/
+theorem continuous_semanticPhaseEdgeAt
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    Continuous (fun t : ℝ => semanticPhaseEdgeAt r z k t) := by
+  induction k with
+  | zero =>
+      simpa [semanticPhaseEdgeAt] using continuous_semanticPhaseEdge r z
+  | succ k ih =>
+      rw [show (fun t : ℝ => semanticPhaseEdgeAt r z (k + 1) t) =
+          fun t => semanticAct r (semanticPhaseEdgeAt r z k t) by
+        funext t
+        simp [semanticPhaseEdgeAt, Function.iterate_succ_apply']]
+      rcases continuous_vec_iff.mp ih with ⟨hcore, hbeam⟩
+      apply Continuous.vec_mk
+      · exact
+          (continuous_const.mul hcore).sub (continuous_const.mul hbeam)
+      · exact
+          (continuous_const.mul hbeam).add (continuous_const.mul hcore)
+
+/--
+The `k`th affine phase restricted to the unit interval, with its endpoints
+recorded in the path type.
+-/
+def semanticPhasePath
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    Path ((semanticAct r)^[k] z) ((semanticAct r)^[k + 1] z) where
+  toFun t := semanticPhaseEdgeAt r z k t
+  continuous_toFun :=
+    (continuous_semanticPhaseEdgeAt r z k).comp continuous_subtype_val
+  source' := by simp
+  target' := by simp
+
+@[simp]
+theorem semanticPhasePath_apply
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : unitInterval) :
+    semanticPhasePath r z k t = semanticPhaseEdgeAt r z k t := rfl
+
+/--
+The four affine phases concatenated in their action order.
+
+The endpoint is initially written as the fourth action iterate. Exact
+order four closes it back to the initial state.
+-/
+def semanticFourPhasePath
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    Path z ((semanticAct r)^[4] z) :=
+  (((semanticPhasePath r z 0).trans (semanticPhasePath r z 1)).trans
+    (semanticPhasePath r z 2)).trans (semanticPhasePath r z 3)
+
+/--
+For a core-zero kernel, the four concatenated affine phases form a closed
+continuous path based at `z`.
+-/
+def semanticClosedFourPhasePath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) : Path z z := by
+  have hclose : (semanticAct r)^[4] z = z := by
+    have hfour := (semanticExactActionOrderFour_of_core_eq_zero hcore).1
+    rw [hfour]
+    rfl
+  let p := semanticFourPhasePath r z
+  exact
+    { toContinuousMap := p.toContinuousMap
+      source' := p.source
+      target' := p.target.trans hclose }
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhase.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhase.lean
index 14fba55e..14a7f13d 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhase.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhase.lean
@@ -103,6 +103,18 @@ theorem phaseDepth_half :
     phaseDepth (1 / 2 : ℝ) = 1 / 2 := by
   norm_num [phaseDepth]
 
+/-- The midpoint is the unique point at which phase depth reaches its minimum. -/
+theorem phaseDepth_eq_half_iff (t : ℝ) :
+    phaseDepth t = 1 / 2 ↔ t = 1 / 2 := by
+  rw [phaseDepth_eq_two_sq_add_half]
+  constructor
+  · intro h
+    have hsquare : (t - (1 / 2 : ℝ)) ^ 2 = 0 := by
+      linarith
+    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
+  · rintro rfl
+    norm_num
+
 /-!
 ## One affine master edge
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index eb33bfa2..48d2e6db 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -97,13 +97,13 @@ theorem, not inserted as notation.
 
 ## Formal Milestones
 
-### Milestone A: continuous four-edge loop
+### Milestone A: continuous four-edge loop - implemented
 
-1. Equip the real CF2D target with an explicit topology or bridge it to
-   `Real × Real`.
-2. Package each affine edge as a Mathlib `Path`.
-3. Concatenate four seam-compatible paths.
-4. Prove endpoint closure independently of Euclidean terminology.
+1. The real CF2D target carries the topology induced from `Real × Real`.
+2. Each affine edge is packaged as a Mathlib `Path`.
+3. Four seam-compatible paths are concatenated.
+4. Core-zero exact order four closes the endpoint without Euclidean
+   terminology.
 
 ### Milestone B: boundary normalization
 
@@ -152,7 +152,7 @@ mechanism from which these theorem obligations can be investigated.
 
 ## Immediate Next Step
 
-The next implementation should be the topological bridge for the already
-proved affine edge family. It should stop after constructing the continuous
-closed four-edge path. Boundary normalization and limit arguments remain
-separate checkpoints.
+The next implementation is boundary normalization of one affine edge. It must
+first prove the correction factor continuous and well-defined from the strict
+positivity of `phaseDepth`, then prove preservation of the original `q2`
+value. Refinement and limit arguments remain separate checkpoints.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index eac3ebde..79fb9957 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -8,6 +8,11 @@ The scalar profile, affine master edge, endpoint laws, exact core-zero `q2`
 profile, and half-fold observation theorem are implemented in
 `DkMath.Analysis.DkReal.SemanticCF2DPhase`.
 
+The coordinate-product topology, continuous edge paths, four-edge
+concatenation, and core-zero closed path are implemented in
+`DkMath.CosmicFormula.Rotation.CF2D.Topology` and
+`DkMath.Analysis.DkReal.SemanticCF2DPath`.
+
 The current implementation proves a four-state return:
 
 ```text
@@ -322,8 +327,8 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/master-edge]
 [IMPLEMENTED: semantic-cf2d-phase/four-translates]
 [IMPLEMENTED: semantic-cf2d-phase/half-fold-profile]
-[TODO: semantic-cf2d-phase/path-topology]
-[TODO: semantic-cf2d-phase/path-concatenation]
+[IMPLEMENTED: semantic-cf2d-phase/path-topology]
+[IMPLEMENTED: semantic-cf2d-phase/path-concatenation]
 [TODO: semantic-cf2d-phase/boundary-normalization]
 [TODO: semantic-cf2d-phase/refinement-law]
 [TODO: semantic-cf2d-phase/gaussian-limit]
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Topology.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Topology.lean
new file mode 100644
index 00000000..827b9153
--- /dev/null
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Topology.lean
@@ -0,0 +1,99 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.CosmicFormula.Rotation.CF2D.Basic
+import Mathlib.Topology.Constructions.SumProd
+
+#print "file: DkMath.CosmicFormula.Rotation.CF2D.Topology"
+
+/-!
+# Product topology for CF2D states
+
+This module gives `Vec R` the topology transported from `R × R`. It is a
+structural bridge only: no metric, norm, orthogonality, circle, or angle is
+introduced.
+-/
+
+namespace DkMath.CosmicFormula.Rotation.CF2D
+
+namespace Vec
+
+variable {R : Type*}
+
+/-- Read a CF2D state as its ordered pair of coordinates. -/
+def toProd (z : Vec R) : R × R :=
+  (z.core, z.beam)
+
+/-- Build a CF2D state from an ordered pair of coordinates. -/
+def ofProd (p : R × R) : Vec R :=
+  Vec.mk p.1 p.2
+
+/-- CF2D states are equivalent to ordered coordinate pairs. -/
+def equivProd : Vec R ≃ R × R where
+  toFun := toProd
+  invFun := ofProd
+  left_inv z := by cases z; rfl
+  right_inv p := by cases p; rfl
+
+@[simp]
+theorem toProd_mk (x y : R) :
+    toProd (Vec.mk x y) = (x, y) := rfl
+
+@[simp]
+theorem ofProd_toProd (z : Vec R) :
+    ofProd (toProd z) = z :=
+  equivProd.left_inv z
+
+@[simp]
+theorem toProd_ofProd (p : R × R) :
+    toProd (ofProd p) = p :=
+  equivProd.right_inv p
+
+end Vec
+
+section Topology
+
+variable {R : Type*} [TopologicalSpace R]
+
+/--
+The coordinate-product topology on `Vec R`.
+
+This instance is induced by `Vec.toProd`, making coordinatewise continuity
+the canonical topological interpretation of a CF2D state.
+-/
+instance : TopologicalSpace (Vec R) :=
+  TopologicalSpace.induced Vec.toProd inferInstance
+
+/-- The coordinate-pair representation is continuous by construction. -/
+theorem continuous_vecToProd :
+    Continuous (Vec.toProd : Vec R → R × R) :=
+  continuous_induced_dom
+
+/-- A map into `Vec R` is continuous exactly when both coordinates are. -/
+theorem continuous_vec_iff
+    {X : Type*} [TopologicalSpace X] {f : X → Vec R} :
+    Continuous f ↔
+      Continuous (fun x => (f x).core) ∧
+        Continuous (fun x => (f x).beam) := by
+  constructor
+  · intro hf
+    have hpair : Continuous (fun x => Vec.toProd (f x)) :=
+      continuous_vecToProd.comp hf
+    exact ⟨continuous_fst.comp hpair, continuous_snd.comp hpair⟩
+  · rintro ⟨hcore, hbeam⟩
+    rw [continuous_induced_rng]
+    exact hcore.prodMk hbeam
+
+/-- Coordinatewise continuous functions assemble to a continuous CF2D state. -/
+theorem Continuous.vec_mk
+    {X : Type*} [TopologicalSpace X] {f g : X → R}
+    (hf : Continuous f) (hg : Continuous g) :
+    Continuous (fun x => Vec.mk (f x) (g x)) :=
+  continuous_vec_iff.mpr ⟨hf, hg⟩
+
+end Topology
+
+end DkMath.CosmicFormula.Rotation.CF2D
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index bf7b5a12..1e73b717 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -587,3 +587,25 @@ Archive
      段階として分離し、次は continuous four-edge path と定めた。
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DPhase` 成功 (8274 jobs)。
+
+### 2026/06/23 06:05 JST (Continuous closed four-phase path)
+
+1. レビュー補正:
+   - `phaseDepth_eq_half_iff` を追加し、midpoint が unique minimum であるという
+     module docstring の主張を定理化した。
+2. 位相 bridge:
+   - `CF2D.Topology.lean` を新設した。
+   - `Vec R` と `R × R` の座標同値、および積から誘導される topology を
+     実装した。
+   - `Vec` 値関数の連続性を2座標の連続性へ分解する API を追加した。
+3. Path:
+   - `SemanticCF2DPath.lean` を新設した。
+   - master edge と全 action translate の連続性を証明した。
+   - 各 edge を Mathlib `Path` として包装し、4本を `Path.trans` で連結した。
+   - core-zero exact order four により `Path z z` となる閉路を構成した。
+4. 境界:
+   - 得られたものは continuous piecewise-affine closed path であり、まだ
+     fixed-`q2` boundary path ではない。
+   - 次段階を `phaseDepth` による boundary normalization とした。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DPath` 成功 (8276 jobs)。
````
`````
