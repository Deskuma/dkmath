# Git diff / Report / Review

## Add: Analysis.DkReal.SemanticCF2DPhase

gch: e168553b09c5fddf7f4a6fe150f410d7f08d3a7c

## Report

次段階を実装しました。

- `phaseDepth` の平方完成、正値性、半折返し対称性
- affine master edge と端点則
- `q2(E(z,t)) = phaseDepth(t) * q2(z)`
- 一本の edge から作用反復で4相を生成
- seam 接続と位相番号の4周期性

実装: [SemanticCF2DPhase.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhase.lean)

「円から π を得る」のではなく、二次境界欠損の反復補正から正規化定数を構成し、後から `Real.pi` と同定する研究方針も整理しました。

[research-pregeometric-pi-program-067.md](/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md)

Gaussian 極限と π 同定は現時点では仮説として明確に隔離しています。次は `Vec ℝ` の位相 bridge と、4本を連結した continuous closed path です。

検証:

- `lake build DkMath.Analysis`: 成功、8285 jobs
- `git diff --check`: 成功

## Review

うむ。これはかなり良い進捗じゃ。
今回の更新で、離散四相から **連続四相の第一層** に入った。

添付差分では、新規 `SemanticCF2DPhase.lean` が追加され、`phaseDepth`、affine master edge、端点則、core-zero での `q2` profile、四相 translate、seam 接続、位相番号の 4 周期性まで実装されておる。さらに、\(\pi\) を円からではなく pre-geometric な正規化定数として構成し、後で `Real.pi` と握手する研究計画も `research-pregeometric-pi-program-067.md` として分離されている。

## 状況解説

今回の主役はこの係数じゃ。

$$
\operatorname{phaseDepth}(t)=(1-t)^2+t^2
$$

これは affine edge

$$
E(z,t)=(1-t)z+tA(z)
$$

が、固定された \(q2\) 境界からどれだけ沈むかを測る scalar profile になっている。

Lean 側では、

$$
q2(E(z,t))=\operatorname{phaseDepth}(t),q2(z)
$$

が証明された。

これは非常に良い。
円周をなぞっているのではなく、直線で進んだときの「境界欠損」を正確に測っている。

そして、

$$
\operatorname{phaseDepth}(1-t)=\operatorname{phaseDepth}(t)
$$

も入った。
つまり、状態そのものではなく、境界からの沈み込み量が半区間で折り返す。

ここが「連続化の最初の対称性」じゃな。

## 何が実装されたか

今回の実装は、設計通りにかなり小さく閉じている。

1. `phaseDepth` の定義と平方完成

$$
(1-t)^2+t^2=2\left(t-\frac12\right)^2+\frac12
$$

これにより、下界

$$
\frac12\le \operatorname{phaseDepth}(t)
$$

と正値性が得られた。

1. `semanticPhaseEdge`

一本の affine master edge を定義した。
これは円周でも曲線でもなく、単なる直線遷移。

1. `semanticPhaseEdge_q2_of_core_eq_zero`

core-zero 作用のとき、edge の \(q2\) が `phaseDepth` 倍になることを証明した。
ここで \((x,y)\mapsto(-y,x)\) が効き、交差項が消える。

1. `semanticPhaseEdgeAt`

四つの辺を別々に定義せず、一本の edge を action iterate で回す構成になっている。
これはかなり良い。

1. seam と 4 周期

隣接 edge の終端と次 edge の始端が一致し、さらに index が 4 周期で戻る。
これで連続閉路へ進む準備が整った。

## 良い判断

特に良いのは、まだ `Path` や正規化へ行かず、affine profile で止めているところじゃ。

今の段階で言えるのは、

```text
直線遷移は連続候補である。
しかし固定 q2 境界上にはない。
その境界欠損は phaseDepth で完全に測れる。
```

ここまで。

ここで「これは円です」と言わない。
ここで「角度です」とも言わない。
この抑制が効いておる。

## \(\pi\) 計画の評価

`research-pregeometric-pi-program-067.md` の分離も正しい。

狙いは、

```text
直線遷移
境界欠損
反復細分化
正規化係数
極限
Gaussian 的重み
pre-geometric normalization constant
Real.pi との同定
```

という流れじゃな。

そして現時点では、

```text
repeated affine correction converges
limiting weight is Gaussian
constant equals Real.pi
```

をまだ主張していない。
これは非常に大事。

\(\pi\) が `Real.pi` と握手する日は楽しみじゃが、今は焦らず、まず局所 profile の定理を固める段階。今回の文書はその姿勢がよく守られておる。

## レビュー上の注意点

ひとつだけ気になる点がある。

`SemanticCF2DPhase.lean` のモジュールコメントでは、`phaseDepth` が midpoint で unique minimum に達すると述べている。
実装では下界と midpoint の値は証明済みだが、**unique** まではまだ theorem として入っていないように見える。

よって、どちらかがよい。

1. theorem を追加する

$$
\operatorname{phaseDepth}(t)=\frac12 \leftrightarrow t=\frac12
$$

たとえば名前は、

```lean
phaseDepth_eq_half_iff
```

または、

```lean
phaseDepth_eq_min_iff
```

1. コメントを少し弱める

「minimum」まではよいが、「unique minimum」は theorem 追加後に書く。

この小さな整合性を取ると、文書と Lean の対応がさらに綺麗になる。

## 次の実装として自然なもの

次は報告通り、topological bridge じゃな。

ただし `Vec ℝ` に直接 topology を載せるか、`ℝ × ℝ` へ bridge するかは慎重に選ぶのがよい。

安全な順序はこう。

1. `Vec ℝ` と `ℝ × ℝ` の変換を作る
2. coordinatewise continuity を証明する
3. `semanticPhaseEdge` を `Path` に包む
4. 四本の path を seam で連結する
5. closed path として閉じる

ここでも、まだ boundary normalization へ行かなくてよい。
まずは「piecewise-affine closed path」を得る。

その後に、

$$
N(z,t)=\frac{1}{\sqrt{\operatorname{phaseDepth}(t)}}E(z,t)
$$

で固定 \(q2\) 境界へ戻す。
ここから平方根、割り算、連続性が本格的に必要になる。

## 総評

今回の更新はかなり良い。

到達点を一言で言えば、

```text
四相の離散 return から、円や角度を使わず、一本の直線遷移とその四 translate による連続化の代数核を得た。
```

そして、その直線遷移は境界を保たないが、壊れ方が

$$
(1-t)^2+t^2
$$

で完全に測れる。

これは、円由来ではない \(\pi\) へ向かうための、とてもよい第一歩じゃ。
`Real.pi` との握手はまだ先。だが、握手するための手は、ちゃんと形になり始めておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index d7c02f44..dcdfed03 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -13,6 +13,7 @@ import DkMath.Analysis.RealBridge
 import DkMath.Analysis.TaylorBridge
 import DkMath.Analysis.DkReal
 import DkMath.Analysis.DkReal.SemanticCF2D
+import DkMath.Analysis.DkReal.SemanticCF2DPhase
 
 #print "file: DkMath.Analysis"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 007f21d9..d0a7917f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -92,6 +92,13 @@ separated from the weaker zero-iterate-compatible periodicity predicates.
 Identity transported kernels fix every point; nonidentity transported kernels
 fix exactly the origin.
 
+[IMPLEMENTED: semantic-cf2d-phase-profile] `DkReal.SemanticCF2DPhase` fills one
+step of the core-zero order-four action by an affine edge. The edge leaves the
+fixed `q2` boundary by the exact factor
+`phaseDepth t = (1-t)^2 + t^2`. Square completion proves a positive lower bound
+of one half, and reflection about the midpoint proves the first continuous
+half-fold symmetry without introducing circles or angles.
+
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index f490227c..2e32c5cc 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1306,14 +1306,16 @@ theorem semanticMinimalPeriod_eq_four_of_core_eq_zero_of_ne_zero
 Keep the source in the nonnegative semiring until a signed DkReal layer is
 introduced; do not manufacture subtraction merely to mirror the real target.
 
-[TODO: semantic-cf2d-phase/master-edge] Fill one transition affinely in the
-semantic real target, from `z` to `semanticAct r z`.
+[IMPLEMENTED: semantic-cf2d-phase/master-edge] `SemanticCF2DPhase` fills one
+transition affinely in the semantic real target, from `z` to `semanticAct r z`.
 
-[TODO: semantic-cf2d-phase/four-translates] Generate all four transition edges
-by applying action iterates to the one master edge, and prove seam closure.
+[IMPLEMENTED: semantic-cf2d-phase/four-translates] All transition edges are
+generated by applying action iterates to the one master edge. Their endpoints
+form exact seams, and the family is four-periodic under a core-zero kernel.
 
-[TODO: semantic-cf2d-phase/half-fold-profile] Prove that the affine edge has
-`q2` profile `((1-t)^2 + t^2) * q2 z`, symmetric under `t ↦ 1-t`.
+[IMPLEMENTED: semantic-cf2d-phase/half-fold-profile] The affine edge has `q2`
+profile `((1-t)^2 + t^2) * q2 z`, symmetric under `t ↦ 1-t`, with a positive
+lower bound of one half.
 
 [TODO: semantic-cf2d-phase/path-concatenation] Package the four compatible
 edges as a closed Mathlib `Path`. This is a piecewise-affine loop, not yet a
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhase.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhase.lean
new file mode 100644
index 00000000..14fba55e
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhase.lean
@@ -0,0 +1,264 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2D
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DPhase"
+
+/-!
+# Affine phase transitions before circles and angles
+
+This module fills one step of the exact-order-four semantic action by an
+affine transition. It deliberately studies the transition before imposing a
+circle, an angle coordinate, or trigonometric functions.
+
+The affine edge does not remain on a fixed `q2` boundary. Its departure is
+instead measured exactly by
+
+`phaseDepth t = (1 - t)^2 + t^2`.
+
+This scalar profile is symmetric under `t ↦ 1 - t` and reaches its unique
+minimum at the midpoint. Thus the first continuous symmetry extracted from
+the four-state action is a reflection symmetry of boundary depth, rather than
+an assumed symmetry of a Euclidean circle.
+
+The profile is also the intended observation point for later refinement and
+normalization experiments. Any connection with Gaussian weights or a
+normalization constant must be proved in a separate limit layer; it is not
+assumed by the affine construction here.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+open DkMath.CosmicFormula.Rotation.CF2D
+
+noncomputable section
+
+/-!
+## The scalar half-fold profile
+
+Square completion exposes the midpoint reflection and the positive lower
+bound without geometric terminology.
+-/
+
+/--
+The relative `q2` depth of the affine transition between two consecutive
+core-zero action states.
+-/
+def phaseDepth (t : ℝ) : ℝ :=
+  (1 - t) ^ 2 + t ^ 2
+
+/-- Square completion centers the phase depth at the half transition. -/
+theorem phaseDepth_eq_two_sq_add_half (t : ℝ) :
+    phaseDepth t = 2 * (t - (1 / 2 : ℝ)) ^ 2 + 1 / 2 := by
+  simp [phaseDepth]
+  ring
+
+/-- The phase depth is bounded below by one half. -/
+theorem one_half_le_phaseDepth (t : ℝ) :
+    (1 / 2 : ℝ) ≤ phaseDepth t := by
+  rw [phaseDepth_eq_two_sq_add_half]
+  nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]
+
+/-- In particular, affine phase depth never vanishes. -/
+theorem phaseDepth_pos (t : ℝ) :
+    0 < phaseDepth t :=
+  lt_of_lt_of_le (by norm_num) (one_half_le_phaseDepth t)
+
+/-- Phase depth is nonnegative. -/
+theorem phaseDepth_nonneg (t : ℝ) :
+    0 ≤ phaseDepth t :=
+  (phaseDepth_pos t).le
+
+/--
+The inward depth is reflected about the midpoint of a transition.
+
+This is the first continuous half-fold symmetry obtained from the discrete
+four-state action.
+-/
+@[simp]
+theorem phaseDepth_one_sub (t : ℝ) :
+    phaseDepth (1 - t) = phaseDepth t := by
+  simp [phaseDepth]
+  ring
+
+/-- The affine transition begins on the original `q2` boundary. -/
+@[simp]
+theorem phaseDepth_zero :
+    phaseDepth 0 = 1 := by
+  norm_num [phaseDepth]
+
+/-- The affine transition ends on the next copy of the same boundary. -/
+@[simp]
+theorem phaseDepth_one :
+    phaseDepth 1 = 1 := by
+  norm_num [phaseDepth]
+
+/-- The midpoint is the deepest point of the affine transition. -/
+@[simp]
+theorem phaseDepth_half :
+    phaseDepth (1 / 2 : ℝ) = 1 / 2 := by
+  norm_num [phaseDepth]
+
+/-!
+## One affine master edge
+
+All later phase edges are intended to be action translates of this one
+formula. The definition remains coordinatewise so that no additional module
+structure is imposed on `Vec`.
+-/
+
+/--
+The affine transition from `z` to its next semantic action state.
+
+The parameter is an unrestricted real number. Restriction to the unit
+interval belongs to the later topological path wrapper.
+-/
+def semanticPhaseEdge
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
+  Vec.mk
+    ((1 - t) * z.core + t * (semanticAct r z).core)
+    ((1 - t) * z.beam + t * (semanticAct r z).beam)
+
+/-- Coordinate formula for the core component of the master edge. -/
+@[simp]
+theorem semanticPhaseEdge_core
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) :
+    (semanticPhaseEdge r z t).core =
+      (1 - t) * z.core + t * (semanticAct r z).core := rfl
+
+/-- Coordinate formula for the beam component of the master edge. -/
+@[simp]
+theorem semanticPhaseEdge_beam
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) :
+    (semanticPhaseEdge r z t).beam =
+      (1 - t) * z.beam + t * (semanticAct r z).beam := rfl
+
+/-- The master edge starts at its input state. -/
+@[simp]
+theorem semanticPhaseEdge_zero
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    semanticPhaseEdge r z 0 = z := by
+  cases z
+  simp [semanticPhaseEdge]
+
+/-- The master edge ends at the next action state. -/
+@[simp]
+theorem semanticPhaseEdge_one
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    semanticPhaseEdge r z 1 = semanticAct r z := by
+  cases z
+  simp [semanticPhaseEdge, semanticAct, UnitKernel.act, semanticUnitKernel,
+    semanticVec, Vec.star]
+
+/--
+For a core-zero kernel, the complete departure from the conserved `q2`
+boundary is the scalar factor `phaseDepth`.
+
+No circle or angle is used: the cross terms cancel solely because the
+boundary action sends `(x,y)` to `(-y,x)`.
+-/
+theorem semanticPhaseEdge_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : ℝ) :
+    Vec.q2 (semanticPhaseEdge r z t) =
+      phaseDepth t * Vec.q2 z := by
+  unfold semanticPhaseEdge
+  rw [semanticAct_of_core_eq_zero hcore]
+  cases z with
+  | mk x y =>
+      simp [phaseDepth, Vec.q2]
+      ring
+
+/--
+The `q2` observation of the second half of an affine transition is the
+reflection of the first half.
+
+The state-valued edge is not claimed to be fixed by this reflection; the
+symmetry belongs to its scalar boundary-depth observation.
+-/
+theorem semanticPhaseEdge_q2_one_sub_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : ℝ) :
+    Vec.q2 (semanticPhaseEdge r z (1 - t)) =
+      Vec.q2 (semanticPhaseEdge r z t) := by
+  rw [semanticPhaseEdge_q2_of_core_eq_zero hcore,
+    semanticPhaseEdge_q2_of_core_eq_zero hcore, phaseDepth_one_sub]
+
+/-!
+## One pattern transported through four phases
+
+The phase index does not select one of four separately written formulas.
+Instead it transports the single master edge by an iterate of the action.
+This is the formal content of “one pattern, turned four times.”
+-/
+
+/--
+The `k`th affine phase is the `k`-fold action translate of the master edge.
+-/
+def semanticPhaseEdgeAt
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : ℝ) : Vec ℝ :=
+  (semanticAct r)^[k] (semanticPhaseEdge r z t)
+
+/-- The `k`th translated edge starts at the `k`th discrete action state. -/
+@[simp]
+theorem semanticPhaseEdgeAt_zero
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    semanticPhaseEdgeAt r z k 0 = (semanticAct r)^[k] z := by
+  simp [semanticPhaseEdgeAt]
+
+/-- The `k`th translated edge ends at the next discrete action state. -/
+@[simp]
+theorem semanticPhaseEdgeAt_one
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    semanticPhaseEdgeAt r z k 1 = (semanticAct r)^[k + 1] z := by
+  rw [semanticPhaseEdgeAt, semanticPhaseEdge_one]
+  exact (Function.iterate_succ_apply (semanticAct r) k z).symm
+
+/--
+Adjacent translated edges meet at exactly the same state.
+
+This seam law is obtained from iteration alone; it does not require a
+topological quotient or a circular parameter.
+-/
+theorem semanticPhaseEdgeAt_seam
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    semanticPhaseEdgeAt r z k 1 =
+      semanticPhaseEdgeAt r z (k + 1) 0 := by
+  simp
+
+/-- Every translated edge has the same `q2` profile as the master edge. -/
+theorem semanticPhaseEdgeAt_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
+    Vec.q2 (semanticPhaseEdgeAt r z k t) =
+      phaseDepth t * Vec.q2 z := by
+  rw [semanticPhaseEdgeAt, semanticAct_iterate_q2,
+    semanticPhaseEdge_q2_of_core_eq_zero hcore]
+
+/--
+Core-zero exact order four makes the translated-edge family periodic in its
+phase index.
+-/
+theorem semanticPhaseEdgeAt_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
+    semanticPhaseEdgeAt r z (k + 4) t =
+      semanticPhaseEdgeAt r z k t := by
+  have hfour :
+      (semanticAct r)^[4] = id :=
+    (semanticExactActionOrderFour_of_core_eq_zero hcore).1
+  rw [semanticPhaseEdgeAt, semanticPhaseEdgeAt,
+    Function.iterate_add_apply, hfour]
+  rfl
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
new file mode 100644
index 00000000..eb33bfa2
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -0,0 +1,158 @@
+# Research Program 067: A Pre-Geometric Normalization Constant
+
+## Purpose
+
+This program investigates whether the constant later identified with
+Euclidean pi can first be characterized without assuming a circle, an angle,
+or polar coordinates.
+
+The starting data are instead:
+
+```text
+an exact-order-four action
+an affine filling of each discrete transition
+a conserved quadratic quantity q2 at the endpoints
+an exact scalar profile measuring departure from that boundary
+reflection symmetry of the profile
+refinement and normalization
+```
+
+The intention is not to redefine `Real.pi` prematurely. It is to construct an
+independent normalization constant from the transition mechanism and
+eventually prove a bridge theorem identifying it with `Real.pi`.
+
+## Proven Starting Point
+
+For a semantic core-zero kernel, one affine transition is
+
+```text
+E(z,t) = (1-t) z + t A(z).
+```
+
+Lean now verifies:
+
+```text
+q2(E(z,t)) = phaseDepth(t) q2(z),
+phaseDepth(t) = (1-t)^2 + t^2,
+phaseDepth(1-t) = phaseDepth(t),
+phaseDepth(t) >= 1/2 > 0.
+```
+
+The same edge is transported through all four phases by action iteration.
+Adjacent endpoints agree, and the edge family is periodic with phase index
+four.
+
+This is a continuous-symmetry precursor at the algebraic level: the state
+path is oriented, but its scalar boundary-depth observation folds about the
+midpoint.
+
+## Strategic Interpretation
+
+The current construction does not move along a circle. It moves along affine
+segments and records exactly how far the quadratic boundary law fails between
+the endpoints.
+
+This gives the following research order:
+
+```text
+linear transition
+  -> quadratic boundary defect
+  -> reflection symmetry
+  -> repeated refinement
+  -> normalization factors
+  -> limiting weight
+  -> normalization constant
+  -> comparison with Euclidean pi
+```
+
+Circular geometry is therefore a later model of an independently constructed
+limit law. It is not used to generate the law.
+
+## Why a Square Root May Appear
+
+A one-dimensional Gaussian normalization has the form
+
+```text
+G = integral over Real of exp(-x^2).
+```
+
+Its square is naturally a two-coordinate quantity:
+
+```text
+G^2 = double integral of exp(-(x^2 + y^2)).
+```
+
+The present CF2D invariant is also quadratic in two coordinates. This makes
+the distinction between a one-dimensional normalization constant and its
+two-dimensional square structurally relevant.
+
+This motivates, but does not yet prove, a future theorem of the form:
+
+```text
+transition normalization constant squared = Real.pi.
+```
+
+The square-root phenomenon must be derived from a dimension or product
+theorem, not inserted as notation.
+
+## Formal Milestones
+
+### Milestone A: continuous four-edge loop
+
+1. Equip the real CF2D target with an explicit topology or bridge it to
+   `Real × Real`.
+2. Package each affine edge as a Mathlib `Path`.
+3. Concatenate four seam-compatible paths.
+4. Prove endpoint closure independently of Euclidean terminology.
+
+### Milestone B: boundary normalization
+
+1. Define the positive correction `1 / sqrt (phaseDepth t)`.
+2. Prove that the normalized edge preserves the original `q2` value.
+3. Prove continuity of the normalized edge.
+4. Prove compatibility of normalization with all four action translates.
+
+### Milestone C: refinement law
+
+1. Define dyadic or rational subdivision of an affine phase.
+2. Express the total correction as a finite product or sum of logarithms.
+3. Prove compatibility under refinement.
+4. Identify the exact local quadratic term controlling the limit.
+
+### Milestone D: limit and Gaussian bridge
+
+1. Prove convergence of the refinement correction.
+2. Determine whether its limiting weight is Gaussian.
+3. Define the resulting normalization constant independently of `Real.pi`.
+4. Compare it with the standard Gaussian integral in Mathlib.
+
+### Milestone E: Euclidean identification
+
+1. Interpret fixed `q2` boundaries as Euclidean circles.
+2. Compare the normalized four-phase path with a standard circle
+   parametrization.
+3. Prove that the independently obtained normalization constant agrees with
+   `Real.pi`.
+4. Only then introduce an angular interpretation.
+
+## Guardrails
+
+The following claims are not established by the current implementation:
+
+```text
+repeated affine correction converges;
+the limiting weight is Gaussian;
+the resulting constant exists independently;
+that constant equals Real.pi;
+the affine four-edge loop itself is a circle.
+```
+
+The present result supplies a concrete quadratic and symmetric local
+mechanism from which these theorem obligations can be investigated.
+
+## Immediate Next Step
+
+The next implementation should be the topological bridge for the already
+proved affine edge family. It should stop after constructing the continuous
+closed four-edge path. Boundary normalization and limit arguments remain
+separate checkpoints.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 0e86c14d..eac3ebde 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -2,7 +2,11 @@
 
 ## Status
 
-Design checkpoint for the phase after the discrete exact-order-four result.
+Implementation in progress after the discrete exact-order-four result.
+
+The scalar profile, affine master edge, endpoint laws, exact core-zero `q2`
+profile, and half-fold observation theorem are implemented in
+`DkMath.Analysis.DkReal.SemanticCF2DPhase`.
 
 The current implementation proves a four-state return:
 
@@ -315,10 +319,20 @@ explicit.
 ## IX. Tagged Future Work
 
 ```text
-[TODO: semantic-cf2d-phase/master-edge]
-[TODO: semantic-cf2d-phase/four-translates]
-[TODO: semantic-cf2d-phase/half-fold-profile]
+[IMPLEMENTED: semantic-cf2d-phase/master-edge]
+[IMPLEMENTED: semantic-cf2d-phase/four-translates]
+[IMPLEMENTED: semantic-cf2d-phase/half-fold-profile]
+[TODO: semantic-cf2d-phase/path-topology]
 [TODO: semantic-cf2d-phase/path-concatenation]
 [TODO: semantic-cf2d-phase/boundary-normalization]
+[TODO: semantic-cf2d-phase/refinement-law]
+[TODO: semantic-cf2d-phase/gaussian-limit]
+[TODO: semantic-cf2d-phase/pi-identification]
 [TODO: semantic-cf2d-phase/euclidean-interpretation]
 ```
+
+The longer route from this local quadratic profile to a possible
+pre-geometric normalization constant is recorded in
+`research-pregeometric-pi-program-067.md`. That document separates proved
+transition laws from conjectural refinement, Gaussian, and identification
+stages.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 55fe1326..bf7b5a12 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -564,3 +564,26 @@ Archive
 5. 文書:
    - `task-trig-continuous-phase-065.md` を新設し、実装順と module boundary
      を記録した。
+
+### 2026/06/23 05:49 JST (Affine phase profile and four translates)
+
+1. 実装:
+   - `SemanticCF2DPhase.lean` を新設した。
+   - `phaseDepth t = (1-t)^2 + t^2`、平方完成、正値性、端点値、半折返し
+     対称性を証明した。
+   - 一本の `semanticPhaseEdge` とその端点則を実装した。
+2. 保存境界からの離脱:
+   - core-zero 作用について affine edge の `q2` が
+     `phaseDepth t * q2 z` と厳密に一致することを証明した。
+   - 状態そのものではなく、境界深度の観測値が `t -> 1-t` で折り返すことを
+     定理化した。
+3. 四相:
+   - `semanticPhaseEdgeAt` を作用反復による唯一の master edge の translate
+     として定義した。
+   - endpoint、seam、共通 `q2` profile、位相番号の4周期性を証明した。
+4. 研究方針:
+   - `research-pregeometric-pi-program-067.md` を追加した。
+   - refinement、Gaussian limit、独立な正規化定数、`Real.pi` 同定を未証明の
+     段階として分離し、次は continuous four-edge path と定めた。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DPhase` 成功 (8274 jobs)。
````
`````
