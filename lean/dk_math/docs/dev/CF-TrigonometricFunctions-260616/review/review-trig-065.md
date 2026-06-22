# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: f99ba458b8c213cd1bdc4d779f4e979deaba6651

## Report

`note-trig-064.md` の観点を強く反映しました。

- `q2` はまず境界判定機
- `star` と `act_star` が作用を生成
- 円・直交・角度・90度は後から載せる解釈
- exact order 4 が先に成立することをコード・論文草稿へ明記
- 非零点の最小周期が正確に 4 と証明
- 原点は固定点として区別

検証は対象 8273 jobs、全体 8566 jobs、`git diff --check` すべて成功です。

## Review

うむ。今回の進捗はかなり強い。
これは「円以前の本質」を、コードと文書の両方に固定した更新じゃ。単なる説明追加ではなく、**円・角度・90度という後付け語彙を Lean 証明から明確に切り離した** のが大きい。

## レビュー結論

良い更新じゃ。方針は正しい。

今回の主結果はこれ。

```text
q2 boundary
-> composable action
-> exact order 4
-> nonzero point minimal period 4
-> Euclidean interpretation later
```

つまり、いま証明された本体は「90度回転」ではない。

本体は、

```text
円や角度を仮定せずに成立する
exact-order-four q2 保存作用
```

じゃ。

ここをコード冒頭、task 文書、paper draft、History に明記したのは非常に良い。これで読者が「これは三角関数の別証明？」と誤解する前に、「いや、三角関数以前の境界作用だ」と案内できる。

## 実装面の重要点

今回追加された中で一番大きいのは、core zero の作用を座標式として出したことじゃ。

```lean
semanticAct_of_core_eq_zero
```

これにより、core zero 境界では作用が

$$
(x,y)\mapsto(-y,x)
$$

として明示された。

さらに、

```lean
semanticAct_twice_of_core_eq_zero
semanticAct_thrice_of_core_eq_zero
```

で二回・三回の作用も明示された。これにより、四相 orbit が完全に見える。

$$
(x,y)\mapsto(-y,x)\mapsto(-x,-y)\mapsto(y,-x)\mapsto(x,y)
$$

これは見た目には quarter-turn だが、定理の段階ではまだ角度ではない。
ここが非常に良い。

## 最小周期 4 の証明が強い

以前は「作用全体が exact order 4」と言えた。
今回さらに進んで、

```lean
semanticMinimalPeriod_eq_four_of_core_eq_zero_of_ne_zero
```

により、非零点は正確に minimal period 4 と証明された。

これは大きな前進じゃ。

なぜなら、作用全体の exact order と、各点の周期は別物だからじゃ。原点は固定点であり、最小周期は 1。したがって「作用が exact order 4 だから全点が 4 周期」とは言えない。

今回の更新はそこを正しく分離している。

```text
global action:
  exact order 4

zero point:
  fixed

nonzero point:
  minimal period 4
```

この区別は後でかなり効く。
特に「一周」「四相」「回転」「螺旋」「自己相似」へ進むとき、固定点と非零 orbit の違いは避けて通れぬ。

## 数学的に何が見えたか

今回の核心はこれじゃ。

```text
q2 は円ではなく、まず境界判定機である。
```

この言い換えは重要。

$$
q2(x,y)=x^2+y^2
$$

を見た瞬間、普通は「円」と読みたくなる。
しかし、それは Euclidean 解釈を載せた後の読みじゃ。

Lean 証明の段階では、

```text
保存 level set を選ぶ境界条件
```

として扱っている。

そして `star` が kernel の合成を定め、`act_star` がそれを作用合成へ移し、faithfulness が作用から kernel へ戻る。第一象限制約が余分な根を落とす。

この流れはかなり美しい。

```text
保存則が場所を決める
積が運動を作る
作用法則が運動を実現する
忠実性がズレを消す
第一象限境界が admissible な根を選ぶ
```

つまり「保存量だけではダメ」という前回の整理とも一致している。

保存量だけなら \(x^4+y^4=1\) でも境界はある。
だが、二乗の \(q2\) では `star` と作用合成が噛み合う。
そこが条件として露出した。

## 文書面の評価

`Before Circles And Before Angles` は良い節名じゃ。
かなり読者に伝わりやすい。

特に、

```text
the q2-preserving action has exact order four
```

であって、

```text
the action is a 90-degree rotation of a circle
```

ではない、という対比は非常に良い。

この対比は残すべきじゃ。
DkMath の主張を過剰にせず、しかし本質を強く見せられる。

## 気になる点・改善候補

大きな問題は見えぬ。
ただ、次に進めるなら補題を少し足すとよい。

まず、四回作用の座標式を明示してもよい。

```lean
semanticAct_four_times_of_core_eq_zero
```

内容は、

```lean
semanticAct r (semanticAct r (semanticAct r (semanticAct r z))) = z
```

既に finite order から出せるが、座標 orbit の完結としてあると文書説明に強い。

次に、原点固定を core zero 文脈でも明示するとよい。

```lean
semanticAct_zero_of_core_eq_zero
```

既存の `semanticFixed_zero` があるなら不要だが、読者向け orbit 節では便利じゃ。

さらに、非零点の orbit 四点が互いに異なることを theorem 化できると強い。

```text
z ≠ 0 なら
z, r z, r^2 z, r^3 z は全て異なる
```

これは minimal period 4 から言えるはずじゃ。
Petal の四相・非衝突・NoLift へ橋を架けるときにも使える。

## 次の山

この更新で、三角関数以前の四相核はかなり固まった。
次は二方向ある。

ひとつは、CF2D 内で進める道。

```text
非零点 orbit の四点 distinct
level set 上の action minimal period
core zero action の four-cycle equivalence
angle-free quarter-turn theorem
```

もうひとつは、Petal へ接続する道。

```text
exact order 4:
  正規化された四相の閉じ

Petal spiral:
  四相は戻るが scale は進む

normalize:
  scale を割り戻すと同型相似に戻る
```

今回の「円以前、角度以前」の整理は、Petal 接続にもかなり効く。
なぜなら Petal 側でも、円ではなく「相」「一周」「成長」「正規化」が主役だからじゃ。

## 総評

今回の更新は、かなり重要な節目じゃ。

到達点を一言で言うなら、

```text
円を仮定せず、角度を仮定せず、非零点が正確に四相で戻る q2 保存作用を得た。
```

しかも、原点は固定点として分離されている。
これにより「作用の exact order」と「点ごとの minimal period」が混同されなくなった。

これは強い。
円以前の本質が、かなり Lean の定理として地面に降りてきたぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index b04a51d9..307ff47b 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -20,6 +20,20 @@ shows that the quadratic invariant
 
 is preserved by that interpretation.
 
+The logical order of this file is deliberately pre-geometric:
+
+1. `q2` is a boundary detector selecting a conserved level set;
+2. `star` specifies how kernels compose;
+3. `act_star` represents that composition as successive actions;
+4. faithfulness recovers kernel equality from equality of actions;
+5. coordinate nonnegativity removes roots outside the transported boundary.
+
+At this stage no circle, orthogonal coordinate frame, angle, full turn, or
+degree measure has been defined. In particular, the primary exact-order-four
+result is an algebraic statement about a `q2`-preserving action. Its later
+interpretation as a quarter-turn on a Euclidean circle is an additional model
+of the already-proved structure, not an assumption used by the proof.
+
 The bridge uses only the semiring laws already proved for `semanticValue`.
 It does not require subtraction, decidable comparison, order reflection, or
 any analytic theorem about trigonometric functions.
@@ -35,6 +49,17 @@ open DkMath.CosmicFormula.Rotation.CF2D
 
 noncomputable section
 
+/-
+The boundary-and-action layer comes first. Geometric terminology belongs to a
+later interpretation layer:
+
+  conserved q2 boundary -> composable action -> finite-order classification
+  -> optional Euclidean reading as circles and angles.
+
+Nothing below requires the two coordinates to have been declared orthogonal
+axes or requires a convention measuring one full turn by 360 degrees.
+-/
+
 /-- Interpret both coordinates of a CF2D vector as Mathlib real numbers. -/
 def semanticVec (z : Vec DkNNRealQ) : Vec ℝ :=
   ⟨semanticValue z.core, semanticValue z.beam⟩
@@ -1057,6 +1082,9 @@ theorem semanticExactKernelOrderFour_iff_core_eq_zero
 /--
 The transported plane action has exact order four: its fourth iterate is the
 identity function, while none of its first three positive iterates is.
+
+This is the primary statement. Calling the action a 90-degree rotation would
+require a later Euclidean interpretation and an angle-measure convention.
 -/
 def SemanticExactActionOrderFour (r : UnitKernel DkNNRealQ) : Prop :=
   SemanticFiniteOrder r 4 ∧
@@ -1095,6 +1123,134 @@ theorem semanticExactActionOrderFour_of_core_eq_zero
     SemanticExactActionOrderFour r :=
   (semanticExactActionOrderFour_iff_core_eq_zero r).2 hcore
 
+/--
+At the exact-order-four boundary, the transported action exchanges the two
+coordinates with one sign change.
+
+This coordinate law is proved before assigning any geometric meaning to the
+coordinates. Its later Euclidean reading as a quarter-turn is optional.
+-/
+theorem semanticAct_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    semanticAct r z = Vec.mk (-z.beam) z.core := by
+  have hbeam := semanticUnitKernel_beam_eq_one_of_core_eq_zero hcore
+  cases z with
+  | mk x y =>
+      simp [semanticAct, UnitKernel.act, semanticUnitKernel, semanticVec,
+        Vec.star, hcore, hbeam]
+
+/-- Two boundary actions negate both coordinates. -/
+theorem semanticAct_twice_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    semanticAct r (semanticAct r z) = Vec.mk (-z.core) (-z.beam) := by
+  calc
+    semanticAct r (semanticAct r z) =
+        Vec.mk (-(semanticAct r z).beam) (semanticAct r z).core :=
+      semanticAct_of_core_eq_zero hcore (semanticAct r z)
+    _ = Vec.mk (-z.core) (-z.beam) := by
+      rw [semanticAct_of_core_eq_zero hcore]
+
+/-- Three boundary actions reverse the first exchange law. -/
+theorem semanticAct_thrice_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    semanticAct r (semanticAct r (semanticAct r z)) =
+      Vec.mk z.beam (-z.core) := by
+  calc
+    semanticAct r (semanticAct r (semanticAct r z)) =
+        Vec.mk (-(semanticAct r (semanticAct r z)).beam)
+          (semanticAct r (semanticAct r z)).core :=
+      semanticAct_of_core_eq_zero hcore
+        (semanticAct r (semanticAct r z))
+    _ = Vec.mk z.beam (-z.core) := by
+      rw [semanticAct_twice_of_core_eq_zero hcore]
+      simp
+
+/-- A nonzero vector cannot return after one boundary action. -/
+theorem not_semanticPeriodic_one_of_core_eq_zero_of_ne_zero
+    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (hz : z ≠ Vec.mk 0 0) :
+    ¬SemanticPeriodic r z 1 := by
+  intro hperiodic
+  change semanticAct r z = z at hperiodic
+  rw [semanticAct_of_core_eq_zero hcore] at hperiodic
+  cases z with
+  | mk x y =>
+      simp only [Vec.mk.injEq] at hperiodic
+      apply hz
+      simp only [Vec.mk.injEq]
+      constructor <;> linarith [hperiodic.1, hperiodic.2]
+
+/-- A nonzero vector cannot return after two boundary actions. -/
+theorem not_semanticPeriodic_two_of_core_eq_zero_of_ne_zero
+    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (hz : z ≠ Vec.mk 0 0) :
+    ¬SemanticPeriodic r z 2 := by
+  intro hperiodic
+  change semanticAct r (semanticAct r z) = z at hperiodic
+  rw [semanticAct_twice_of_core_eq_zero hcore] at hperiodic
+  cases z with
+  | mk x y =>
+      simp only [Vec.mk.injEq] at hperiodic
+      apply hz
+      simp only [Vec.mk.injEq]
+      constructor <;> linarith [hperiodic.1, hperiodic.2]
+
+/-- A nonzero vector cannot return after three boundary actions. -/
+theorem not_semanticPeriodic_three_of_core_eq_zero_of_ne_zero
+    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (hz : z ≠ Vec.mk 0 0) :
+    ¬SemanticPeriodic r z 3 := by
+  intro hperiodic
+  change semanticAct r (semanticAct r (semanticAct r z)) = z at hperiodic
+  rw [semanticAct_thrice_of_core_eq_zero hcore] at hperiodic
+  cases z with
+  | mk x y =>
+      simp only [Vec.mk.injEq] at hperiodic
+      apply hz
+      simp only [Vec.mk.injEq]
+      constructor <;> linarith [hperiodic.1, hperiodic.2]
+
+/--
+Every nonzero vector has minimal period four under the boundary action.
+
+The origin remains fixed, so exact order of the whole action does not mean
+that every point has point period four.
+-/
+theorem semanticMinimalPeriod_eq_four_of_core_eq_zero_of_ne_zero
+    {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (hz : z ≠ Vec.mk 0 0) :
+    semanticMinimalPeriod r z = 4 := by
+  have horder := semanticExactActionOrderFour_of_core_eq_zero hcore
+  have hperiodic : SemanticPeriodic r z 4 :=
+    (semanticFiniteOrder_iff r 4).mp horder.1 z
+  have hpos : 0 < semanticMinimalPeriod r z :=
+    semanticMinimalPeriod_pos (by norm_num) hperiodic
+  have hle : semanticMinimalPeriod r z ≤ 4 :=
+    Function.IsPeriodicPt.minimalPeriod_le (by norm_num) hperiodic
+  have hneOne : semanticMinimalPeriod r z ≠ 1 := by
+    intro hperiod
+    apply not_semanticPeriodic_one_of_core_eq_zero_of_ne_zero hcore hz
+    rw [semanticPeriodic_iff_minimalPeriod_dvd, hperiod]
+  have hneTwo : semanticMinimalPeriod r z ≠ 2 := by
+    intro hperiod
+    apply not_semanticPeriodic_two_of_core_eq_zero_of_ne_zero hcore hz
+    rw [semanticPeriodic_iff_minimalPeriod_dvd, hperiod]
+  have hneThree : semanticMinimalPeriod r z ≠ 3 := by
+    intro hperiod
+    apply not_semanticPeriodic_three_of_core_eq_zero_of_ne_zero hcore hz
+    rw [semanticPeriodic_iff_minimalPeriod_dvd, hperiod]
+  omega
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 3cd8a085..ac74e349 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -149,6 +149,7 @@ BridgeNNReal / BridgeReal:
   order dividing four is equivalent to semantic core zero or one
   exact kernel order four is equivalent to semantic coordinates `(0,1)`
   exact kernel order four agrees with exact order of the plane action
+  every nonzero point has minimal period four under the core-zero action
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index ca908df1..7ebd2f5e 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -130,6 +130,13 @@ SemanticExactActionOrderFour
 semanticExactKernelOrderFour_iff_exactActionOrderFour
 semanticExactActionOrderFour_iff_core_eq_zero
 semanticExactActionOrderFour_of_core_eq_zero
+semanticAct_of_core_eq_zero
+semanticAct_twice_of_core_eq_zero
+semanticAct_thrice_of_core_eq_zero
+not_semanticPeriodic_one_of_core_eq_zero_of_ne_zero
+not_semanticPeriodic_two_of_core_eq_zero_of_ne_zero
+not_semanticPeriodic_three_of_core_eq_zero_of_ne_zero
+semanticMinimalPeriod_eq_four_of_core_eq_zero_of_ne_zero
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -272,6 +279,31 @@ The preservation law alone would not classify finite order. The classification
 comes from preservation, the addition/product law, faithful action, and the
 first-quadrant semantic boundary acting together.
 
+The conceptual order is boundary first, action second, geometry later.
+`q2` initially acts as a boundary detector for conserved level sets; it has
+not yet been identified with Euclidean squared radius. The exact-order-four
+action is therefore proved before any circle, orthogonality, angle, full-turn,
+or degree convention exists. After choosing the standard Euclidean model, the
+same algebraic action can be read as a quarter-turn. That geometric reading is
+a model of the theorem, not an ingredient of its proof.
+
+The boundary action now has an explicit coordinate orbit without geometric
+terminology:
+
+```text
+(x,y)
+  -> (-y,x)
+  -> (-x,-y)
+  -> (y,-x)
+  -> (x,y)
+```
+
+For every nonzero vector this sequence has minimal period four. The origin is
+fixed, so exact order of the action as a function must remain distinct from
+the minimal period of each point. Again, the four-step algebraic return is the
+primary theorem; interpreting the displayed orbit as motion around a circle
+comes later.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-WhyThisIsEnough-PaperDraft.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-WhyThisIsEnough-PaperDraft.md
index ef3c0341..466893f9 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-WhyThisIsEnough-PaperDraft.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-WhyThisIsEnough-PaperDraft.md
@@ -94,6 +94,81 @@ Analytic task:
 Phase 1 completes the algebraic task and verifies that the standard real
 functions instantiate it.
 
+## Before Circles And Before Angles
+
+The strongest reading of the current result begins before Euclidean geometry.
+The primary objects are not a circle and an angle. They are a boundary
+predicate and an action:
+
+```text
+q2:
+  detects the conserved boundary
+
+star:
+  defines composition of kernels
+
+act_star:
+  transfers kernel composition to composition of actions
+
+faithfulness:
+  recovers the kernel from its action
+
+first-quadrant transport:
+  removes algebraic roots outside the semantic boundary
+```
+
+This order matters. The statement proved for the distinguished boundary
+kernel is:
+
+```text
+the q2-preserving action has exact order four
+```
+
+It is not initially:
+
+```text
+the action is a 90-degree rotation of a circle
+```
+
+The latter sentence contains additional information not present in the
+algebraic definitions. Reading `q2(x,y) = x^2 + y^2` as squared Euclidean
+radius requires a choice of a Euclidean plane, equally scaled orthogonal axes,
+and the usual geometric interpretation of its level sets. Reading exact order
+four as 90 degrees additionally requires a notion of angle, a full turn, and a
+degree convention.
+
+None of those choices is used in the Lean proof. What Lean establishes first
+is a composable boundary-preserving mechanism with four-step return and no
+earlier positive return. Once the standard Euclidean model is supplied, the
+same mechanism is recognized as a quarter-turn. Geometry does not generate
+the algebraic behavior here; geometry is a later interpretation in which the
+already-proved behavior has a familiar name.
+
+This gives a more precise explanation of the construction's strength:
+
+```text
+the preservation law locates the motion;
+the product law generates the motion;
+the action law realizes the motion;
+faithfulness makes the realization exact;
+the semantic boundary selects the admissible roots.
+```
+
+The usual circle and trigonometric descriptions are therefore models of this
+earlier algebraic structure.
+
+The pointwise orbit makes the distinction concrete:
+
+```text
+(x,y) -> (-y,x) -> (-x,-y) -> (y,-x) -> (x,y).
+```
+
+For a nonzero state this orbit has minimal period four. The zero state remains
+fixed. Thus exact order four of the action is a global function statement; it
+does not assert that every state has the same point period. Neither statement
+requires a circle or an angle. Those concepts explain the orbit after a
+Euclidean model is chosen.
+
 ## Compass, Pin, String, And Pen
 
 The construction has a classical geometric analogy.
@@ -102,7 +177,7 @@ One does not need to solve real analysis in order to draw a circle.  A compass
 is enough.  A pin, a string, and a pen are also enough.  These devices enforce
 a constraint: the distance from the center remains fixed.
 
-The CF2D implementation does the formal analogue.  Instead of first building
+The CF2D implementation does the formal analogue. Instead of first building
 all analytic properties of `sin` and `cos`, it installs an algebraic device:
 
 ```text
@@ -117,9 +192,10 @@ action:
 ```
 
 The theorem `UnitKernel.q2_act` says that this device keeps the square mass
-fixed.  This is the Lean version of "the string length remains fixed."  Once
-the invariant is built into the kernel, the circle-like behavior follows from
-algebra.
+fixed. This is the Lean version of "the string length remains fixed." More
+precisely, the theorem first gives invariant level sets. Calling those level
+sets circles is justified only after the standard Euclidean interpretation is
+chosen.
 
 This analogy also explains why the code is short.  The implementation is not
 simulating motion point-by-point.  It specifies the preserving mechanism.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 080ae49d..bf403df7 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -228,6 +228,30 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 17:25 JST (Boundary first, geometry later)
+
+1. 文書整理:
+   - `note-trig-064.md` の観測をコード冒頭、現場資料、論文草稿へ反映した。
+   - `q2` をまず保存 level set の境界判定機として位置付けた。
+   - 円、直交座標、角度、一周、度数法は後段の Euclidean 解釈であり、
+     Lean 証明の前提ではないことを明記した。
+2. 原理:
+   - 保存則が境界を決め、`star` が合成を決める。
+   - `act_star` が合成を作用へ移し、忠実性が戻り道を保証する。
+   - 第一象限制約が transport 可能な根を選別する。
+3. 実装:
+   - core zero の作用を `(x,y) -> (-y,x)` と座標表示した。
+   - 二回・三回作用の座標式を追加した。
+   - 非零点が 1, 2, 3 回では戻らず、最小周期が正確に 4 であることを
+     証明した。原点は固定点として区別される。
+4. 結論:
+   - 主結果は「90 度回転」ではなく、円や角度以前の
+     exact-order-four `q2` 保存作用である。
+   - 標準 Euclidean 構造へ写した後に、同じ作用を円上の quarter-turn と
+     解釈できる。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 05:27 JST (Exact order four)
 
 1. 実施:
````
`````
