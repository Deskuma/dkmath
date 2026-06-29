# Git diff / Report / Review

## Add: docs: CF2D Pre-Geometric Boundary Action

gch: e8b1334a076ecbb54deada9408e85d3d33fcb2df

## Report

今は完成論文より、論文化前の整理段階と判断しました。

- 新規研究レポートを作成
- 主定理・五段構造・claims / non-claims を整理
- Euclidean 解釈を後段 bridge として分離
- `SemanticCF2D.lean` に論理的な節見出しを追加
- quarter-turn の表現を過大化しない形へ修正

新規資料: [CF2D-PreGeometric-Boundary-Action-Report.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-PreGeometric-Boundary-Action-Report.md)

全体ビルド 8566 jobs、`git diff --check` ともに成功しています。

## Review

うむ。今回の更新は、定理追加というより **研究主張の固定化** じゃな。
実装が進んだというより、「何を証明したのか」「何をまだ主張していないのか」を整理し、論文化前の足場を作った段階と見てよい。

## 状況解説

今回の中心は、新規資料 `CF2D-PreGeometric-Boundary-Action-Report.md` の追加じゃ。

ここで主張がかなり明確になった。

```text id="j8hjxx"
主張の本体:
  q2 保存境界上の exact order 4 action

後段の解釈:
  標準 Euclidean model を載せたとき quarter-turn と読める
```

つまり、DkMath が今証明しているのは、

```text id="6smyks"
90 度回転の別証明
```

ではない。

もっと前段の、

```text id="z12rcf"
円・角度・直交座標を導入する前に成立する
四相境界作用
```

じゃ。

この分離は非常に重要。
ここを曖昧にすると、「結局、普通の円の話でしょ？」と読まれてしまう。今回の文書化は、それを防いでいる。

## コード整理の評価

`SemanticCF2D.lean` に節見出しを追加したのは良い。

特にこの順序が明確になった。

```text id="mrhy3o"
semantic transport and boundary detection
boundary-preserving action
composition, inverse, and level-set actions
iteration, orbit, and point period
identity and fixed-point classification
real-side powers and low-order classification
pre-geometric four-phase boundary action
```

これは読者にも、将来の自分にも効く。

このファイルは定理が増えてかなり長くなっているので、節構造がないと「何を積み上げているのか」が見えにくい。
今回の整理で、証明の論理順序がかなり追いやすくなった。

## 一番良い点

今回いちばん強いのは、`claims / non-claims` を分けたことじゃ。

現在確立したものは、

```text id="31ub8e"
q2-preserving real action
faithful representation of real-side kernel powers
low-order finite-order classification
exact-order-four nonidentity boundary action
minimal point period four away from the origin
```

一方で、まだ主張していないものも明記されている。

```text id="6srz0x"
source-level signed kernel group
reconstructed angle parameter
topological classification of level sets
continuity or differentiability of angle map
bundled equivalence with Euclidean rotation
complete classification of all finite-order transported kernels
```

これはとても大事じゃ。
DkMath は発想が強いぶん、読者が過大に読む危険がある。先に「ここまでは言える」「ここから先はまだ言っていない」と線を引いたのは、論文化の準備として正しい。

## 表現修正の評価

`quarter-turn kernel` を直接言いすぎないように直したのも良い。

以前の表現だと、読者はすぐに幾何へ飛ぶ。
今回の表現では、

```text id="6v33cm"
first nonidentity exact-order boundary kernel
```

とした上で、

```text id="dg66us"
後段の Euclidean 解釈では quarter-turn と読める
```

という順序になっている。

これは今の思想に合っている。

## 数学的な位置づけ

今の成果は、こう整理できる。

```text id="p5c2k1"
q2:
  円ではなく、まず境界判定機

star:
  回転ではなく、まず kernel 合成

act_star:
  角度加法ではなく、まず作用合成への表現

faithfulness:
  作用から kernel へ戻る保証

first-quadrant transport:
  余分な代数的根を落とす境界条件
```

これらが揃った結果として、

```text id="a20f0o"
非零点が四相で戻る
```

が出ている。

ここにまだ円も角度もない。
だから「円以前の本質」としてかなりよく整理されておる。

## レビュー上の注意点

大きな問題は見えぬ。
ただし、今後の文書では `plane` という語だけ少し注意してもよい。

`plane action` は自然な表現ではあるが、読者によってはすぐ Euclidean plane を想像する。
厳密に pre-geometric を強調するなら、場面によっては、

```text id="3td8ip"
real CF2D target action
```

または、

```text id="g4m35q"
two-coordinate real target action
```

のような言い方もあり得る。

もちろん Lean 名としては `SemanticExactActionOrderFour` で十分良い。
説明文だけ、必要に応じて「Euclidean plane ではなく two-coordinate target」と補足すると安全じゃ。

## 次の自然な作業

この checkpoint の次は、すぐ定理を増やすより、まず橋の設計がよい。

```text id="zvb9v7"
1. pre-geometric theorem package の依存表を作る
2. Euclidean interpretation bridge の最小仮定を列挙する
3. q2 level set を circle と読むために必要な構造を明示する
4. exact order 4 を quarter-turn と読むために必要な角度構造を分離する
5. complex multiplication / rotation matrix との比較節を作る
```

この順序が良さそうじゃ。

実装側なら、次はまだ Real 側に留まり、

```text id="eez3vc"
非零 orbit 四点の pairwise distinct
fourth action coordinate law
level-set 上の nonzero minimal period 4
```

あたりが自然じゃな。

## 総評

今回の更新は、かなりよい consolidation じゃ。

言い換えると、DkMath はここで、

```text id="ouftzf"
円を使って四相を説明する
```

のではなく、

```text id="u13khr"
四相境界作用を証明し、その後に円として読む
```

という順序を獲得した。

これは大きい。
完成論文へ行く前に、この研究レポートを挟んだ判断も正しい。

今は「定理の量を増やす段階」から、「何を本体として掲げるかを固定する段階」へ移った。
円以前の本質が、かなり言葉とコードの両方で固まってきておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 307ff47b..cdc1b5d2 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -60,6 +60,13 @@ Nothing below requires the two coordinates to have been declared orthogonal
 axes or requires a convention measuring one full turn by 360 degrees.
 -/
 
+/-
+## Semantic transport and boundary detection
+
+Coordinates are transported independently. The first structure recorded after
+transport is the conserved `q2` boundary, without a geometric interpretation.
+-/
+
 /-- Interpret both coordinates of a CF2D vector as Mathlib real numbers. -/
 def semanticVec (z : Vec DkNNRealQ) : Vec ℝ :=
   ⟨semanticValue z.core, semanticValue z.beam⟩
@@ -125,6 +132,13 @@ theorem semanticUnitKernel_sq_add_sq (r : UnitKernel DkNNRealQ) :
   simpa [Vec.q2, semanticVec] using
     (UnitKernel.coe_q2 (semanticUnitKernel r))
 
+/-
+## Boundary-preserving action
+
+The action is introduced only after transport to the signed real target. This
+is the first layer that needs subtraction.
+-/
+
 /--
 Act on a real CF2D vector by first interpreting a nonnegative DkMath unit
 kernel as a real unit kernel.
@@ -164,6 +178,13 @@ theorem semanticAct_preservesQ2 (r : UnitKernel DkNNRealQ) :
     PreservesQ2 (semanticAct r) :=
   semanticAct_q2 r
 
+/-
+## Composition, inverse, and level-set actions
+
+Products and inverse kernels remain on the real side. Source preimages for
+these signed kernels are neither required nor asserted.
+-/
+
 /--
 Real-side product of two independently interpreted nonnegative DkMath
 kernels.
@@ -311,6 +332,12 @@ theorem semanticActLevelEquiv_apply
     (z : LevelSet ℝ rho2) :
     semanticActLevelEquiv r z = semanticActLevel r z := rfl
 
+/-
+## Iteration, orbit, and point period
+
+Period parameters in this section are iterate counts, not angle measures.
+-/
+
 /-- Every finite iterate of a transported action preserves square mass. -/
 theorem semanticAct_iterate_q2
     (r : UnitKernel DkNNRealQ) (n : ℕ) (z : Vec ℝ) :
@@ -550,6 +577,13 @@ theorem semanticMinimalPeriod_pos_of_positiveFiniteOrder
   semanticMinimalPeriod_pos h.1
     ((semanticFiniteOrder_iff r n).mp h.2 z)
 
+/-
+## Identity and fixed-point classification
+
+The classification uses only the unit equation and a two-variable linear
+system. No continuity or angular parameterization enters.
+-/
+
 /-- The transported kernel is the neutral real unit kernel. -/
 def SemanticIdentityKernel (r : UnitKernel DkNNRealQ) : Prop :=
   semanticUnitKernel r = UnitKernel.one ℝ
@@ -640,6 +674,14 @@ theorem semanticFixed_iff_eq_zero_of_not_identity
   exact ⟨eq_zero_of_semanticFixed_of_core_ne_one hcore,
     fun hz => hz ▸ semanticFixed_zero r⟩
 
+/-
+## Real-side powers and low-order classification
+
+Finite powers turn repeated action into polynomial coordinate identities.
+Orders one through three collapse to identity in the transported first
+quadrant; order four introduces the nonidentity boundary case.
+-/
+
 /--
 The `n`-fold product of a transported kernel, formed entirely in the real
 unit-kernel monoid.
@@ -1123,6 +1165,13 @@ theorem semanticExactActionOrderFour_of_core_eq_zero
     SemanticExactActionOrderFour r :=
   (semanticExactActionOrderFour_iff_core_eq_zero r).2 hcore
 
+/-
+## Pre-geometric four-phase boundary action
+
+The following results expose the four-step orbit and its point periods. A
+Euclidean circle and angle measure have not been chosen.
+-/
+
 /--
 At the exact-order-four boundary, the transported action exchanges the two
 coordinates with one sign change.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 7ebd2f5e..cf10edee 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -248,7 +248,8 @@ C = 1 or C = 0
 The `C = 1` branch is identity. In the `C = 0` branch, the unit equation and
 `S >= 0` force `S = 1`, so the transported kernel is `(0,1)`. Thus the
 first-quadrant restriction excludes nontrivial orders two and three but admits
-the quarter-turn kernel.
+the first nonidentity exact-order boundary kernel. Under the later standard
+Euclidean interpretation this kernel is read as a quarter-turn.
 
 Exact order four is now recorded explicitly. `SemanticExactKernelOrderFour`
 requires the fourth power to be neutral and excludes neutrality of powers
@@ -304,9 +305,10 @@ the minimal period of each point. Again, the four-step algebraic return is the
 primary theorem; interpreting the displayed orbit as motion around a circle
 comes later.
 
+The present chapter is now at a documentation and consolidation checkpoint.
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
-Both require signed arithmetic. They should wait for a signed DkReal layer
-rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
-remain on the real side, for example classifying low product orders through
-explicit semantic coordinate identities. Order reflection remains a separate,
+Both require signed arithmetic and should wait for a signed DkReal layer.
+Before crossing that boundary, the current pre-geometric result should be
+packaged as a research statement and its later Euclidean interpretation should
+be specified as a separate bridge. Order reflection remains an independent,
 heavier task.
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-PreGeometric-Boundary-Action-Report.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-PreGeometric-Boundary-Action-Report.md
new file mode 100644
index 00000000..31dba6c8
--- /dev/null
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-PreGeometric-Boundary-Action-Report.md
@@ -0,0 +1,176 @@
+# CF2D Pre-Geometric Boundary Action
+
+## Research Consolidation Report
+
+## Status
+
+This report records the current theorem-level result before a Euclidean circle
+or angle parameter is introduced. It is source material for a future paper,
+not a finished paper.
+
+The formal implementation is in:
+
+```text
+DkMath.Analysis.DkReal.SemanticCF2D
+```
+
+## Primary Result
+
+The primary result is not a theorem about a 90-degree rotation. It is a theorem
+about a boundary-preserving action with exact order four.
+
+For a transported nonnegative unit kernel with semantic core zero:
+
+```text
+semantic core = 0
+semantic beam = 1
+kernel product has exact order 4
+plane action has exact order 4
+every nonzero point has minimal period 4
+the zero point is fixed
+```
+
+The pointwise orbit is:
+
+```text
+(x,y)
+  -> (-y,x)
+  -> (-x,-y)
+  -> (y,-x)
+  -> (x,y).
+```
+
+This orbit is established entirely by coordinate algebra.
+
+## Boundary Before Geometry
+
+At the current formal layer, `q2` is a boundary detector:
+
+```text
+q2(x,y) = x^2 + y^2
+```
+
+Its level sets are conserved by the action. The development has not yet
+declared that the coordinates are orthogonal Euclidean axes, that these level
+sets are circles, that an angle parameter exists, or that a full turn is
+measured by 360 degrees. Those are additional structures and conventions, not
+hidden assumptions in the exact-order proof.
+
+## The Five-Part Mechanism
+
+The result comes from five interacting components.
+
+1. **Boundary detection:** `q2 = rho2` selects a conserved level set.
+2. **Kernel composition:** `star` defines composition of kernels.
+3. **Action representation:** `act_star` transfers multiplication to actions.
+4. **Faithfulness:** the action on the unit vector recovers the kernel.
+5. **Semantic root selection:** source nonnegativity removes inadmissible roots.
+
+The preservation equation alone does not produce the classification. The
+product, action, faithfulness, and semantic boundary are all essential.
+
+## Low-Order Classification
+
+The current formal classification is:
+
+```text
+power 1 = identity  iff core = 1
+power 2 = identity  iff core = 1
+power 3 = identity  iff core = 1
+power 4 = identity  iff core = 1 or core = 0
+exact order 4       iff core = 0
+```
+
+The first nonidentity finite-order case in the transported first quadrant is
+the semantic kernel `(0,1)`. Its intermediate real-side powers leave the first
+quadrant:
+
+```text
+(0,1)^2 = (-1,0)
+(0,1)^3 = (0,-1)
+(0,1)^4 = (1,0).
+```
+
+This explains why multiplication is performed after transport to `Real`
+rather than being forced into the nonnegative source.
+
+## Theorem Map
+
+The principal Lean declarations are:
+
+```text
+semanticAct_q2
+semanticAct_comp
+unitKernel_eq_one_of_act_eq_id
+semanticKernelPower_act
+semanticKernelFiniteOrder_iff
+semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero
+semanticExactKernelOrderFour_iff_core_eq_zero
+semanticExactKernelOrderFour_iff_exactActionOrderFour
+semanticExactActionOrderFour_iff_core_eq_zero
+semanticAct_of_core_eq_zero
+semanticAct_twice_of_core_eq_zero
+semanticAct_thrice_of_core_eq_zero
+semanticMinimalPeriod_eq_four_of_core_eq_zero_of_ne_zero
+```
+
+## Euclidean Interpretation Comes Later
+
+After choosing the standard Euclidean interpretation of `Real x Real`, `q2`
+becomes squared radius, its level sets become circles, and the coordinate
+action can be read as a quarter-turn.
+
+The bridge should be stated in this direction:
+
+```text
+pre-geometric algebraic structure
+  -> Euclidean model
+  -> familiar circle and angle terminology
+```
+
+The Euclidean model recognizes the existing algebraic behavior. It does not
+create or justify the exact-order theorem retroactively.
+
+## Claims And Non-Claims
+
+The current implementation establishes:
+
+```text
+a q2-preserving real action;
+faithful representation of real-side kernel powers;
+low-order finite-order classification;
+an exact-order-four nonidentity boundary action;
+minimal point period four away from the origin.
+```
+
+It does not yet establish:
+
+```text
+a source-level signed kernel group;
+a reconstructed angle parameter;
+topological classification of the level sets;
+continuity or differentiability of an angle map;
+a bundled equivalence with Euclidean rotation;
+a complete classification of all finite-order transported kernels.
+```
+
+## Publication Readiness
+
+The central observation is suitable for a research paper:
+
+```text
+circle-like four-phase behavior is already present in a smaller algebraic
+boundary-action structure, before circles and angles are introduced.
+```
+
+A finished paper should still add:
+
+1. an abstract definition of the boundary-action structure;
+2. a theorem separating algebraic assumptions from semantic root selection;
+3. a Euclidean interpretation theorem in a separate section;
+4. comparison with complex multiplication and rotation matrices;
+5. a precise novelty statement relative to existing formalizations;
+6. a reproducible theorem dependency table.
+
+The result is beyond a speculative note, but the correct present artifact is a
+research consolidation report and theorem package before a full manuscript.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index bf403df7..bd8532f9 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -228,6 +228,24 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/23 04:34 JST (Pre-geometric research consolidation)
+
+1. 判断:
+   - 完成論文へ直行せず、主定理・依存原理・非主張事項を固定する研究
+     consolidation report を先に作る段階とした。
+2. コード整理:
+   - `SemanticCF2D.lean` を semantic transport、boundary action、
+     composition/inverse、period、fixed point、low-order classification、
+     four-phase action の節へ整理した。
+3. 文書:
+   - `CF2D-PreGeometric-Boundary-Action-Report.md` を新設した。
+   - 境界判定機と作用が先にあり、円・角度は Euclidean model による後段
+     解釈であることを主軸にした。
+   - 現時点の claims / non-claims と論文化前の不足項目を明示した。
+4. 表現修正:
+   - 証明本体の段階で `(0,1)` を quarter-turn と断定せず、後段の標準
+     Euclidean 解釈でそう読める、という順序へ統一した。
+
 ### 2026/06/22 17:25 JST (Boundary first, geometry later)
 
 1. 文書整理:
````
`````
