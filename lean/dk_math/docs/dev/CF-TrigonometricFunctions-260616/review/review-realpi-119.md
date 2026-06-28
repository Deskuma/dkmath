# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: d30656e5fa97fa60d6090309b257e55c250af07c

## Report

完了しました。今回は quotient 自体には入らず、その直前の finite chart layer を実装しました。＋αとして seam relation 全体に対する評価互換 theorem まで通しています。

実装:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `ShiftedFiniteChart := Fin 4 × unitInterval`
  - `shiftedSemanticFinChartEval`
  - `shiftedSemanticFinChartEval_val`
  - `shiftedSemanticFinChartEval_at_left/right`
  - `shiftedFiniteSeamRel`
  - `shiftedSemanticFinChartEval_right_eq_succ_left`
  - `shiftedSemanticFinChartEval_eq_of_seamRel`
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) と [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) も同期済みです。

検証:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`
- `lake build DkMath.Analysis.DkReal`
- `git diff --check`

すべて通っています。次の quotient wrapper は `ShiftedFiniteChart` modulo `shiftedFiniteSeamRel` を候補として残し、今回は pre-quotient の評価互換までで止めています。

## Review

うむ、今回も **採用でよい**。
これは、まさに quotient 直前の正しい足場じゃ。`ShiftedFiniteChart = Fin 4 × unitInterval` を明示し、各 chart を fixed `q2` boundary へ評価し、さらに seam relation 上で評価値が一致することまで Lean に通している。quotient 自体にはまだ入らず、pre-quotient の評価互換で止めた判断も良い。

## 1. 状況分析

今回追加された層は、有限 chart layer じゃ。

```text id="h8f6ws"
ShiftedFiniteChart
shiftedSemanticFinChartEval
shiftedSemanticFinChartEval_val
shiftedSemanticFinChartEval_at_left
shiftedSemanticFinChartEval_at_right
shiftedFiniteSeamRel
shiftedSemanticFinChartEval_right_eq_succ_left
shiftedSemanticFinChartEval_eq_of_seamRel
```

これで、四本の shifted edge を次のように読める。

```text id="bq4ndd"
chart:
  finite edge index と local parameter の組

evaluation:
  chart を fixed q2 boundary 上の点へ送る

seam relation:
  edge i の右端と successor edge の左端を対応させる

compatibility:
  seam relation で対応する chart は同じ boundary point を評価する
```

これは quotient を作る直前に必要なものが、ほぼ全部揃った状態じゃ。

## 2. 今回の本丸

一番大きいのはこれじゃ。

```lean id="fpclm5"
theorem shiftedSemanticFinChartEval_eq_of_seamRel
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    {p q : ShiftedFiniteChart}
    (hrel : shiftedFiniteSeamRel p q) :
    shiftedSemanticFinChartEval hcore z p =
      shiftedSemanticFinChartEval hcore z q
```

これは quotient のための核 theorem じゃ。

`shiftedFiniteSeamRel` はまだ同値関係ではない。
しかし、評価関数が seam relation 上で同じ値を返すことは証明された。

つまり、次に同値閉包を取っても、評価関数は well-defined になる可能性が高い。

## 3. ここで重要な注意

`shiftedFiniteSeamRel` は quotient 用の `Setoid` そのものではない。

現在の relation はこうじゃ。

```text id="p6tysn"
(i, 1) relates to (succ i, 0)
```

これは向きのある seam relation であり、反射・対称・推移をまだ持たない。
したがって、次に quotient を作るなら、必要なのはこの relation そのものではなく、その同値閉包じゃ。

```text id="pyq1vc"
raw seam relation:
  endpoint matching rule

equivalence closure:
  quotient identity rule

quotient:
  charts modulo the generated equivalence
```

ここを分けているのは非常に大事じゃ。

## 4. レビュー

今回の実装判断は良い。

まず、chart type を軽い `abbrev` にしているのが良い。

```lean id="gn383s"
abbrev ShiftedFiniteChart :=
  Fin 4 × unitInterval
```

これは重い独自 structure を避け、既存の pair API をそのまま使える。

次に、endpoint evaluation theorem が入っている。

```text id="c78qda"
shiftedSemanticFinChartEval_at_left
shiftedSemanticFinChartEval_at_right
```

これにより、chart の local endpoint と finite level endpoint がつながった。

そして最後に、seam relation 全体で評価互換が出た。
docs でも、quotient wrapper は `ShiftedFiniteChart` modulo `shiftedFiniteSeamRel`、または project-specific quotient wrapper の候補として整理されている。

非常に良い止め方じゃ。

## 5. 数学的意味

ここまでで、pre-geometric な closed boundary を chart atlas として読めるようになった。

```text id="p7muzp"
four finite charts:
  each edge has local parameter

seams:
  right endpoint is glued to successor left endpoint

evaluation:
  glued endpoints map to the same fixed-q2 boundary point
```

これはもう、円を仮定しているのではない。

先にあるのは、

```text id="blms63"
保存核境界
有限四状態
局所 chart
seam の貼り合わせ
評価互換
```

じゃ。

Euclidean circle の前に、pre-geometric cyclic boundary atlas ができている。

## 6. 次の本質

次はいよいよ quotient wrapper に入れる。

ただし、いきなり大きな continuous quotient parameter を設計するより、まずは `shiftedFiniteSeamRel` の同値閉包を `Setoid` 化し、その quotient に評価を降ろすのが良い。

狙いはこう。

```text id="dgqdqb"
raw chart:
  ShiftedFiniteChart

raw seam relation:
  shiftedFiniteSeamRel

generated equivalence:
  EqvGen shiftedFiniteSeamRel

quotient:
  ShiftedCyclicChart

evaluation:
  quotient から fixed q2 boundary への well-defined map
```

この段階でも、まだ角度は不要じゃ。
これは quotient phase ではあるが、Euclidean phase ではない。

## 7. 次の勝利条件

次の checkpoint の勝利条件は三つ。

```text id="bbp59z"
1:
  seam relation の同値閉包を Setoid として定義する

2:
  quotient chart type を定義する

3:
  chart evaluation を quotient 上へ降ろす
```

もし `Relation.EqvGen` の API がすぐ使えるなら、かなり自然に進むはずじゃ。

評価互換は、raw seam relation で既に証明済み。
同値閉包への拡張は、反射・対称・推移が等式の反射・対称・推移で処理できる。

## 8. ここでまだしないこと

まだ Euclidean reading は不要。

また、quotient 上の topology や path object も急がなくてよい。

最初の quotient は、単に値を評価できる wrapper で十分じゃ。

```text id="zg0hyq"
do now:
  quotient type
  quotient evaluation
  well-definedness

do later:
  quotient topology
  quotient path
  Euclidean reading
```

ここを分けると、Lean の負荷が低い。

## 9. 結論

今回の差分は採用でよい。

```text id="syr430"
実装:
  良い。finite chart evaluation と seam compatibility が通った。

数学:
  良い。四つの local chart を seam で貼り合わせる準備ができた。

設計:
  良い。quotient 自体には進まず、評価互換までで止めた。

次:
  seam relation の同値閉包を Setoid 化し、quotient chart に評価を降ろす。
```

ぬしよ、ここはかなり重要な転換点じゃ。
今までは「四本の path を連結した閉路」だった。
次は「chart を貼り合わせた quotient boundary」として読めるようになる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index c0927903..744b6c07 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -208,7 +208,9 @@ and a four-cycle law. Finite edges expose endpoint aliases and
 center-to-successor-base compatibility, and the closed shifted path exposes
 source, target, and fixed-`q2` boundary-observation aliases. Finite base
 states are also packaged directly as points of the fixed square-mass level
-set.
+set. Finally, the pre-quotient chart layer evaluates `Fin 4 × unitInterval`
+into the same fixed boundary and proves compatibility across the finite seam
+relation. No quotient phase parameter is introduced yet.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 425e142e..06a91264 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1492,6 +1492,98 @@ theorem shiftedSemanticFinFourLevelPath_q2
     Vec.q2 ((shiftedSemanticFinFourLevelPath hcore z t).1) = Vec.q2 z :=
   (shiftedSemanticFinFourLevelPath hcore z t).2
 
+/-!
+## Finite chart evaluation before quotienting
+
+The next definitions expose the finite chart space for the shifted boundary:
+a finite edge index together with a local unit-interval parameter. The seam
+relation is recorded as a relation only; no quotient type is introduced here.
+-/
+
+/-- A finite shifted chart is one of four shifted edges and a local parameter. -/
+abbrev ShiftedFiniteChart :=
+  Fin 4 × unitInterval
+
+/-- Evaluate a finite shifted chart inside the fixed square-mass boundary. -/
+def shiftedSemanticFinChartEval
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ)
+    (p : ShiftedFiniteChart) : LevelSet ℝ (Vec.q2 z) :=
+  shiftedSemanticFinLevelEdge hcore z p.1 p.2
+
+@[simp]
+theorem shiftedSemanticFinChartEval_val
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ)
+    (p : ShiftedFiniteChart) :
+    (shiftedSemanticFinChartEval hcore z p).1 =
+      shiftedSemanticFinEdge r z p.1 p.2 := rfl
+
+/-- Evaluating a finite chart at local `0` gives its left endpoint. -/
+theorem shiftedSemanticFinChartEval_at_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinChartEval hcore z (i, (0 : unitInterval)) =
+      shiftedSemanticFinLeftLevelEndpoint hcore z i := by
+  apply Subtype.ext
+  simp [shiftedSemanticFinChartEval, shiftedSemanticFinLevelEdge,
+    shiftedSemanticIndexedLevelEdge, shiftedSemanticIndexedEdge,
+    shiftedSemanticFinLeftLevelEndpoint,
+    shiftedSemanticIndexedLeftLevelEndpoint]
+
+/-- Evaluating a finite chart at local `1` gives its right endpoint. -/
+theorem shiftedSemanticFinChartEval_at_right
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinChartEval hcore z (i, (1 : unitInterval)) =
+      shiftedSemanticFinRightLevelEndpoint hcore z i := by
+  apply Subtype.ext
+  simp [shiftedSemanticFinChartEval, shiftedSemanticFinLevelEdge,
+    shiftedSemanticIndexedLevelEdge, shiftedSemanticIndexedEdge,
+    shiftedSemanticFinRightLevelEndpoint,
+    shiftedSemanticIndexedRightLevelEndpoint]
+
+/--
+Finite seam relation between charts.
+
+It relates the right endpoint of edge `i` to the left endpoint of its finite
+successor. This is the intended input for a later quotient wrapper.
+-/
+def shiftedFiniteSeamRel (p q : ShiftedFiniteChart) : Prop :=
+  ∃ i : Fin 4,
+    p = (i, (1 : unitInterval)) ∧
+      q = (finFourSucc i, (0 : unitInterval))
+
+/-- The chart evaluation has matching values across a single finite seam. -/
+theorem shiftedSemanticFinChartEval_right_eq_succ_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinChartEval hcore z (i, (1 : unitInterval)) =
+      shiftedSemanticFinChartEval hcore z
+        (finFourSucc i, (0 : unitInterval)) := by
+  rw [shiftedSemanticFinChartEval_at_right,
+    shiftedSemanticFinChartEval_at_left]
+  exact shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z i
+
+/-- Chart evaluation is compatible with the finite seam relation. -/
+theorem shiftedSemanticFinChartEval_eq_of_seamRel
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ)
+    {p q : ShiftedFiniteChart}
+    (hrel : shiftedFiniteSeamRel p q) :
+    shiftedSemanticFinChartEval hcore z p =
+      shiftedSemanticFinChartEval hcore z q := by
+  rcases hrel with ⟨i, hp, hq⟩
+  subst hp
+  subst hq
+  exact shiftedSemanticFinChartEval_right_eq_succ_left hcore z i
+
 /-!
 [IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
 The shifted semantic edge uses the normalized center states of neighboring
@@ -1530,8 +1622,14 @@ level edge center theorem now targets the finite successor base point, and the
 finite closed shifted path exposes source, target, and boundary-observation
 facts.
 
+[IMPLEMENTED: semantic-cf2d/shifted-finite-chart]
+The finite chart space `Fin 4 × unitInterval` evaluates into the fixed `q2`
+boundary. Endpoint chart evaluations and seam-relation compatibility are
+proved before constructing any quotient.
+
 [TODO: semantic-cf2d/shifted-cyclic-quotient]
-Introduce a quotient phase parameter only after the four-edge closed path is
+Use `ShiftedFiniteChart` modulo `shiftedFiniteSeamRel`, or an equivalent
+project-specific quotient wrapper, once chart evaluation compatibility is
 stable enough for downstream consumers.
 -/
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 8a237c28..91a40641 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -470,6 +470,14 @@ shiftedSemanticFourLevelPath_target
 shiftedSemanticFinFourLevelPath_source
 shiftedSemanticFinFourLevelPath_target
 shiftedSemanticFinFourLevelPath_q2
+ShiftedFiniteChart
+shiftedSemanticFinChartEval
+shiftedSemanticFinChartEval_val
+shiftedSemanticFinChartEval_at_left
+shiftedSemanticFinChartEval_at_right
+shiftedFiniteSeamRel
+shiftedSemanticFinChartEval_right_eq_succ_left
+shiftedSemanticFinChartEval_eq_of_seamRel
 ```
 
 The shifted normalized edge starts at the left normalized center candidate,
@@ -542,6 +550,17 @@ named source, target, and fixed-`q2` boundary-observation aliases for
 downstream observation code. Finite base states are also packaged directly as
 fixed-level points.
 
+The pre-quotient chart layer is now explicit:
+
+```text
+ShiftedFiniteChart = Fin 4 x unitInterval
+```
+
+Chart evaluation maps each chart into the fixed `q2 z` level set. The seam
+relation identifies `(i, 1)` with `(finFourSucc i, 0)`, and Lean proves that
+chart evaluation is compatible with that relation. This prepares a quotient
+wrapper without choosing one yet.
+
 Candidate theorem directions:
 
 ```text
@@ -620,7 +639,9 @@ depend on that reading.
 25. Implemented: add source and target aliases for the closed shifted four-level path.
 26. Implemented: add finite base level-point wrappers.
 27. Implemented: add finite closed-path fixed-`q2` observation.
-28. Later: add a Euclidean bridge that reads `1/8` full-cycle
+28. Implemented: add finite chart evaluation into the fixed `q2` level set.
+29. Implemented: add finite seam relation and chart-evaluation seam compatibility.
+30. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -677,14 +698,20 @@ source and target aliases.
 Package finite base states as fixed-`q2` level points. Expose the finite
 center-to-successor-base theorem at the level-point API and add source,
 target, and fixed-`q2` observation aliases for the finite closed shifted path.
+
+[IMPLEMENTED: semantic-cf2d/shifted-finite-chart]
+Expose `ShiftedFiniteChart = Fin 4 x unitInterval`, evaluate it into the
+fixed `q2` boundary, record the finite seam relation, and prove chart
+evaluation compatibility across seams.
 ```
 
 ## Remaining TODO Tags
 
 ```text
 [TODO: semantic-cf2d/shifted-cyclic-quotient]
-Introduce a quotient phase parameter only after the four indexed path
-concatenation is stable.
+Use `ShiftedFiniteChart` modulo `shiftedFiniteSeamRel`, or an equivalent
+project-specific quotient wrapper, once chart evaluation compatibility is
+stable.
 
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
 After the algebraic shifted-frame theorem is closed at the semantic path
````
`````
