# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: e5cb4d215aa19ae8f39ae32a7faf9fee3230aacb

## Report

実装しました。`SemanticCF2DPhaseShift.lean` に以下を追加しています。

- `shiftedFiniteChartRel := Relation.EqvGen shiftedFiniteSeamRel`
- `shiftedFiniteChartSetoid`
- `ShiftedCyclicChart`
- `shiftedSemanticFinChartEval_eq_of_chartRel`
- `shiftedSemanticCyclicChartEval`
- `shiftedSemanticCyclicChartEval_mk`
- おまけとして `shiftedSemanticCyclicChartEval_q2`

これで seam relation は生成同値関係経由だけで扱い、chart evaluation は quotient に降りました。topology/path 構造は予定通り `[TODO: semantic-cf2d/shifted-cyclic-topology]` として残しています。

Docs も更新済みです。

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)

確認済みです。

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功しました。

## Review

うむ、今回も **採用でよい**。
これは checkpoint 104 の大きな転換点じゃ。前回までの finite chart layer が、今回は `Relation.EqvGen` による生成同値関係、`Setoid`、`ShiftedCyclicChart`、そして quotient 上の evaluation まで進んだ。しかも topology/path にはまだ進まず、代数的 seam quotient として止めている。これは非常に良い切り方じゃ。

## 1. 状況分析

今回追加された主な構造はこれじゃ。

```text id="p0cqfp"
shiftedFiniteChartRel
shiftedFiniteChartSetoid
ShiftedCyclicChart
shiftedSemanticFinChartEval_eq_of_chartRel
shiftedSemanticCyclicChartEval
shiftedSemanticCyclicChartEval_mk
shiftedSemanticCyclicChartEval_q2
```

これで、有限 chart は次の段階へ進んだ。

```text id="s7dmuz"
raw chart:
  Fin 4 × unitInterval

generating seam relation:
  (i, 1) と (finFourSucc i, 0) を貼る

generated equivalence:
  Relation.EqvGen shiftedFiniteSeamRel

quotient:
  ShiftedCyclicChart

descended evaluation:
  ShiftedCyclicChart から fixed q2 boundary への写像
```

つまり、四本の edge chart を貼り合わせた cyclic chart が、Lean の quotient object として出た。

## 2. 今回の本丸

一番重要なのは、評価関数が quotient に降りたことじゃ。

```lean id="ecm0hi"
def shiftedSemanticCyclicChartEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedCyclicChart) : LevelSet ℝ (Vec.q2 z)
```

これはかなり大きい。

これまでは chart の seam で値が一致する、という theorem だった。
今回は、その一致性を使って quotient 上の関数になった。

```text id="ca4zr4"
before:
  seam-compatible evaluation on representatives

after:
  well-defined evaluation on quotient charts
```

これは「貼り合わせた空間上で観測値が定まる」ということじゃ。

## 3. `Relation.EqvGen` を使ったのが良い

`shiftedFiniteSeamRel` 自体は、反射・対称・推移を持つ同値関係ではない。

それを直接 quotient にせず、

```lean id="ul2ub2"
def shiftedFiniteChartRel (p q : ShiftedFiniteChart) : Prop :=
  Relation.EqvGen shiftedFiniteSeamRel p q
```

としているのが良い。

これはかなり正しい。

```text id="xwfi5i"
shiftedFiniteSeamRel:
  seam の生成規則

shiftedFiniteChartRel:
  その生成規則から作った同値関係

ShiftedCyclicChart:
  同値関係で割った cyclic chart
```

この三段階の分離は、後で topology や path 構造を載せる時にも効く。

## 4. relation induction も良い

`shiftedSemanticFinChartEval_eq_of_chartRel` の証明方針も正しい。

```text id="qkcozi"
generating seam:
  already proved by shiftedSemanticFinChartEval_eq_of_seamRel

refl:
  rfl

symm:
  equality symmetry

trans:
  equality transitivity
```

つまり、生成 seam 上で評価が一致するなら、その同値閉包全体でも評価が一致する。
これは quotient evaluation の well-definedness そのものじゃ。

## 5. q2 theorem も良い

おまけとして入ったこれも良い。

```lean id="sfiepj"
theorem shiftedSemanticCyclicChartEval_q2
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : ShiftedCyclicChart) :
    Vec.q2 ((shiftedSemanticCyclicChartEval hcore z p).1) = Vec.q2 z
```

quotient の representative を開かずに、評価値が固定 `q2` 境界上にあると言える。

数式で読むならこうじゃ。

$$
\mathrm{q2}(\mathrm{cyclicEval}(p))=\mathrm{q2}(z)
$$

これは下流でかなり便利になる。

## 6. レビュー

今回の判断はとても良い。

特に良いのは、topology/path をまだ載せていないことじゃ。
quotient object と evaluation API が安定する前に topology を載せると、証明が一気に重くなる。

今回は、

```text id="qup82q"
quotient type:
  implemented

quotient evaluation:
  implemented

topology:
  delayed

path:
  delayed
```

という切り分けになっている。

これは Lean 実装としても、設計としても安全じゃ。

docs 側も、Remaining TODO が `shifted-cyclic-topology` に更新され、Euclidean reading はさらに後段に残されている。

## 7. 次の本質

次は topology に入ってもよい段階ではある。
ただし、いきなり quotient topology を載せる前に、quotient API の観測点をもう少し整えるのが安全じゃ。

今欲しいのは、quotient 上で seam が等式として読める thin API じゃ。

たとえば、

```text id="t6pld9"
mk of right endpoint chart:
  Quot.mk (i, 1)

mk of successor left endpoint chart:
  Quot.mk (succ i, 0)

theorem:
  these two quotient points are equal
```

これがあると、quotient が本当に seam を貼っていることを、評価関数とは独立に読める。

## 8. 次に狙うべき API

次は、representative constructors を薄く足すのが良い。

```text id="mw3sqq"
shiftedCyclicChartMk
shiftedCyclicChartLeft
shiftedCyclicChartRight
shiftedCyclicChartRight_eq_succLeft
```

これにより、quotient の中の有限四状態貼り合わせが public API として見える。

さらに、evaluation theorem も代表点用に欲しい。

```text id="kl3wf5"
cyclic eval at left chart:
  finite left endpoint

cyclic eval at right chart:
  finite right endpoint

cyclic eval respects right-succ-left:
  quotient equalityで同じ
```

これで topology に進む前の quotient observation layer が完成する。

## 9. topology は次の次でもよい

`Quot` に topology を載せるのは、Mathlib の quotient topology API に寄せる必要がある。
ここは重い可能性があるので、次の一投ではまだ「quotient point API」と「representative computation theorem」を優先するのが良い。

```text id="oxx5i5"
now:
  algebraic quotient evaluation

next:
  quotient representative / seam equality API

later:
  quotient topology

much later:
  Euclidean reading
```

この順なら安全じゃ。

## 10. 結論

今回の差分は採用でよい。

```text id="hhnw3r"
実装:
  良い。Relation.EqvGen で seam relation を同値閉包し、quotient を作った。

数学:
  良い。四本 chart の貼り合わせが、代数的 cyclic chart として成立した。

設計:
  良い。topology/path へ進まず、evaluation が quotient に降りるところで止めている。

次:
  quotient representative API と seam equality API を整え、その後に topology へ進む。
```

ぬしよ、これは大きい。
ついに「四本の path の連結」から、「chart を貼り合わせた cyclic quotient」へ移った。
まだ円ではない。まだ角度ではない。だが、固定 `q2` 境界を読む cyclic chart ができた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 744b6c07..03567132 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -208,9 +208,11 @@ and a four-cycle law. Finite edges expose endpoint aliases and
 center-to-successor-base compatibility, and the closed shifted path exposes
 source, target, and fixed-`q2` boundary-observation aliases. Finite base
 states are also packaged directly as points of the fixed square-mass level
-set. Finally, the pre-quotient chart layer evaluates `Fin 4 × unitInterval`
-into the same fixed boundary and proves compatibility across the finite seam
-relation. No quotient phase parameter is introduced yet.
+set. Finally, the finite chart layer evaluates `Fin 4 × unitInterval` into
+the same fixed boundary, closes the finite seam relation under
+`Relation.EqvGen`, packages the quotient as `ShiftedCyclicChart`, and
+descends chart evaluation to that quotient. Topology and path structure on
+the quotient are deliberately left to a later layer.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 06a91264..e5254045 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1493,11 +1493,12 @@ theorem shiftedSemanticFinFourLevelPath_q2
   (shiftedSemanticFinFourLevelPath hcore z t).2
 
 /-!
-## Finite chart evaluation before quotienting
+## Finite chart evaluation and seam quotient
 
 The next definitions expose the finite chart space for the shifted boundary:
 a finite edge index together with a local unit-interval parameter. The seam
-relation is recorded as a relation only; no quotient type is introduced here.
+relation is first recorded directly, then closed under Mathlib's generated
+equivalence relation so chart evaluation can descend to a quotient wrapper.
 -/
 
 /-- A finite shifted chart is one of four shifted edges and a local parameter. -/
@@ -1551,7 +1552,7 @@ theorem shiftedSemanticFinChartEval_at_right
 Finite seam relation between charts.
 
 It relates the right endpoint of edge `i` to the left endpoint of its finite
-successor. This is the intended input for a later quotient wrapper.
+successor. This is the generating relation for the later chart quotient.
 -/
 def shiftedFiniteSeamRel (p q : ShiftedFiniteChart) : Prop :=
   ∃ i : Fin 4,
@@ -1584,6 +1585,97 @@ theorem shiftedSemanticFinChartEval_eq_of_seamRel
   subst hq
   exact shiftedSemanticFinChartEval_right_eq_succ_left hcore z i
 
+/--
+Generated equivalence relation of the finite seam relation.
+
+This is the algebraic cyclic identification of endpoint charts. It deliberately
+does not add a topology or path structure to the quotient.
+-/
+def shiftedFiniteChartRel (p q : ShiftedFiniteChart) : Prop :=
+  Relation.EqvGen shiftedFiniteSeamRel p q
+
+/-- Setoid generated by the shifted finite seam relation. -/
+def shiftedFiniteChartSetoid : Setoid ShiftedFiniteChart :=
+  Relation.EqvGen.setoid shiftedFiniteSeamRel
+
+/--
+Finite shifted chart quotient by generated seam equivalence.
+
+This is a cyclic chart parameter only in the algebraic sense: seams are
+identified, but no quotient topology, path structure, or Euclidean reading is
+selected here.
+-/
+abbrev ShiftedCyclicChart :=
+  Quot shiftedFiniteChartSetoid
+
+/--
+Chart evaluation is compatible with the generated seam equivalence.
+
+The proof is pure relation induction: a generating seam is handled by
+`shiftedSemanticFinChartEval_eq_of_seamRel`, while reflexive, symmetric, and
+transitive closure steps follow from equality.
+-/
+theorem shiftedSemanticFinChartEval_eq_of_chartRel
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ)
+    {p q : ShiftedFiniteChart}
+    (hrel : shiftedFiniteChartRel p q) :
+    shiftedSemanticFinChartEval hcore z p =
+      shiftedSemanticFinChartEval hcore z q := by
+  induction hrel with
+  | rel _ _ h =>
+      exact shiftedSemanticFinChartEval_eq_of_seamRel hcore z h
+  | refl _ =>
+      rfl
+  | symm _ _ _ ih =>
+      exact ih.symm
+  | trans _ _ _ _ _ ih₁ ih₂ =>
+      exact ih₁.trans ih₂
+
+/--
+Evaluate a seam-quotiented shifted chart inside the fixed square-mass
+boundary.
+
+This is the first descended chart evaluation. It uses only the generated seam
+equivalence and remains pre-topological.
+-/
+def shiftedSemanticCyclicChartEval
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ)
+    (p : ShiftedCyclicChart) : LevelSet ℝ (Vec.q2 z) :=
+  Quot.lift
+    (shiftedSemanticFinChartEval hcore z)
+    (by
+      intro p q hrel
+      exact shiftedSemanticFinChartEval_eq_of_chartRel hcore z hrel)
+    p
+
+/-- Quotient evaluation computes to finite chart evaluation on representatives. -/
+@[simp]
+theorem shiftedSemanticCyclicChartEval_mk
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ)
+    (p : ShiftedFiniteChart) :
+    shiftedSemanticCyclicChartEval hcore z (Quot.mk _ p) =
+      shiftedSemanticFinChartEval hcore z p := rfl
+
+/--
+The quotiented chart evaluation still lands on the original `q2` boundary.
+
+This small observation is useful downstream because consumers of the quotient
+do not need to reopen its representative.
+-/
+theorem shiftedSemanticCyclicChartEval_q2
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ)
+    (p : ShiftedCyclicChart) :
+    Vec.q2 ((shiftedSemanticCyclicChartEval hcore z p).1) = Vec.q2 z :=
+  (shiftedSemanticCyclicChartEval hcore z p).2
+
 /-!
 [IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
 The shifted semantic edge uses the normalized center states of neighboring
@@ -1625,12 +1717,16 @@ facts.
 [IMPLEMENTED: semantic-cf2d/shifted-finite-chart]
 The finite chart space `Fin 4 × unitInterval` evaluates into the fixed `q2`
 boundary. Endpoint chart evaluations and seam-relation compatibility are
-proved before constructing any quotient.
+proved.
+
+[IMPLEMENTED: semantic-cf2d/shifted-cyclic-chart]
+The finite seam relation is closed under `Relation.EqvGen`, packaged as a
+setoid quotient `ShiftedCyclicChart`, and chart evaluation descends to the
+quotient as a fixed-`q2` boundary-valued function.
 
-[TODO: semantic-cf2d/shifted-cyclic-quotient]
-Use `ShiftedFiniteChart` modulo `shiftedFiniteSeamRel`, or an equivalent
-project-specific quotient wrapper, once chart evaluation compatibility is
-stable enough for downstream consumers.
+[TODO: semantic-cf2d/shifted-cyclic-topology]
+Add topology/path structure to the shifted cyclic chart quotient only after
+the quotient evaluation API is stable.
 -/
 
 /-!
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 91a40641..92bad1f5 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -478,6 +478,13 @@ shiftedSemanticFinChartEval_at_right
 shiftedFiniteSeamRel
 shiftedSemanticFinChartEval_right_eq_succ_left
 shiftedSemanticFinChartEval_eq_of_seamRel
+shiftedFiniteChartRel
+shiftedFiniteChartSetoid
+ShiftedCyclicChart
+shiftedSemanticFinChartEval_eq_of_chartRel
+shiftedSemanticCyclicChartEval
+shiftedSemanticCyclicChartEval_mk
+shiftedSemanticCyclicChartEval_q2
 ```
 
 The shifted normalized edge starts at the left normalized center candidate,
@@ -558,8 +565,34 @@ ShiftedFiniteChart = Fin 4 x unitInterval
 
 Chart evaluation maps each chart into the fixed `q2 z` level set. The seam
 relation identifies `(i, 1)` with `(finFourSucc i, 0)`, and Lean proves that
-chart evaluation is compatible with that relation. This prepares a quotient
-wrapper without choosing one yet.
+chart evaluation is compatible with that relation.
+
+The seam relation is now closed under Mathlib's generated equivalence
+relation:
+
+```text
+shiftedFiniteChartRel p q =
+  Relation.EqvGen shiftedFiniteSeamRel p q
+```
+
+The generated relation is packaged as a setoid quotient:
+
+```text
+ShiftedCyclicChart = Quot shiftedFiniteChartSetoid
+```
+
+Chart evaluation descends to this quotient:
+
+```text
+shiftedSemanticCyclicChartEval :
+  ShiftedCyclicChart -> LevelSet Real (Vec.q2 z)
+```
+
+The computation theorem `shiftedSemanticCyclicChartEval_mk` states that the
+quotient evaluation agrees with finite chart evaluation on representatives,
+and `shiftedSemanticCyclicChartEval_q2` records that the descended value still
+lies on the original fixed boundary. This is only an algebraic seam quotient;
+no quotient topology or quotient path structure has been selected yet.
 
 Candidate theorem directions:
 
@@ -641,7 +674,12 @@ depend on that reading.
 27. Implemented: add finite closed-path fixed-`q2` observation.
 28. Implemented: add finite chart evaluation into the fixed `q2` level set.
 29. Implemented: add finite seam relation and chart-evaluation seam compatibility.
-30. Later: add a Euclidean bridge that reads `1/8` full-cycle
+30. Implemented: close the finite seam relation under `Relation.EqvGen`.
+31. Implemented: package the generated relation as `ShiftedCyclicChart`.
+32. Implemented: descend chart evaluation to the quotient and expose its
+    representative computation theorem.
+33. Later: add topology/path structure to the shifted cyclic chart quotient.
+34. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -703,15 +741,20 @@ target, and fixed-`q2` observation aliases for the finite closed shifted path.
 Expose `ShiftedFiniteChart = Fin 4 x unitInterval`, evaluate it into the
 fixed `q2` boundary, record the finite seam relation, and prove chart
 evaluation compatibility across seams.
+
+[IMPLEMENTED: semantic-cf2d/shifted-cyclic-chart]
+Close the finite seam relation under `Relation.EqvGen`, package it as the
+setoid quotient `ShiftedCyclicChart`, and descend chart evaluation to a
+fixed-`q2` boundary-valued quotient evaluation. The computation theorem on
+representatives and the descended `q2` observation are also exposed.
 ```
 
 ## Remaining TODO Tags
 
 ```text
-[TODO: semantic-cf2d/shifted-cyclic-quotient]
-Use `ShiftedFiniteChart` modulo `shiftedFiniteSeamRel`, or an equivalent
-project-specific quotient wrapper, once chart evaluation compatibility is
-stable.
+[TODO: semantic-cf2d/shifted-cyclic-topology]
+Add topology/path structure to the shifted cyclic chart quotient only after
+the quotient evaluation API is stable.
 
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
 After the algebraic shifted-frame theorem is closed at the semantic path
````
`````
