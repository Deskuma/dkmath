# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: b152640886eecd3e47000a40c22bf0471a1bd117

## Report

完了しました。今回は finite fixed-`q2` observation API を仕上げ、＋αで closed path の境界観測 theorem まで追加しました。

実装:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedSemanticFinBaseLevelPoint`
  - `shiftedSemanticFinBaseLevelPoint_eq_indexed`
  - `shiftedSemanticFinBaseLevelPoint_val`
  - `shiftedSemanticFinLevelEdge_center_eq_succ_base_level_of_core_eq_zero`
  - `shiftedSemanticFinFourLevelPath_source/target`
  - `shiftedSemanticFinFourLevelPath_q2`
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) と [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) も同期済みです。

検証:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`
- `lake build DkMath.Analysis.DkReal`
- `git diff --check`

すべて通っています。continuous cyclic quotient はまだ開始せず、有限 `Fin 4` 上の fixed-boundary observation layer を閉じました。

## Review

うむ、今回も **採用でよい**。
これは checkpoint 104 の finite observation layer をきれいに閉じた差分じゃ。`Fin 4` 上の base level point、center-to-successor-base の level API、closed four-level path の source / target / fixed-`q2` observation まで揃った。報告どおり、continuous cyclic quotient にはまだ入らず、有限 `Fin 4` 上の fixed-boundary observation layer として閉じている。

## 1. 状況分析

今回追加された主な API はこれじゃ。

```text id="g6um3f"
shiftedSemanticFinBaseLevelPoint
shiftedSemanticFinBaseLevelPoint_eq_indexed
shiftedSemanticFinBaseLevelPoint_val
shiftedSemanticFinLevelEdge_center_eq_succ_base_level_of_core_eq_zero
shiftedSemanticFinFourLevelPath_source
shiftedSemanticFinFourLevelPath_target
shiftedSemanticFinFourLevelPath_q2
```

前回までで、`Fin 4` の有限 cyclic skeleton はできていた。
今回はそれを fixed-`q2` level-set 側の観測 API として仕上げている。

つまり、有限 index の読みがこうなった。

```text id="wy88h2"
finite base:
  Vec Real 側でも読める

finite base level point:
  fixed q2 boundary 内でも読める

finite level edge center:
  successor base level point に到達する

finite closed path:
  source と target が読める
  全点が fixed q2 boundary 上にある
```

これは良い。
下流コードが「この閉路はどこから始まり、どこへ戻り、境界上にいるのか」を直接読める。

## 2. 今回の本丸

一番重要なのは、finite base を level point として包装したことじゃ。

```lean id="j23940"
def shiftedSemanticFinBaseLevelPoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticIndexedBaseLevelPoint r z i.val
```

これで、`Fin 4` の base state が fixed `q2` 境界内の点として扱える。

これまでは、center theorem の到達先が indexed base level point だった。
今回で finite wrapper ができたため、finite API のまま閉じられる。

## 3. center-to-successor-base level theorem が良い

今回の核 theorem はこれじゃ。

```lean id="qpogcw"
theorem shiftedSemanticFinLevelEdge_center_eq_succ_base_level_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinLevelEdge hcore z i phaseCenter =
      shiftedSemanticFinBaseLevelPoint r z (finFourSucc i)
```

これはかなり良い。

意味はこう。

```text id="vbxfsj"
finite level edge i の中心:
  successor base level point
```

つまり、`Vec ℝ` ではなく fixed-boundary type の内部で、

```text id="rqcnxh"
edge i の中心が succ i の base に到達する
```

と言える。

これは後の cyclic quotient でも、観測点 API として強い。

## 4. closed path の fixed-q2 observation が良い

今回のもう一つの重要 theorem はこれじゃ。

```lean id="xqjfru"
theorem shiftedSemanticFinFourLevelPath_q2
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    Vec.q2 ((shiftedSemanticFinFourLevelPath hcore z t).1) = Vec.q2 z
```

これは実質的には、path の codomain が LevelSet なので自然に出る theorem じゃ。
しかし、名前付きで出しておく価値がある。

なぜなら、下流で閉路を扱う時に、

```text id="z1uuse"
この閉路の任意点は保存核境界上にある
```

と直接使えるからじゃ。

DkMath 的には、この theorem はかなり読みやすい。

$$
\mathrm{q2}(\mathrm{closedPath}(t))=\mathrm{q2}(z)
$$

この式は、円や半径を言わずに、保存核境界上の閉路であることを言っている。

## 5. source / target aliases も良い

```lean id="m5vvsa"
shiftedSemanticFinFourLevelPath_source
shiftedSemanticFinFourLevelPath_target
```

これも良い。

`Path.source` と `Path.target` で取れるが、名前付き alias にしておくと、ドキュメントや downstream theorem が読みやすくなる。

閉じた path であることが、命名上も見える。

```text id="ln984j"
source:
  finite closed path starts at base boundary point

target:
  finite closed path returns to the same boundary point
```

ここまで整うと、finite closed boundary path の public API としてかなり安定じゃ。

## 6. レビュー

今回の実装判断は正しい。

特に良いのは、continuous cyclic quotient に進まなかったことじゃ。
今やるべきことは、有限観測 API の穴を塞ぐことだった。

今回でそれがほぼ完了した。

```text id="xmpf6g"
Fin 4 successor:
  implemented

four-cycle:
  implemented

finite seam law:
  implemented

closed four-level path:
  implemented

finite base level points:
  implemented

closed path q2 observation:
  implemented
```

ここまで来たので、finite skeleton はかなり完成度が高い。

## 7. 次の本質

次はいよいよ `shifted-cyclic-quotient` を考えてよい段階じゃ。

ただし、いきなり quotient type を作るより、まず design document と small vocabulary を入れるのがよい。

理由は、quotient には複数の選択肢があるからじゃ。

```text id="y1rpad"
Option A:
  Fin 4 を主 index とし、各 edge 内 t を持つ Sigma 型

Option B:
  Nat index と t を持ち、k + 4 を同一視する quotient

Option C:
  normalized scalar parameter s を使い、s と s + 1 を同一視する quotient

Option D:
  既存の closed Path object を主対象にして、quotient は後段にする
```

今の DkMath route では、まず Option A が安全に見える。

つまり、連続 quotient に入る前に、

```text id="rri7ah"
finite edge index:
  i : Fin 4

local edge parameter:
  t : unitInterval
```

を組にした parameter space を作る。

これは quotient ではなく、四つの edge chart の disjoint union に近い。
そこに seam compatibility を加えると、後で quotient にできる。

## 8. 次の勝利条件

次の一投では、本格 quotient ではなく、`Fin 4 × unitInterval` 型の parameter chart を試すのが良い。

候補はこうじゃ。

```lean id="m5z3xg"
structure ShiftedFiniteChart where
  edge : Fin 4
  pos : unitInterval
```

または、簡単に `Fin 4 × unitInterval` を直接使ってもよい。

そこから evaluation function を作る。

```lean id="z4o6k8"
def shiftedSemanticFinEval
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ)
    (p : Fin 4 × unitInterval) :
    LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticFinLevelEdge hcore z p.1 p.2
```

そして、まずは endpoint compatibility を chart の seam relation として書く。

```text id="bcc6ua"
(i, 1) is compatible with (finFourSucc i, 0)
```

ここまでなら quotient を作らずに済む。
しかし、quotient 設計の準備はかなり進む。

## 9. cyclic quotient に入る前の注意

quotient を本当に作るなら、同値関係が必要じゃ。

少なくとも、

```text id="z1fy5d"
(i, 1) ~ (succ i, 0)
```

を入れる必要がある。

さらに、同値関係の反射・対称・推移を組むことになる。
これは少し重くなる可能性がある。

だから次は、まず relation を Prop として置き、必要な endpoint compatibility theorem を証明するのがよい。

```lean id="tqovdj"
def shiftedFiniteSeamRel (p q : Fin 4 × unitInterval) : Prop := ...
```

ただし、`unitInterval` の `0` と `1` の表現がやや面倒なら、最初は theorem の形だけでよい。

## 10. 結論

今回の差分は採用でよい。

```text id="hzs5df"
実装:
  良い。finite fixed-q2 observation API が閉じた。

数学:
  良い。Fin 4 の base / edge / closed path を fixed-boundary 内で読める。

設計:
  良い。continuous quotient に進まず、有限観測層を完成させた。

次:
  quotient の前段として、Fin 4 × unitInterval の finite chart evaluation と seam relation を設計する。
```

ぬしよ、これはかなり安定した。
有限四状態閉路はもう Lean API として読める。
次は「連続 quotient」に飛び込む前に、四つの edge chart と seam relation を明文化する段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 9948fb1c..c0927903 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -206,7 +206,9 @@ successor seam law for downstream code that wants a bounded index rather than
 raw natural-number indices. The finite successor has named small-step facts
 and a four-cycle law. Finite edges expose endpoint aliases and
 center-to-successor-base compatibility, and the closed shifted path exposes
-source and target aliases.
+source, target, and fixed-`q2` boundary-observation aliases. Finite base
+states are also packaged directly as points of the fixed square-mass level
+set.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index b99a8388..425e142e 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1175,6 +1175,24 @@ theorem shiftedSemanticFinBase_q2
     Vec.q2 (shiftedSemanticFinBase r z i) = Vec.q2 z :=
   shiftedSemanticIndexedBase_q2 r z i.val
 
+/-- The finite shifted base as a point of the original square-mass level set. -/
+def shiftedSemanticFinBaseLevelPoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
+    LevelSet ℝ (Vec.q2 z) :=
+  shiftedSemanticIndexedBaseLevelPoint r z i.val
+
+@[simp]
+theorem shiftedSemanticFinBaseLevelPoint_eq_indexed
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinBaseLevelPoint r z i =
+      shiftedSemanticIndexedBaseLevelPoint r z i.val := rfl
+
+@[simp]
+theorem shiftedSemanticFinBaseLevelPoint_val
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
+    (shiftedSemanticFinBaseLevelPoint r z i).1 =
+      shiftedSemanticFinBase r z i := rfl
+
 /-- The shifted normalized edge indexed by `Fin 4`. -/
 def shiftedSemanticFinEdge
     (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) (t : ℝ) : Vec ℝ :=
@@ -1336,6 +1354,16 @@ theorem shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero
         norm_num
         exact semanticAct_four_of_core_eq_zero hcore z
 
+/-- The finite level edge center reaches the finite successor base point. -/
+theorem shiftedSemanticFinLevelEdge_center_eq_succ_base_level_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinLevelEdge hcore z i phaseCenter =
+      shiftedSemanticFinBaseLevelPoint r z (finFourSucc i) := by
+  simpa using
+    shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero hcore z i
+
 /-- The finite shifted normalized edge as a fixed-boundary path. -/
 def shiftedSemanticFinLevelPath
     {r : UnitKernel DkNNRealQ}
@@ -1435,6 +1463,35 @@ theorem shiftedSemanticFourLevelPath_target
       shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 :=
   (shiftedSemanticFourLevelPath hcore z).target
 
+/-- Source endpoint of the finite alias for the closed shifted four-level path. -/
+theorem shiftedSemanticFinFourLevelPath_source
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinFourLevelPath hcore z 0 =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 :=
+  shiftedSemanticFourLevelPath_source hcore z
+
+/-- Target endpoint of the finite alias for the closed shifted four-level path. -/
+theorem shiftedSemanticFinFourLevelPath_target
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinFourLevelPath hcore z 1 =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 :=
+  shiftedSemanticFourLevelPath_target hcore z
+
+/--
+Every point of the finite closed shifted path lies on the original
+square-mass boundary.
+-/
+theorem shiftedSemanticFinFourLevelPath_q2
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : unitInterval) :
+    Vec.q2 ((shiftedSemanticFinFourLevelPath hcore z t).1) = Vec.q2 z :=
+  (shiftedSemanticFinFourLevelPath hcore z t).2
+
 /-!
 [IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
 The shifted semantic edge uses the normalized center states of neighboring
@@ -1467,6 +1524,12 @@ successor has named small-step facts and a four-cycle law, finite edges expose
 endpoint and center-to-successor facts, and the closed shifted path exposes
 source and target aliases.
 
+[IMPLEMENTED: semantic-cf2d/shifted-fin-observation]
+Finite base states are also packaged as fixed-`q2` level points. The finite
+level edge center theorem now targets the finite successor base point, and the
+finite closed shifted path exposes source, target, and boundary-observation
+facts.
+
 [TODO: semantic-cf2d/shifted-cyclic-quotient]
 Introduce a quotient phase parameter only after the four-edge closed path is
 stable enough for downstream consumers.
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index bdb01c6b..8a237c28 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -447,6 +447,7 @@ finFourSucc_two
 finFourSucc_three
 finFourSucc_four_cycle
 shiftedSemanticFinBase
+shiftedSemanticFinBaseLevelPoint
 shiftedSemanticFinEdge
 shiftedSemanticFinEdge_leftEndpoint
 shiftedSemanticFinEdge_rightEndpoint
@@ -456,6 +457,7 @@ shiftedSemanticFinEdge_center_eq_succ_base_of_core_eq_zero
 shiftedSemanticFinPath
 shiftedSemanticFinLevelEdge
 shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero
+shiftedSemanticFinLevelEdge_center_eq_succ_base_level_of_core_eq_zero
 shiftedSemanticFinLevelPath
 shiftedSemanticFinRightLevelEndpoint_eq_succ_left
 shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left
@@ -465,6 +467,9 @@ shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left
 shiftedSemanticFinFourLevelPath
 shiftedSemanticFourLevelPath_source
 shiftedSemanticFourLevelPath_target
+shiftedSemanticFinFourLevelPath_source
+shiftedSemanticFinFourLevelPath_target
+shiftedSemanticFinFourLevelPath_q2
 ```
 
 The shifted normalized edge starts at the left normalized center candidate,
@@ -533,7 +538,9 @@ This is still a finite cyclic index, not a continuous quotient phase
 parameter. The successor has named values for `0 -> 1 -> 2 -> 3 -> 0` and a
 four-cycle theorem. Finite shifted edges also expose endpoint aliases and a
 center-to-successor-base theorem. The closed shifted four-level path exposes
-named source and target aliases for downstream observation code.
+named source, target, and fixed-`q2` boundary-observation aliases for
+downstream observation code. Finite base states are also packaged directly as
+fixed-level points.
 
 Candidate theorem directions:
 
@@ -611,7 +618,9 @@ depend on that reading.
 23. Implemented: add small-step and four-cycle API for `finFourSucc`.
 24. Implemented: add finite endpoint aliases and center-to-successor-base compatibility.
 25. Implemented: add source and target aliases for the closed shifted four-level path.
-26. Later: add a Euclidean bridge that reads `1/8` full-cycle
+26. Implemented: add finite base level-point wrappers.
+27. Implemented: add finite closed-path fixed-`q2` observation.
+28. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -663,6 +672,11 @@ successor and prove the corresponding cyclic seam law. The successor has
 named small-step facts and a four-cycle law, finite edges expose endpoint and
 center-to-successor-base compatibility, and the closed shifted path has named
 source and target aliases.
+
+[IMPLEMENTED: semantic-cf2d/shifted-fin-observation]
+Package finite base states as fixed-`q2` level points. Expose the finite
+center-to-successor-base theorem at the level-point API and add source,
+target, and fixed-`q2` observation aliases for the finite closed shifted path.
 ```
 
 ## Remaining TODO Tags
````
`````
