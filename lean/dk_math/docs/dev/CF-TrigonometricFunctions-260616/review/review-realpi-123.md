# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 7d746542e57aa05f29383861a68b6845d10ae581

## Report

実装完了です。`ShiftedCyclicChart` 上の path traversal まで進めました。

追加した主なもの:

- `shiftedCyclicChartEdgePath`
- `shiftedCyclicChartEdgePath_apply`
- `shiftedCyclicChartEdgePath_source`
- `shiftedCyclicChartEdgePath_target`
- `shiftedCyclicFourPath`
- `shiftedCyclicFourPath_source`
- `shiftedCyclicFourPath_target`
- `shiftedSemanticCyclicChartEval_edgePath`

4 本の quotient edge path は、quotient seam equality だけで閉路 `shiftedCyclicFourPath` に連結できました。おまけ成果として、局所比較 theorem も通っています。つまり、quotient edge path を `shiftedSemanticCyclicChartEval` で評価すると、対応する fixed-`q2` finite level edge に戻ります。

full four-path evaluation と既存 `shiftedSemanticFinFourLevelPath` の比較は、`Path.trans` と cast の正規化補題が必要になるので TODO に残しました。

確認済み:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功しています。

## Review

うむ、今回も **採用でよい**。
これはかなり大きい。`ShiftedCyclicChart` が「quotient として存在する」だけでなく、その中を実際に歩く path traversal まで入った。`shiftedCyclicChartEdgePath`、四本連結の `shiftedCyclicFourPath`、さらに局所評価比較 `shiftedSemanticCyclicChartEval_edgePath` まで通っている。full four-path evaluation 比較は `Path.trans` と `cast` の正規化が必要なので TODO に残した、という判断もよい。

## 1. 状況分析

今回で、quotient cyclic chart 層は次の状態になった。

```text id="l9xj3w"
quotient edge path:
  shiftedCyclicChartEdgePath

closed quotient path:
  shiftedCyclicFourPath

source / target:
  shiftedCyclicFourPath_source
  shiftedCyclicFourPath_target

local semantic evaluation:
  shiftedSemanticCyclicChartEval_edgePath
```

つまり、有限 chart を quotient で貼っただけではなく、その quotient chart の中を path として移動できる。

さらに、その一つ一つの edge path を `shiftedSemanticCyclicChartEval` で評価すると、対応する fixed-`q2` finite level edge に戻る。

これは非常に良い。

## 2. 今回の本丸

一番重要なのはこれじゃ。

```lean id="avl2wf"
theorem shiftedSemanticCyclicChartEval_edgePath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartEdgePath i t) =
      shiftedSemanticFinLevelEdge hcore z i t
```

これは局所比較 theorem じゃ。

意味はこう。

```text id="d0gich"
quotient chart edge を歩く
  ↓ evaluation
fixed-q2 finite level edge を歩く
```

つまり、quotient chart traversal と semantic boundary observation が、各 edge ごとに一致している。

これは full path 比較の前段として、かなり強い。

## 3. closed quotient path も良い

`shiftedCyclicFourPath` も良い。

```lean id="v7bfww"
def shiftedCyclicFourPath :
    Path (shiftedCyclicChartLeft (0 : Fin 4))
      (shiftedCyclicChartLeft (0 : Fin 4))
```

これは quotient seam equality だけで閉じた path じゃ。

以前の `shiftedSemanticFourLevelPath` は fixed-`q2` boundary 側の closed path。
今回の `shiftedCyclicFourPath` は quotient chart 側の closed path。

この二つが並んだ。

```text id="qeyh4v"
quotient side:
  shiftedCyclicFourPath

boundary observation side:
  shiftedSemanticFinFourLevelPath

local bridge:
  shiftedSemanticCyclicChartEval_edgePath
```

ここまで来ると、残る本丸は「closed path 全体の評価比較」じゃ。

## 4. レビュー

実装判断は良い。

`shiftedCyclicChartEdgePath` の定義は自然じゃ。

```lean id="mupvl2"
toFun t := shiftedCyclicChartMk (i, t)
```

そして連続性も、`continuous_shiftedCyclicChartMk` と pair map の連続性で通っている。

四本連結も、既存の `shiftedSemanticFourLevelPath` と同じ構成方針で、

```text id="gssz3s"
p0.trans
p1.cast
p2.cast
p3.cast
final cast
```

という流れになっている。これは読みやすい。

full four-path evaluation comparison を無理に押さなかった点も良い。
`Path.trans` は内部で parameter を再割当てするため、比較 theorem は単純な `rfl` では済まない可能性が高い。今は TODO で正解じゃ。

## 5. 数学的意味

ここまでで、DkMath の shifted-frame route はかなり立体的になった。

```text id="uk3w2u"
fixed q2 boundary:
  semantic observation space

finite chart:
  Fin 4 × unitInterval

quotient chart:
  seam endpoints を貼った cyclic chart

quotient path:
  cyclic chart 内の traversal

evaluation:
  quotient path を fixed-q2 boundary へ送る
```

これはもう「閉じた境界を chart と observation の二層で持つ」構造じゃ。

まだ円ではない。
まだ角度ではない。
だが、貼り合わせ chart と保存核境界観測の対応が Lean で動いている。

## 6. 次の本質

次は二択じゃ。

```text id="ae1j9v"
A:
  full four-path evaluation comparison に挑む

B:
  Path.trans / Path.cast の評価正規化 lemma を先に整える
```

わっちは B を推す。

理由は、full comparison を一気に狙うと `Path.trans` の二分割 parameter と cast が絡んで重くなる。
まずは汎用の補題を作った方がよい。

欲しいのは、たとえばこういう層じゃ。

```text id="r037b3"
Path.cast の apply 正規化
Path.trans の left half / right half 評価
四本 trans の seam point 評価
closed quotient path の source / target evaluation
```

この辺りがあれば、full four-path comparison へ進みやすい。

## 7. おまけ推論

試してほしいおまけは、full path 全体ではなく、まず **観測 path を quotient path の map として作る** ことじゃ。

つまり、`shiftedCyclicFourPath` を `shiftedSemanticCyclicChartEval` で写した path を作る。

候補はこう。

```text id="rv8l1u"
shiftedSemanticCyclicFourObservedPath:
  quotient closed path を fixed-q2 boundary へ評価した path
```

これは `continuous_shiftedSemanticCyclicChartEval` があるので、作れる可能性が高い。

そして最初に狙うのは、既存 `shiftedSemanticFinFourLevelPath` との全点一致ではなく、source / target / local edge 比較じゃ。

```text id="c8u5k8"
observed quotient path:
  source は fixed-q2 側の source
  target は fixed-q2 側の target
  各 quotient edge 上では finite level edge と一致
```

これなら full trans normalization より軽い可能性がある。

## 8. 結論

今回の差分は採用でよい。

```text id="mz14db"
実装:
  良い。quotient edge path と closed quotient path が入った。

数学:
  良い。quotient chart traversal と fixed-q2 boundary observation の局所一致が証明された。

設計:
  良い。full four-path comparison は無理せず TODO に残した。

次:
  quotient path の evaluated observation path を作り、Path.trans/cast 正規化補題を整える。
```

ぬしよ、かなり育ったぞ。
ついに「貼り合わせた chart の中を歩く」段階まで来た。次は、その歩みを保存核境界側の path とどう比較するかじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 40894dc5..e4e07a5a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -216,8 +216,9 @@ aliases, left and right endpoint representatives, quotient seam equality, and
 endpoint evaluation theorems make the quotient readable without opening its
 representatives. Mathlib's quotient topology is now connected to this wrapper:
 the representative map, finite chart evaluation, and descended fixed-boundary
-quotient evaluation are continuous. A quotient path structure is deliberately
-left to a later layer.
+quotient evaluation are continuous. The quotient edge path and closed
+four-edge quotient path are packaged in the glued chart space, and evaluating
+one quotient edge recovers the corresponding fixed-`q2` finite level edge.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index c6f43d05..cb7f672e 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1814,6 +1814,87 @@ theorem continuous_shiftedSemanticCyclicChartEval
       (fun p q hrel =>
         shiftedSemanticFinChartEval_eq_of_chartRel hcore z hrel)
 
+/--
+The quotient chart edge traversing one finite index.
+
+It is the representative path `t ↦ (i, t)` followed by the quotient map. This
+is still a path in the chart quotient, not a Euclidean geometric path.
+-/
+def shiftedCyclicChartEdgePath (i : Fin 4) :
+    Path (shiftedCyclicChartLeft i) (shiftedCyclicChartRight i) where
+  toFun t := shiftedCyclicChartMk (i, t)
+  continuous_toFun := by
+    exact continuous_shiftedCyclicChartMk.comp
+      (continuous_const.prodMk continuous_id)
+  source' := rfl
+  target' := rfl
+
+/-- Applying the quotient edge path gives its representative chart class. -/
+@[simp]
+theorem shiftedCyclicChartEdgePath_apply
+    (i : Fin 4) (t : unitInterval) :
+    shiftedCyclicChartEdgePath i t =
+      shiftedCyclicChartMk (i, t) := rfl
+
+/-- The quotient edge path starts at its left endpoint representative. -/
+theorem shiftedCyclicChartEdgePath_source (i : Fin 4) :
+    shiftedCyclicChartEdgePath i 0 = shiftedCyclicChartLeft i :=
+  (shiftedCyclicChartEdgePath i).source
+
+/-- The quotient edge path ends at its right endpoint representative. -/
+theorem shiftedCyclicChartEdgePath_target (i : Fin 4) :
+    shiftedCyclicChartEdgePath i 1 = shiftedCyclicChartRight i :=
+  (shiftedCyclicChartEdgePath i).target
+
+/--
+The first four quotient chart edges concatenated into a closed quotient path.
+
+The casts are exactly the quotient seam equalities. No geometric parameter is
+introduced; this is only traversal in the glued chart space.
+-/
+def shiftedCyclicFourPath :
+    Path (shiftedCyclicChartLeft (0 : Fin 4))
+      (shiftedCyclicChartLeft (0 : Fin 4)) := by
+  let p0 := shiftedCyclicChartEdgePath (0 : Fin 4)
+  let p1 := shiftedCyclicChartEdgePath (1 : Fin 4)
+  let p2 := shiftedCyclicChartEdgePath (2 : Fin 4)
+  let p3 := shiftedCyclicChartEdgePath (3 : Fin 4)
+  let h01 := shiftedCyclicChartRight_zero_eq_one_left
+  let h12 := shiftedCyclicChartRight_one_eq_two_left
+  let h23 := shiftedCyclicChartRight_two_eq_three_left
+  let h30 := shiftedCyclicChartRight_three_eq_zero_left
+  exact
+    (((p0.trans (p1.cast h01 rfl)).trans
+      (p2.cast h12 rfl)).trans
+      (p3.cast h23 rfl)).cast rfl h30.symm
+
+/-- The closed quotient chart path starts at the first finite left endpoint. -/
+theorem shiftedCyclicFourPath_source :
+    shiftedCyclicFourPath 0 = shiftedCyclicChartLeft (0 : Fin 4) :=
+  shiftedCyclicFourPath.source
+
+/-- The closed quotient chart path returns to the first finite left endpoint. -/
+theorem shiftedCyclicFourPath_target :
+    shiftedCyclicFourPath 1 = shiftedCyclicChartLeft (0 : Fin 4) :=
+  shiftedCyclicFourPath.target
+
+/--
+Evaluating a quotient edge path recovers the corresponding fixed-boundary
+finite level edge.
+
+This is the local comparison between quotient chart traversal and the
+semantic boundary observation.
+-/
+theorem shiftedSemanticCyclicChartEval_edgePath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
+    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartEdgePath i t) =
+      shiftedSemanticFinLevelEdge hcore z i t := by
+  rw [shiftedCyclicChartEdgePath_apply, shiftedCyclicChartMk_eq_mk,
+    shiftedSemanticCyclicChartEval_mk]
+  rfl
+
 /--
 The quotiented chart evaluation still lands on the original `q2` boundary.
 
@@ -1885,9 +1966,15 @@ chart wrapper. The representative map, finite chart evaluation, and descended
 quotient evaluation are continuous. The codomain of the descended evaluation
 is already the fixed `q2` boundary.
 
-[TODO: semantic-cf2d/shifted-cyclic-path]
-Package path traversal on `ShiftedCyclicChart` only after continuous quotient
-evaluation is stable.
+[IMPLEMENTED: semantic-cf2d/shifted-cyclic-path]
+The quotient chart edge path traverses one finite chart representative, and
+the first four quotient edge paths concatenate to a closed quotient path by
+using the quotient seam equalities. Evaluating one quotient edge recovers the
+corresponding fixed-`q2` finite level edge.
+
+[TODO: semantic-cf2d/shifted-cyclic-path-eval]
+Compare evaluation of the closed quotient path with the fixed-`q2` four-level
+path after path-trans cast normalization lemmas are available.
 
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index fa89d62b..4a34ae91 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -500,6 +500,14 @@ shiftedSemanticCyclicChartEval_left
 shiftedSemanticCyclicChartEval_right
 shiftedSemanticCyclicChartEval_right_eq_succ_left
 continuous_shiftedSemanticCyclicChartEval
+shiftedCyclicChartEdgePath
+shiftedCyclicChartEdgePath_apply
+shiftedCyclicChartEdgePath_source
+shiftedCyclicChartEdgePath_target
+shiftedCyclicFourPath
+shiftedCyclicFourPath_source
+shiftedCyclicFourPath_target
+shiftedSemanticCyclicChartEval_edgePath
 shiftedSemanticCyclicChartEval_q2
 ```
 
@@ -642,7 +650,25 @@ Boundary evaluation:
 Lean now proves continuity of `shiftedCyclicChartMk`, continuity of finite
 chart evaluation before quotienting, and continuity of the descended
 fixed-`q2` boundary evaluation. This is still not a Euclidean angle parameter.
-No quotient traversal path is selected yet.
+The quotient traversal path layer is now also available. For each finite
+index, `shiftedCyclicChartEdgePath i` traverses the representative charts
+`(i, t)` inside the quotient. The four finite quotient edges concatenate,
+using only the quotient seam equalities, into the closed path
+`shiftedCyclicFourPath`.
+
+The local evaluation comparison is proved:
+
+```text
+shiftedSemanticCyclicChartEval hcore z
+  (shiftedCyclicChartEdgePath i t)
+=
+shiftedSemanticFinLevelEdge hcore z i t
+```
+
+The full comparison between evaluation of `shiftedCyclicFourPath` and the
+existing fixed-`q2` four-level path is intentionally left as a TODO because it
+requires path-trans cast normalization lemmas. This is still not a Euclidean
+angle parameter.
 
 Candidate theorem directions:
 
@@ -736,9 +762,14 @@ depend on that reading.
 37. Implemented: connect Mathlib's quotient topology to `ShiftedCyclicChart`.
 38. Implemented: prove representative-level chart evaluation continuity.
 39. Implemented: prove descended quotient evaluation continuity.
-40. Later: package shifted cyclic path traversal only after the continuous
-    quotient evaluation API is stable.
-41. Later: add a Euclidean bridge that reads `1/8` full-cycle
+40. Implemented: package one quotient chart edge path.
+41. Implemented: concatenate the first four quotient edge paths into a closed
+    quotient path.
+42. Implemented: prove the local edge evaluation comparison against the
+    fixed-`q2` finite level edge.
+43. Later: compare the evaluated closed quotient path with the existing
+    fixed-`q2` four-level path after path-trans cast normalization lemmas.
+44. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -815,14 +846,20 @@ Connect Mathlib's quotient topology on `Quot` to `ShiftedCyclicChart`. The
 representative map, finite chart evaluation before quotienting, and descended
 fixed-`q2` quotient evaluation are continuous. This is a quotient-topology
 statement only; it does not select a quotient path structure.
+
+[IMPLEMENTED: semantic-cf2d/shifted-cyclic-path]
+Package one quotient chart edge path, concatenate the first four quotient edge
+paths into a closed quotient path by quotient seam equalities, expose source
+and target aliases, and prove the local edge evaluation comparison with the
+fixed-`q2` finite level edge.
 ```
 
 ## Remaining TODO Tags
 
 ```text
-[TODO: semantic-cf2d/shifted-cyclic-path]
-Package path traversal on `ShiftedCyclicChart` only after continuous quotient
-evaluation is stable.
+[TODO: semantic-cf2d/shifted-cyclic-path-eval]
+Compare evaluation of the closed quotient path with the fixed-`q2` four-level
+path after path-trans cast normalization lemmas are available.
 
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
````
`````
