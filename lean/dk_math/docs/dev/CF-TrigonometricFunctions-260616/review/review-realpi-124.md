# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: f71bdaaadc46855e37464e401727d692d7c7cd39

## Report

実装完了です。closed quotient chart path を semantic boundary observation に接続しました。

追加した主なもの:

- `shiftedSemanticObservedCyclicFourPath`
- `shiftedSemanticObservedCyclicFourPath_source`
- `shiftedSemanticObservedCyclicFourPath_target`
- `shiftedSemanticCyclicChartEval_left_zero`
- `shiftedSemanticObservedCyclicFourPath_q2`

これで `shiftedCyclicFourPath` を `shiftedSemanticCyclicChartEval` で観測したものが、固定 `q2` 境界内の閉 path として明示的に使えるようになりました。source/target と `q2` observation も theorem として出しています。

full comparison:

```lean
shiftedSemanticObservedCyclicFourPath hcore z =
  shiftedSemanticFinFourLevelPath hcore z
```

これは予定通り `Path.trans` / `Path.cast` の正規化補題が必要なので、TODO のまま維持しました。

確認済み:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功しています。

## Review

うむ、今回も **採用でよい**。
これは「quotient chart 側の closed path」と「semantic boundary observation 側」を、ついに明示的につないだ差分じゃ。`shiftedSemanticObservedCyclicFourPath` によって、`shiftedCyclicFourPath` を `shiftedSemanticCyclicChartEval` で観測したものが、固定 `q2` 境界内の closed path として使えるようになった。source / target / endpoint evaluation / `q2` observation も theorem 化されており、今の checkpoint としては十分に良い。

## 1. 状況分析

今回追加された主なものはこれじゃ。

```text id="p3mvoa"
shiftedSemanticObservedCyclicFourPath
shiftedSemanticObservedCyclicFourPath_source
shiftedSemanticObservedCyclicFourPath_target
shiftedSemanticCyclicChartEval_left_zero
shiftedSemanticObservedCyclicFourPath_q2
```

構造としては、こうなった。

```text id="g62ilb"
quotient chart closed path:
  shiftedCyclicFourPath

descended semantic evaluation:
  shiftedSemanticCyclicChartEval

observed closed boundary path:
  shiftedSemanticObservedCyclicFourPath
```

つまり、quotient chart の中を歩いた結果を、固定 `q2` 境界側へ観測する path ができた。

これは良い。
以前は「局所 edge を評価すると fixed-`q2` finite level edge に戻る」だった。今回は閉じた quotient path 全体を観測 path として包装している。

## 2. レビュー

今回の実装判断は正しい。

`shiftedSemanticObservedCyclicFourPath` の定義は自然じゃ。

```lean id="d7wj65"
toFun t := shiftedSemanticCyclicChartEval hcore z (shiftedCyclicFourPath t)
```

そして連続性は、すでに得ている quotient evaluation の連続性と `shiftedCyclicFourPath` の連続性の合成で出している。

```text id="x33uex"
quotient path:
  continuous

quotient evaluation:
  continuous

observed path:
  continuous by composition
```

これは理想的な流れじゃ。

また、`shiftedSemanticObservedCyclicFourPath_q2` があるので、この observed path が固定 `q2` 境界上にいることも外部 API から直接使える。

$$
\mathrm{q2}(\mathrm{observedPath}(t))=\mathrm{q2}(z)
$$

これは DkMath の保存核境界観測として非常に読みやすい。

## 3. TODO の内容を少し詳しく

残っている TODO はこれじゃ。

```text id="pspib2"
[TODO: semantic-cf2d/shifted-cyclic-path-eval]
Compare evaluation of the closed quotient path with the fixed-q2 four-level
path after path-trans cast normalization lemmas are available.
```

これは要するに、次の二つの path が同じかどうかを示したい、ということじゃ。

```lean id="ewly4d"
shiftedSemanticObservedCyclicFourPath hcore z
```

```lean id="ypq3n6"
shiftedSemanticFinFourLevelPath hcore z
```

意味はこうじゃ。

```text id="d2t8kq"
observed quotient path:
  quotient chart の閉路を semantic evaluation で観測した path

finite four-level path:
  fixed-q2 level-set 側で直接四本を連結した path
```

直感的には、同じものを二つの経路で作っている。

```text id="gqwkje"
route A:
  quotient chart を作る
  その中を歩く
  semantic evaluation で fixed-q2 境界へ写す

route B:
  fixed-q2 境界側の四本の finite level edge を直接つなぐ
```

だから、期待される最終形はこうじゃ。

```lean id="qcrz82"
theorem shiftedSemanticObservedCyclicFourPath_eq_finFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPath hcore z =
      shiftedSemanticFinFourLevelPath hcore z
```

ただし、これは見た目より重い。

## 4. なぜ TODO が残るのか

理由は `Path.trans` と `Path.cast` じゃ。

四本の path を連結すると、Lean 内部では単純に

```text id="n2xtzi"
edge 0
edge 1
edge 2
edge 3
```

が横に並ぶだけではない。

`Path.trans` は unitInterval の parameter を分割して、前半は前の path、後半は後の path を読むような構造を作る。四本を連結すると、この分割が入れ子になる。

さらに endpoint の型を合わせるために `Path.cast` が入る。
この `cast` は数学的には何も変えていないが、Lean の式としては邪魔になる。

つまり、比較には次の正規化が必要になる。

```text id="rx6g57"
Path.cast:
  cast しても各 t の値は同じ、という補題

Path.trans:
  trans の左側区間での値
  trans の右側区間での値

nested Path.trans:
  四本連結でどの t がどの edge に対応するか
```

これらがないと、full equality は証明がかなり汚くなる。

## 5. 今すぐできていること

ただし、全体比較は未完でも、局所比較はもう通っている。

```lean id="gcmt8b"
shiftedSemanticCyclicChartEval_edgePath
```

これは非常に重要じゃ。

意味は、

```text id="tltc4s"
one quotient edge path を評価する
  equals
対応する finite level edge
```

じゃ。

つまり、四本の各部品はすでに一致している。
残っているのは、四本を `Path.trans` で連結したときの正規化だけじゃ。

これは数学的 obstruction ではない。
Lean の path packaging の正規化課題じゃ。

## 6. 次の方針

次は full equality をいきなり狙うより、まず `Path.cast` と `Path.trans` の小補題を作るのがよい。

第一候補はこれじゃ。

```lean id="drqiln"
theorem path_cast_apply
    {α : Type _} [TopologicalSpace α]
    {a b c d : α}
    (p : Path a b) (hac : a = c) (hbd : b = d)
    (t : unitInterval) :
    (p.cast hac hbd) t = p t
```

もし Mathlib に既存の simp theorem があるなら、それを使うだけでよい。
なければ、この補題をローカルに足す価値がある。

次に、`Path.trans` の source / target や、特定点での値だけを見る。

まず全 \(t\) の比較ではなく、観測点を狙うのが安全じゃ。

```text id="axp93g"
source comparison:
  observed source equals finite source

target comparison:
  observed target equals finite target

edge boundary comparison:
  first seam
  second seam
  third seam
  closing seam
```

この順で行くのがよい。

## 7. 次の勝利条件

次の checkpoint の勝利条件はこれでよい。

```text id="pm95ao"
1:
  observed path の source / target を finite four-level path 側の source / target に変換する

2:
  Path.cast apply 補題を追加する、または既存補題を確認する

3:
  できれば first edge segment の比較を theorem 化する

4:
  full path equality は無理なら TODO のまま維持する
```

特に first edge segment comparison は試す価値がある。

ただし、unitInterval の区間分割が絡むなら重くなるので、無理しなくてよい。

## 8. 結論

今回の差分は採用でよい。

```text id="fvaubc"
実装:
  良い。closed quotient path を fixed-q2 boundary observation path として包装した。

数学:
  良い。quotient traversal と semantic observation が closed path レベルで接続された。

設計:
  良い。full four-path equality は Path.trans/cast 正規化待ちとして残した。

次:
  Path.cast / Path.trans の正規化補題を整え、observed path と finite four-level path の比較へ進む。
```

ぬしよ、これはかなりの到達点じゃ。
今はもう「貼り合わせた chart を歩く」と「保存核境界で観測する」が connected している。残りは、その観測 path と既存 finite four-level path が同じ歩みであることを、Lean の path 正規化で押さえる段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index e4e07a5a..ca06207f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -219,6 +219,9 @@ the representative map, finite chart evaluation, and descended fixed-boundary
 quotient evaluation are continuous. The quotient edge path and closed
 four-edge quotient path are packaged in the glued chart space, and evaluating
 one quotient edge recovers the corresponding fixed-`q2` finite level edge.
+Observing the closed quotient path through the descended evaluation now gives
+a closed fixed-boundary path with source, target, endpoint, and `q2`
+observation aliases.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index cb7f672e..e9e3dcc5 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1895,6 +1895,74 @@ theorem shiftedSemanticCyclicChartEval_edgePath
     shiftedSemanticCyclicChartEval_mk]
   rfl
 
+/--
+The closed quotient chart path observed inside the fixed square-mass boundary.
+
+This composes the closed quotient traversal with the descended semantic
+evaluation. The codomain is already `LevelSet ℝ (Vec.q2 z)`, so fixed-boundary
+membership is carried by the type.
+-/
+def shiftedSemanticObservedCyclicFourPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path
+      (shiftedSemanticCyclicChartEval hcore z
+        (shiftedCyclicChartLeft (0 : Fin 4)))
+      (shiftedSemanticCyclicChartEval hcore z
+        (shiftedCyclicChartLeft (0 : Fin 4))) where
+  toFun t := shiftedSemanticCyclicChartEval hcore z (shiftedCyclicFourPath t)
+  continuous_toFun :=
+    (continuous_shiftedSemanticCyclicChartEval hcore z).comp
+      shiftedCyclicFourPath.continuous_toFun
+  source' := by
+    rw [shiftedCyclicFourPath_source]
+  target' := by
+    rw [shiftedCyclicFourPath_target]
+
+/-- The observed closed quotient path starts at the observed first left endpoint. -/
+theorem shiftedSemanticObservedCyclicFourPath_source
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticObservedCyclicFourPath hcore z 0 =
+      shiftedSemanticCyclicChartEval hcore z
+        (shiftedCyclicChartLeft (0 : Fin 4)) :=
+  (shiftedSemanticObservedCyclicFourPath hcore z).source
+
+/-- The observed closed quotient path returns to the observed first left endpoint. -/
+theorem shiftedSemanticObservedCyclicFourPath_target
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticObservedCyclicFourPath hcore z 1 =
+      shiftedSemanticCyclicChartEval hcore z
+        (shiftedCyclicChartLeft (0 : Fin 4)) :=
+  (shiftedSemanticObservedCyclicFourPath hcore z).target
+
+/-- Evaluation of the first quotient left endpoint agrees with the finite API. -/
+theorem shiftedSemanticCyclicChartEval_left_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticCyclicChartEval hcore z
+      (shiftedCyclicChartLeft (0 : Fin 4)) =
+        shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_left hcore z (0 : Fin 4)
+
+/--
+The observed closed quotient path remains on the original `q2` boundary.
+
+This is a projection of the subtype proof carried by the path codomain.
+-/
+theorem shiftedSemanticObservedCyclicFourPath_q2
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : unitInterval) :
+    Vec.q2 ((shiftedSemanticObservedCyclicFourPath hcore z t).1) =
+      Vec.q2 z :=
+  (shiftedSemanticObservedCyclicFourPath hcore z t).2
+
 /--
 The quotiented chart evaluation still lands on the original `q2` boundary.
 
@@ -1972,6 +2040,11 @@ the first four quotient edge paths concatenate to a closed quotient path by
 using the quotient seam equalities. Evaluating one quotient edge recovers the
 corresponding fixed-`q2` finite level edge.
 
+[IMPLEMENTED: semantic-cf2d/shifted-cyclic-observation]
+The closed quotient path is observed through the descended semantic
+evaluation as a fixed-`q2` path. Source, target, endpoint-evaluation, and
+boundary-observation aliases are exposed.
+
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
 path after path-trans cast normalization lemmas are available.
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 4a34ae91..d562f3c3 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -508,6 +508,11 @@ shiftedCyclicFourPath
 shiftedCyclicFourPath_source
 shiftedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_edgePath
+shiftedSemanticObservedCyclicFourPath
+shiftedSemanticObservedCyclicFourPath_source
+shiftedSemanticObservedCyclicFourPath_target
+shiftedSemanticCyclicChartEval_left_zero
+shiftedSemanticObservedCyclicFourPath_q2
 shiftedSemanticCyclicChartEval_q2
 ```
 
@@ -665,6 +670,19 @@ shiftedSemanticCyclicChartEval hcore z
 shiftedSemanticFinLevelEdge hcore z i t
 ```
 
+The closed quotient path can now be observed through the descended semantic
+evaluation:
+
+```text
+shiftedSemanticObservedCyclicFourPath hcore z
+```
+
+This is a closed `Path` in the fixed `q2 z` level set. Source, target,
+first-left-endpoint evaluation, and boundary-observation aliases are exposed.
+Thus the quotient traversal is already connected to a fixed-boundary
+observation path, even before comparing the whole concatenated path with the
+existing finite four-level path.
+
 The full comparison between evaluation of `shiftedCyclicFourPath` and the
 existing fixed-`q2` four-level path is intentionally left as a TODO because it
 requires path-trans cast normalization lemmas. This is still not a Euclidean
@@ -767,9 +785,13 @@ depend on that reading.
     quotient path.
 42. Implemented: prove the local edge evaluation comparison against the
     fixed-`q2` finite level edge.
-43. Later: compare the evaluated closed quotient path with the existing
+43. Implemented: observe the closed quotient path as a closed fixed-`q2`
+    boundary path.
+44. Implemented: expose source, target, endpoint-evaluation, and `q2`
+    observation aliases for the observed closed quotient path.
+45. Later: compare the evaluated closed quotient path with the existing
     fixed-`q2` four-level path after path-trans cast normalization lemmas.
-44. Later: add a Euclidean bridge that reads `1/8` full-cycle
+46. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -852,6 +874,11 @@ Package one quotient chart edge path, concatenate the first four quotient edge
 paths into a closed quotient path by quotient seam equalities, expose source
 and target aliases, and prove the local edge evaluation comparison with the
 fixed-`q2` finite level edge.
+
+[IMPLEMENTED: semantic-cf2d/shifted-cyclic-observation]
+Observe the closed quotient chart path through the descended semantic
+evaluation as a closed path in the fixed `q2` boundary. Source, target,
+first-left-endpoint evaluation, and boundary-observation aliases are exposed.
 ```
 
 ## Remaining TODO Tags
````
`````
