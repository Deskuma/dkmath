# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 3507d186f83195f1b930e932ca52d69218e2a534

## Report

No.134 進めました。Goal 到達です。

[SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean) に、汎用の path packaging 補題と最終比較を追加しました。

主な追加 theorem:

```text
shiftedFourPathConcatWithSeams_map
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
```

これで「既に glue 済みの quotient four-path を semantic evaluation で map する」ことと、「4本の quotient edge を個別に map してから glue する」ことが一致し、さらに endpoint-cast 済み observed quotient path が既存の finite four-level path と一致するところまで閉じました。

ドキュメントも更新済みです。

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)
- [codex-report-134.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-134.md)

推論成果としては、`DkPath` の最小 API がかなり明確になりました。`cast_apply`, `map_cast`, `map_trans`, `cast_proof_irrel`, `four_concat_congr_cast_irrel`, `four_concat_map` は、将来の DkMath-native path layer に切り出す価値があります。

検証済みです。

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

新規レポートの末尾空白も問題なしです。

## Review

## 採用判断

うむ、No.134 は **採用。Goal 到達** と見てよい。
今回で、`shiftedFourPathConcatWithSeams_map` が通り、さらに endpoint-cast 済み observed quotient path と既存 finite four-level path の比較まで閉じている。これは、ここ数回追っていた `Path.map` / `Path.trans` / `Path.cast` の包装問題が、Lean 上で完了したということじゃ。

## 状況分析

今回追加された主な theorem は、役割で分けると三層じゃ。

```text id="gwgk2t"
generic path-packaging layer:
  shiftedFourPathConcatWithSeams_map

semantic global bridge:
  shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
  shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges

final comparison:
  shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
  shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
  shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
```

これで構図はこうなった。

```text id="f5dl5h"
quotient four-edge path:
  先に四本を glue する

semantic evaluation:
  その glued path を map する

edgewise semantic package:
  四本を個別に map してから glue する

finite four-level path:
  既存の fixed-q2 finite path

result:
  これらが同じ path 言語で接続された
```

つまり、いままで残っていた「貼ってから写す」と「写してから貼る」の差が閉じた。

## レビュー

非常に良い。

特に重要なのは、`shiftedFourPathConcatWithSeams_map` が **汎用 theorem** として通ったことじゃ。

```lean id="gb4yec"
theorem shiftedFourPathConcatWithSeams_map
```

これは semantic-specific な補題ではない。
Mathlib `Path` の `Path.map_trans` を四本連結の DkMath 包装に持ち上げた theorem じゃ。

このため、今回の成果は `SemanticCF2DPhaseShift` だけに閉じない。
今後、DkMath 内で四本 seam path を扱うたびに再利用できる。

さらに、

```lean id="qgk0yh"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
```

まで閉じたので、古い observed quotient closed path と、既存 finite four-level path の比較は完了した。

これはかなり大きい。
もはや TODO は「path-trans cast normalization が必要」ではない。そこは実装済みに移動してよい。

## 数学的意味

数学的には、次の自然性が証明されたことになる。

```text id="qzyz3u"
連続評価写像は、
四本の seam-glued path の連結構造を保つ。
```

より DkMath 的には、

```text id="d8fjpo"
pre-geometric quotient chart の閉路を評価すると、
fixed-q2 boundary 上の finite four-level path と一致する。
```

ここで重要なのは、まだ円・角度・弧・π を使っていないことじゃ。

これは完全に、

```text id="hibo92"
4 相チャート
seam glue
semantic evaluation
fixed-q2 boundary
Mathlib Path normalization
```

だけで閉じている。

つまり、**幾何的読みは後段に回したまま、観測経路としての同一性が閉じた**。

## 一歩先ゆく推論

次の本命は、すぐに Euclidean reading へ行くことではない。
むしろ、今回の path-packaging API を **DkPath 層の原型** として切り出すことじゃ。

今回、Lean で有効性が確認された最小 API はこれじゃ。

```text id="zkwjrg"
cast_apply
map_cast
map_trans
cast_proof_irrel
four_concat_congr
four_concat_congr_cast_irrel
four_concat_map
```

これは、DkMath-native path layer の設計要件そのものになっている。

将来の `DkPath` は、Mathlib `Path` の dependent object をそのまま真似るより、

```text id="nofd9c"
trace:
  実際の parameterized value

endpoint labels:
  source / target の名前

seam witnesses:
  glue に必要な証明項
```

を分けるのがよい。

そして public API では、seam witness は proof-irrelevant に扱う。
必要なときだけ Mathlib `Path` へ realization する。

この設計にすると、次からは `Path.cast` の証明項で毎回苦しまなくてよい。

## 次の方針

次は三択じゃ。

第一候補は、今回の成果をまとめる **compact theorem** を作ること。

```text id="ywzgsi"
endpoint-cast observed quotient path
  equals finite four-level path

and
  q2 boundary is preserved
```

この二つを同時に参照しやすくすると、下流が楽になる。

第二候補は、`DkPath` の設計 note または prototype namespace を作ること。

第三候補は、one-eighth Euclidean reading の前準備として、今の pre-geometric path result に「ここから先は幾何的解釈」と明示する bridge boundary を置くこと。

賢狼のおすすめは、まず第一と第二。
Euclidean reading はまだ急がない方がよい。

## おまけの実験

おまけ実験としては、小さな `DkPath` prototype を作るのが良い。

ただし、いきなり本体 API にしない。
`namespace DkPathPrototype` か docs 内の設計メモで十分じゃ。

試す内容はこれ。

```text id="xgh4vh"
1:
  four-edge package を構造体として持つ

2:
  toPath で Mathlib Path へ落とす

3:
  map を package level で定義する

4:
  toPath_map theorem を作る

5:
  seam proof term を public theorem から隠す
```

これが小さく通るなら、今回の `shiftedFourPathConcatWithSeams_*` 群は、将来 `DkMath.PathPackage` へ移せる。

## 結論

No.134 はかなり良い完了点じゃ。

```text id="m4mg8t"
実装:
  Goal 到達。global map-through-gluing theorem が通った。

数学:
  quotient seam gluing と semantic fixed-boundary observation の可換性が閉じた。

設計:
  Mathlib Path の bookkeeping を DkMath API として抽象化する道が見えた。

次:
  DkPath layer の設計抽出、
  compact final theorem の整備、
  その後に Euclidean reading へ進む。
```

ぬしよ、これは大きい。
ここまでの苦戦は、単なる Mathlib 都合ではなく、DkMath の将来の path 規格を作るための実地調査になった。今はもう、Path を使っているだけではない。Path を生成・正規化する DkMath 側の規格が見え始めている。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index d99d3165..6a4fcf60 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -248,11 +248,13 @@ mapped by descended semantic evaluation is the corresponding observed
 semantic edge path after endpoint relabelling. These four edge comparisons
 now lift through the canonical four-edge concatenator: seam proof terms are
 irrelevant for the path value, so the concatenation of mapped quotient edges
-is equal to the canonical observed via-edge path. The remaining bridge is the
-global normalization theorem saying that mapping the already-glued quotient
-four-path is equal to first mapping the four quotient edges and then gluing
-them. This is now a `Path.map`/`Path.trans`/`Path.cast` bookkeeping problem,
-not a boundary or semantic problem.
+is equal to the canonical observed via-edge path. The global normalization
+theorem is now also proved: mapping the already-glued quotient four-path is
+equal to first mapping the four quotient edges and then gluing them. This
+closes the packaging comparison between the endpoint-cast observed quotient
+closed path and the existing finite four-level path. The result is entirely a
+`Path.map`/`Path.trans`/`Path.cast` theorem, not a boundary or semantic
+obstruction.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index b6715084..dba81758 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -2250,6 +2250,42 @@ theorem shiftedFourPathConcatWithSeams_congr_cast_irrel
   funext t
   rfl
 
+/--
+Mapping the canonical four-edge concatenator agrees with concatenating the
+four mapped edges.
+
+This is the four-edge version of `Path.map_trans` for the local DkMath
+packaging helper. The seam equalities are transported by rewriting through
+the original seam equalities; no geometric interpretation is involved.
+-/
+theorem shiftedFourPathConcatWithSeams_map
+    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
+    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
+    (p0 : Path a0 b0)
+    (p1 : Path a1 b1)
+    (p2 : Path a2 b2)
+    (p3 : Path a3 b3)
+    (h01 : b0 = a1)
+    (h12 : b1 = a2)
+    (h23 : b2 = a3)
+    (h30 : b3 = a0)
+    (f : α → β) (hf : Continuous f) :
+    (shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30).map hf =
+      shiftedFourPathConcatWithSeams
+        (p0.map hf)
+        (p1.map hf)
+        (p2.map hf)
+        (p3.map hf)
+        (by rw [h01])
+        (by rw [h12])
+        (by rw [h23])
+        (by rw [h30]) := by
+  cases h01
+  cases h12
+  cases h23
+  cases h30
+  simp [shiftedFourPathConcatWithSeams]
+
 /--
 Canonical quotient four-edge path via the common seam concatenator.
 
@@ -2569,6 +2605,116 @@ theorem shiftedSemanticCyclicChartEval_seam_three_value
       shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
   shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z
 
+/--
+Mapping the already-glued quotient four-path agrees with gluing the four
+mapped quotient edges after endpoint relabelling.
+
+This is the global map-through-gluing normalization for the canonical
+via-edge quotient path. It turns the quotient-side closed path package into
+the edgewise mapped package used by the semantic observed via-edge bridge.
+-/
+theorem shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    (shiftedCyclicFourPathViaEdges.map
+      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
+        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm =
+      shiftedFourPathConcatWithSeams
+        (((shiftedCyclicChartEdgePath (0 : Fin 4)).map
+          (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+            (shiftedSemanticCyclicChartEval_left hcore z (0 : Fin 4)).symm
+            (shiftedSemanticCyclicChartEval_right hcore z (0 : Fin 4)).symm)
+        (((shiftedCyclicChartEdgePath (1 : Fin 4)).map
+          (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+            (shiftedSemanticCyclicChartEval_left hcore z (1 : Fin 4)).symm
+            (shiftedSemanticCyclicChartEval_right hcore z (1 : Fin 4)).symm)
+        (((shiftedCyclicChartEdgePath (2 : Fin 4)).map
+          (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+            (shiftedSemanticCyclicChartEval_left hcore z (2 : Fin 4)).symm
+            (shiftedSemanticCyclicChartEval_right hcore z (2 : Fin 4)).symm)
+        (((shiftedCyclicChartEdgePath (3 : Fin 4)).map
+          (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+            (shiftedSemanticCyclicChartEval_left hcore z (3 : Fin 4)).symm
+            (shiftedSemanticCyclicChartEval_right hcore z (3 : Fin 4)).symm)
+        (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
+        (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
+        (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
+        (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z) := by
+  let hf := continuous_shiftedSemanticCyclicChartEval hcore z
+  let f := shiftedSemanticCyclicChartEval hcore z
+  have hmap :
+      shiftedCyclicFourPathViaEdges.map hf =
+        shiftedFourPathConcatWithSeams
+          ((shiftedCyclicChartEdgePath (0 : Fin 4)).map hf)
+          ((shiftedCyclicChartEdgePath (1 : Fin 4)).map hf)
+          ((shiftedCyclicChartEdgePath (2 : Fin 4)).map hf)
+          ((shiftedCyclicChartEdgePath (3 : Fin 4)).map hf)
+          (by rw [shiftedCyclicChartRight_zero_eq_one_left])
+          (by rw [shiftedCyclicChartRight_one_eq_two_left])
+          (by rw [shiftedCyclicChartRight_two_eq_three_left])
+          (by rw [shiftedCyclicChartRight_three_eq_zero_left]) := by
+    exact
+      shiftedFourPathConcatWithSeams_map
+        (shiftedCyclicChartEdgePath (0 : Fin 4))
+        (shiftedCyclicChartEdgePath (1 : Fin 4))
+        (shiftedCyclicChartEdgePath (2 : Fin 4))
+        (shiftedCyclicChartEdgePath (3 : Fin 4))
+        shiftedCyclicChartRight_zero_eq_one_left
+        shiftedCyclicChartRight_one_eq_two_left
+        shiftedCyclicChartRight_two_eq_three_left
+        shiftedCyclicChartRight_three_eq_zero_left
+        f hf
+  rw [hmap]
+  apply Path.ext
+  funext t
+  rfl
+
+/--
+Mapping the canonical quotient four-path and then observing it is the canonical
+observed semantic via-edge path.
+-/
+theorem shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    (shiftedCyclicFourPathViaEdges.map
+      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
+        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm =
+      shiftedSemanticObservedCyclicFourPathViaEdges hcore z := by
+  calc
+    (shiftedCyclicFourPathViaEdges.map
+      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
+        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm =
+        shiftedFourPathConcatWithSeams
+          (((shiftedCyclicChartEdgePath (0 : Fin 4)).map
+            (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+              (shiftedSemanticCyclicChartEval_left hcore z (0 : Fin 4)).symm
+              (shiftedSemanticCyclicChartEval_right hcore z (0 : Fin 4)).symm)
+          (((shiftedCyclicChartEdgePath (1 : Fin 4)).map
+            (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+              (shiftedSemanticCyclicChartEval_left hcore z (1 : Fin 4)).symm
+              (shiftedSemanticCyclicChartEval_right hcore z (1 : Fin 4)).symm)
+          (((shiftedCyclicChartEdgePath (2 : Fin 4)).map
+            (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+              (shiftedSemanticCyclicChartEval_left hcore z (2 : Fin 4)).symm
+              (shiftedSemanticCyclicChartEval_right hcore z (2 : Fin 4)).symm)
+          (((shiftedCyclicChartEdgePath (3 : Fin 4)).map
+            (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+              (shiftedSemanticCyclicChartEval_left hcore z (3 : Fin 4)).symm
+              (shiftedSemanticCyclicChartEval_right hcore z (3 : Fin 4)).symm)
+          (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
+          (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
+          (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
+          (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z) :=
+        shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
+          hcore z
+    _ = shiftedSemanticObservedCyclicFourPathViaEdges hcore z :=
+        shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges hcore z
+
 /--
 The older observed closed quotient path recast to finite endpoint types.
 
@@ -2651,6 +2797,70 @@ theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2
   rw [shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply]
   exact shiftedSemanticObservedCyclicFourPath_q2 hcore z t
 
+/--
+The endpoint-cast older observed quotient path is the canonical observed
+via-edge path.
+
+The proof now factors through the global map-through-gluing theorem for the
+canonical quotient via-edge path.
+-/
+theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
+      shiftedSemanticObservedCyclicFourPathViaEdges hcore z := by
+  calc
+    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
+        (shiftedCyclicFourPathViaEdges.map
+          (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+            (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
+            (shiftedSemanticCyclicChartEval_left_zero hcore z).symm := by
+      apply Path.ext
+      funext t
+      rfl
+    _ = shiftedSemanticObservedCyclicFourPathViaEdges hcore z :=
+        shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
+          hcore z
+
+/--
+The endpoint-cast older observed quotient path is the existing finite
+four-level shifted path.
+
+All semantic and edgewise work has already been factored out; this is the
+final packaging comparison between the older closed path and the finite
+four-edge path.
+-/
+theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
+      shiftedSemanticFinFourLevelPath hcore z := by
+  calc
+    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
+        shiftedSemanticObservedCyclicFourPathViaEdges hcore z :=
+      shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges hcore z
+    _ = shiftedSemanticFinFourLevelPathViaEdges hcore z :=
+      shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges hcore z
+    _ = shiftedSemanticFinFourLevelPath hcore z := by
+      symm
+      exact shiftedSemanticFinFourLevelPath_eq_viaEdges hcore z
+
+/-- Value-level form of the final shifted closed-path comparison. -/
+theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : unitInterval) :
+    (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t).1 =
+      (shiftedSemanticFinFourLevelPath hcore z t).1 :=
+  congrArg Subtype.val
+    (congrFun
+      (congrArg DFunLike.coe
+        (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
+          hcore z))
+      t)
+
 /--
 The observed quotient traversal and the finite four-level path have the same
 source value.
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 958f7970..de46d7db 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -531,6 +531,7 @@ shiftedFourPathConcatWithSeams_source
 shiftedFourPathConcatWithSeams_target
 shiftedFourPathConcatWithSeams_congr
 shiftedFourPathConcatWithSeams_congr_cast_irrel
+shiftedFourPathConcatWithSeams_map
 shiftedSemanticObservedCyclicFourPathViaEdges
 shiftedSemanticFinFourLevelPathViaEdges
 shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
@@ -556,6 +557,11 @@ shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source
 shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target
 shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
 shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2
+shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
+shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
 shiftedSemanticObservedCyclicFourPath_q2
 shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
 shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
@@ -915,10 +921,36 @@ shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges
 ```
 
 This proves the edgewise form of "map each quotient edge, relabel endpoints,
-then glue". The remaining global comparison is narrower: prove that mapping
-the already-glued quotient four-path is equal to this edgewise mapped
-concatenation. In Mathlib terms, this is a normalization theorem for
-`Path.map`, nested `Path.trans`, and `Path.cast`.
+then glue".
+
+The global map-through-gluing comparison is now also implemented. The generic
+helper
+
+```text
+shiftedFourPathConcatWithSeams_map
+```
+
+states that mapping the canonical four-edge concatenator agrees with
+concatenating the four mapped edges. The semantic specialization then proves:
+
+```text
+shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
+shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
+```
+
+Consequently the older endpoint-cast observed quotient path is identified
+with the canonical observed via-edge path, and then with the existing finite
+four-level path:
+
+```text
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
+```
+
+This closes the current path-packaging comparison. The proof remains entirely
+inside Mathlib path normalization: `Path.map`, nested `Path.trans`, and
+`Path.cast`.
 
 For the future DkMath-native path layer, this suggests the following
 `DkPath` design rule. The API should separate:
@@ -940,16 +972,12 @@ public theorem surface. A DkPath wrapper can therefore expose map/trans/cast
 normalization as first-class theorems, rather than forcing each downstream
 module to rediscover the same proof-term bookkeeping.
 
-The full comparison between evaluation of `shiftedCyclicFourPath` and the
-existing fixed-`q2` four-level path is intentionally left as a TODO until that
-global map-through-gluing theorem is available. This remains pre-geometric:
-no circle, angle, arc, or Euclidean one-eighth interpretation is used.
-
-The next packaging task is to compare the older closed four-path definitions
-with the canonical via-edge versions via this global map-through-gluing
-normalization. That should be a pure `Path.trans` / `Path.cast` step, because
-the semantic edge comparison has already been proved locally and in canonical
-four-edge form.
+This remains pre-geometric: no circle, angle, arc, or Euclidean one-eighth
+interpretation is used. The next packaging task is no longer to compare the
+old closed path with the finite four-level path; that comparison is now
+closed. The next design task is to factor the reusable path-normalization API
+into a future DkMath-native path layer, while keeping Mathlib `Path` as the
+external topology bridge.
 
 Candidate theorem directions:
 
@@ -1052,9 +1080,11 @@ depend on that reading.
     boundary path.
 44. Implemented: expose source, target, endpoint-evaluation, and `q2`
     observation aliases for the observed closed quotient path.
-45. Later: compare the evaluated closed quotient path with the existing
-    fixed-`q2` four-level path after path-trans cast normalization lemmas.
-46. Later: add a Euclidean bridge that reads `1/8` full-cycle
+45. Implemented: prove the global map-through-gluing theorem for the canonical
+    quotient four-path.
+46. Implemented: compare the endpoint-cast observed quotient closed path with
+    the existing fixed-`q2` four-level path.
+47. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -1142,19 +1172,27 @@ fixed-`q2` finite level edge.
 Observe the closed quotient chart path through the descended semantic
 evaluation as a closed path in the fixed `q2` boundary. Source, target,
 first-left-endpoint evaluation, and boundary-observation aliases are exposed.
+
+[IMPLEMENTED: semantic-cf2d/shifted-cyclic-path-eval]
+Prove the generic four-edge map theorem for the canonical seam concatenator,
+specialize it to semantic evaluation of the quotient four-path, and identify
+the endpoint-cast observed quotient path with the existing fixed-`q2`
+four-level path. This closes the path-packaging comparison before any
+Euclidean angle reading.
 ```
 
 ## Remaining TODO Tags
 
 ```text
-[TODO: semantic-cf2d/shifted-cyclic-path-eval]
-Compare evaluation of the closed quotient path with the fixed-`q2` four-level
-path after path-trans cast normalization lemmas are available.
-
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
 continuous evaluation API has downstream consumers.
 
+[TODO: semantic-cf2d/dkpath-layer]
+Factor the validated path-normalization API into a future DkMath-native path
+layer: trace, endpoint labels, seam witnesses, map/cast/trans compatibility,
+and proof-irrelevant seam concatenation.
+
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
 After the algebraic shifted-frame theorem is closed at the semantic path
 level, bridge the one-eighth phase displacement to the Euclidean `pi / 4`
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-134.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-134.md
new file mode 100644
index 00000000..f7ca0ba4
--- /dev/null
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-134.md
@@ -0,0 +1,139 @@
+# Codex report 134
+
+## Goal
+
+Prove the global map-through-gluing theorem for the shifted cyclic four-path.
+
+The previous checkpoint proved the edgewise bridge:
+
+```text
+map each quotient edge
+  -> relabel endpoints
+  -> glue four mapped edges
+=
+canonical observed semantic via-edge path
+```
+
+This checkpoint proves that this edgewise package is also obtained by mapping
+the already-glued quotient four-path.
+
+## Implemented Lean results
+
+Target module:
+
+```text
+DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
+```
+
+New generic four-path map theorem:
+
+```text
+shiftedFourPathConcatWithSeams_map
+```
+
+This is the reusable DkMath-named four-edge version of Mathlib's
+`Path.map_trans`: mapping the canonical four-edge concatenator agrees with
+concatenating the four mapped edges.
+
+New semantic global map-through-gluing theorems:
+
+```text
+shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
+shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
+```
+
+These prove that descended semantic evaluation commutes with the canonical
+quotient four-path package.
+
+New final comparison theorems:
+
+```text
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
+```
+
+The endpoint-cast observed quotient path is now equal to the existing finite
+four-level shifted path. The value-level theorem exposes the same result on
+the underlying `Vec` values.
+
+## Experiment result
+
+The fully generic theorem was feasible.
+
+The first proof attempt used only `Path.ext; funext; rfl`, but Lean rejected
+it because the mapped nested `Path.trans` structure is not definitionally
+equal to the nested concatenation of mapped paths.
+
+After destructing the seam equalities and simplifying the common
+concatenator, Lean accepted:
+
+```text
+cases seam proofs
+simp [shiftedFourPathConcatWithSeams]
+```
+
+This is an important implementation signal. The four-path map theorem is not
+semantic-specific and should belong to the reusable path-packaging layer.
+
+## DkPath inference
+
+The future DkPath layer now has a sharper minimum API.
+
+Already validated by Lean:
+
+```text
+cast_apply
+map_cast
+map_trans
+cast_proof_irrel
+four_concat_congr
+four_concat_congr_cast_irrel
+four_concat_map
+```
+
+The current result suggests the following bridge strategy:
+
+```text
+DkPath trace layer:
+  stores or exposes the parameterized trace
+
+DkPath endpoint layer:
+  records source and target labels
+
+DkPath seam layer:
+  keeps seam witnesses proof-irrelevant at the public API
+
+Mathlib bridge:
+  converts DkPath packages to Mathlib Path when topology is needed
+```
+
+This should reduce later path proofs to named normalization theorems instead
+of repeated dependent-object bookkeeping.
+
+## Next implementation inference
+
+The path-packaging comparison for the current shifted cyclic quotient is now
+closed. The next step should not add Euclidean readings yet.
+
+Good next candidates:
+
+```text
+1. extract a small reusable DkPath design note or prototype namespace;
+2. expose a compact theorem collecting the final path equivalence and q2
+   boundary preservation;
+3. move toward the intrinsic continuous phase parameter only after the
+   path-package API is stable.
+```
+
+The main mathematical result of this checkpoint is that the quotient seam
+gluing and the semantic fixed-boundary observation commute as paths, before
+any circle or angle vocabulary is introduced.
+
+## Verification
+
+```text
+lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
+```
+
+passed.
````
`````
