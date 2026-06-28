# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 23192d258d5c0fc3073f663c9c97cfb4d5b7176d

## Report

進めました。128 では、旧 observed closed path の endpoint 型ズレを分離しました。

追加した主な Lean API:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint`
  - `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source`
  - `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target`
  - `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply`

これで、旧 observed path は finite left endpoint 型へ cast 済みの path として扱えます。`apply` theorem により、cast は点wise value を変えないことも明示しました。

今回の到達点:

- endpoint mismatch は解消済み
- 残る問題は、descended semantic evaluation が `shiftedFourPathConcatWithSeams` と可換であること
- つまり「評価してから concat」と「concat してから評価」の bridge lemma が次の焦点です

Docs も同期済み:

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)

確認:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift` 成功
- `lake build DkMath.Analysis.DkReal` 成功
- `git diff --check` 成功

## Review

## 採用判断

うむ、今回も **採用でよい**。
128 はかなり良い切り分けじゃ。旧 observed closed path の endpoint 型ズレを `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint` として分離し、source / target / apply theorem まで出している。これで「endpoint 型が違うから比較できない」という問題は片付いた。

## 状況分析

今回追加された主な API はこれじゃ。

```text id="frydcw"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
```

これにより、旧 observed path は次の形で扱えるようになった。

```text id="mxglkd"
before:
  endpoint is observed quotient-left endpoint

after:
  endpoint is finite left endpoint

pointwise value:
  unchanged
```

つまり、旧 observed path と canonical via-edge path は、同じ endpoint 型の path として比較できる段階に入った。

## レビュー

実装判断は良い。

特に良いのは、`Path.cast` を使って endpoint label の問題だけを切り出したことじゃ。

```lean id="kyqzcd"
def shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
```

この定義により、旧 observed path の実際の値は変えず、型だけを finite endpoint に寄せている。

そして、

```lean id="zy4b5e"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
```

によって、点ごとの値が変わらないことも明示された。

これはかなり大事じゃ。
今後の比較で「cast が値を変えたのでは？」という疑いを消せる。

## TODO の意味

残る TODO は、もう endpoint mismatch ではない。

残るのはこれじゃ。

```text id="noryjp"
concat してから evaluation する

evaluation してから concat する
```

この二つが同じであることを示す必要がある。

旧 observed path は、

```text id="j4fhvz"
shiftedCyclicFourPath
  を作る
shiftedSemanticCyclicChartEval
  で観測する
```

という形。

canonical observed via-edge path は、

```text id="hdzsdl"
各 edge を観測する
観測済み edge path を four-path concat する
```

という形。

つまり次の橋が本丸じゃ。

```text id="xojz7o"
semantic evaluation commutes with shiftedFourPathConcatWithSeams
```

これは数学的には自然。
Lean 的には、`Path.trans` と `Path.cast` の定義に沿って、連続写像の path map が concat と commute することを示す必要がある。

## 次の方針

次は、いきなり四本全部の theorem に行くより、まず **二本 concat での map 互換** を試すのがよい。

汎用化しすぎると dependent endpoint が重くなる。
だから、最初はプロジェクト専用の補題としてよい。

狙いはこう。

```text id="t7mxie"
Path.map or composed path
  preserves Path.cast

Path.map or composed path
  preserves Path.trans

therefore:
  evaluation preserves four-path concatenator
```

もし Mathlib に `Path.map` があるなら、それを使うとよい。
なければ、今まで通り `toFun` と `continuous_toFun` を直接書いてよい。

## 一歩先ゆくおまけ実験

一歩先の実験としては、完全汎用の map-concat lemma ではなく、まず今回の endpoint-casted observed path 専用の theorem を狙うのがよい。

候補はこれじゃ。

```lean id="w8goux"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
```

これが通れば、最終 theorem はほぼ一本道になる。

```text id="gdvjt9"
casted old observed path
  equals
canonical observed via-edge path

canonical observed via-edge path
  equals
canonical finite via-edge path

canonical finite via-edge path
  equals
old finite path
```

ここまで繋がれば、実質的に checkpoint 104 の cyclic path comparison は閉じる。

## 結論

今回の差分は採用でよい。

```text id="b5fcml"
実装:
  良い。旧 observed path の endpoint mismatch が分離された。

数学:
  良い。残る問題が evaluation と concat の可換性へ絞られた。

設計:
  良い。cast は点wise value を変えないと theorem 化されている。

次:
  semantic evaluation が canonical four-path concatenator と可換であることを試す。
```

ぬしよ、これはかなり詰まってきた。
残っているのは、ほぼ「貼ってから写す」と「写してから貼る」の交換法則じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 507db4d0..e82b267d 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -233,8 +233,11 @@ seams now packages canonical via-edge observed and direct finite closed
 paths, and those two canonical paths are equal by the four single-edge
 equalities. The older quotient closed path and the older finite four-level
 path are definitionally equal to their canonical via-edge versions. The
-remaining bridge is to commute descended semantic evaluation with the
-canonical four-path concatenator for the older observed path.
+older observed closed path is also endpoint-cast to the finite left endpoint,
+with source, target, and apply aliases proving that only endpoint labels
+changed. The remaining bridge is to commute descended semantic evaluation
+with the canonical four-path concatenator for this endpoint-cast observed
+path.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 7c316e21..15b6d0d0 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -2245,6 +2245,60 @@ theorem shiftedSemanticCyclicChartEval_left_zero
         shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
   shiftedSemanticCyclicChartEval_left hcore z (0 : Fin 4)
 
+/--
+The older observed closed quotient path recast to finite endpoint types.
+
+The path values are unchanged; only the source and target expressions are
+relabelled from the observed quotient left endpoint to the finite left
+endpoint.
+-/
+def shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path
+      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4))
+      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)) :=
+  (shiftedSemanticObservedCyclicFourPath hcore z).cast
+    (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
+    (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
+
+/-- The recast observed closed path starts at the finite left endpoint. -/
+theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z 0 =
+      shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
+  (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z).source
+
+/-- The recast observed closed path returns to the finite left endpoint. -/
+theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z 1 =
+      shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
+  (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z).target
+
+/--
+Endpoint casting the older observed path does not change its pointwise values.
+
+This is the local bridge that separates endpoint-type bookkeeping from the
+later evaluation-concatenation compatibility problem.
+-/
+theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : unitInterval) :
+    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t =
+      shiftedSemanticObservedCyclicFourPath hcore z t :=
+  shiftedPath_cast_apply
+    (shiftedSemanticObservedCyclicFourPath hcore z)
+    (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
+    (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
+    t
+
 /--
 The observed closed quotient path remains on the original `q2` boundary.
 
@@ -2413,6 +2467,9 @@ closed paths are equal by the four single-edge equalities.
 The older quotient closed path is definitionally equal to its canonical
 via-edge form, and the older finite fixed-boundary four-level path is
 definitionally equal to the canonical direct finite via-edge form.
+The older observed closed path can now be endpoint-cast to the same finite
+endpoint type, with source, target, and pointwise apply aliases showing that
+only endpoint labels changed.
 
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
@@ -2421,7 +2478,9 @@ path after path-trans cast normalization lemmas are available.
 [TODO: semantic-cf2d/shifted-cyclic-via-edge-compare]
 The quotient-side closed path and finite closed path match their canonical
 via-edge versions. The observed quotient path still needs a lemma commuting
-descended semantic evaluation with the canonical four-path concatenator.
+descended semantic evaluation with the canonical four-path concatenator, after
+endpoint casting from the observed quotient-left endpoint to the finite left
+endpoint.
 
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index d1d32024..32e77e2b 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -529,6 +529,10 @@ shiftedSemanticObservedCyclicFourPath
 shiftedSemanticObservedCyclicFourPath_source
 shiftedSemanticObservedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_left_zero
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
 shiftedSemanticObservedCyclicFourPath_q2
 shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
 shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
@@ -775,6 +779,22 @@ observed via-edge path is typed at the finite left endpoint. Even pointwise,
 the remaining theorem must commute descended semantic evaluation with the
 canonical four-path concatenator.
 
+The endpoint mismatch has been isolated by an endpoint-casted older observed
+path:
+
+```text
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
+```
+
+This casted path has the same finite endpoint type as the canonical via-edge
+paths, and its apply theorem states that endpoint casting does not change the
+pointwise observed value. Thus the remaining bridge is no longer endpoint
+typing; it is the compatibility of descended semantic evaluation with the
+canonical four-path concatenator.
+
 Value-level source and target comparisons are also available for the closed
 four-edge paths:
 
@@ -792,7 +812,8 @@ or Euclidean one-eighth reading.
 More precisely, the quotient-side closed path and finite closed path now match
 their canonical via-edge versions. The observed quotient path still needs a
 lemma commuting descended semantic evaluation with the canonical four-path
-concatenator.
+concatenator after endpoint casting from the observed quotient-left endpoint
+to the finite left endpoint.
 
 The full comparison between evaluation of `shiftedCyclicFourPath` and the
 existing fixed-`q2` four-level path is intentionally left as a TODO because it
````
`````
