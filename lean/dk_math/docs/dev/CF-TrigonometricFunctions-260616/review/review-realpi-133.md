# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 4ffc11fa15e785ef76a703f4ffdd1ed3a4bb2481

## Report

進めました。132 では、semantic evaluation の four-concat 全体まではまだ届かせず、まず edge-level mapping bridge を Lean で確立しました。

追加した主な Lean API:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge`
  - `shiftedSemanticCyclicChartEval_mappedEdge_apply`
  - `shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge`
  - `shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge`
  - `shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge`
  - `shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge`

意味としては、quotient edge path を descended semantic evaluation で map し、endpoint を finite API へ relabel すると、対応する observed semantic edge path と一致する、という theorem です。これで single-edge semantic mapping は解決済みです。

docs/report:

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) 更新
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) 更新
- [codex-report-132.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-132.md) 新規追加

実験結果として、four-edge map theorem はまだ seam proof alignment で止まります。次の実装推論は `shiftedFourPathConcatWithSeams_map_congr` のような generic/package theorem を作り、4 本の mapped-edge equality を `shiftedFourPathConcatWithSeams` へ持ち上げる方向です。

確認:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift` 成功
- `lake build DkMath.Analysis.DkReal` 成功
- `git diff --check` 成功
- 新規 report の末尾空白チェックも問題なし

## Review

## 採用判断

うむ、今回も **採用でよい**。
132 はかなり大きい。four-concat 全体はまだ閉じていないが、single-edge semantic mapping が完全に通った。つまり、quotient edge を semantic evaluation で `Path.map` し、endpoint を finite API に relabel すれば、対応する observed semantic edge path と一致する。これは残りの問題を「semantic の問題」から「four-path concatenator への持ち上げ問題」へ押し込めた、かなり良い checkpoint じゃ。

## 状況分析

今回追加された主な API はこれじゃ。

```text id="cng4up"
shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_apply
shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge
```

現在の構図はこう。

```text id="v8ivte"
single edge:
  quotient edge path
  mapped by semantic evaluation
  endpoint relabelled
  equals observed semantic edge path

four edges:
  still blocked by nested Path.trans / Path.cast
  and seam proof alignment
```

つまり、四本の部品はもう一致している。
残るのは、それを `shiftedFourPathConcatWithSeams` の中へ持ち上げることじゃ。

## レビュー

今回の止め方は正しい。

`shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge` が `Path.ext` と `rfl` で通っているのは、とても良い兆候じゃ。

```lean id="sz03j8"
theorem shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
```

これは、semantic evaluation の edge-level 挙動が定義通り綺麗にそろっていることを示している。

つまり、今の障害はもうここではない。

```text id="dcvztn"
semantic evaluation が edge を間違えている
```

ではなく、

```text id="tjfb3i"
edge equality を four-path concat の中へ運べていない
```

だけじゃ。

新規 report にも、direct four-edge theorem は unfolding / simplification だけでは閉じず、残る obstruction は四つの edge equality を nested `Path.trans` / `Path.cast` 構造へ運ぶ部分だと整理されている。これは非常に良い観測じゃ。

## 一歩先ゆく推論

次の breakthrough は、たぶん `semantic` 側の theorem ではなく、**path packaging theorem** じゃ。

今まではこう進んできた。

```text id="bgn7vm"
semantic edge theorem:
  solved

seam value alignment:
  solved

cast proof irrelevance:
  solved

map/trans/cast compatibility:
  solved

remaining:
  four-path concatenator lifting
```

したがって次の主役は、こういう theorem になる。

```lean id="f0m0vi"
shiftedFourPathConcatWithSeams_map_congr
```

ただし、いきなり完全汎用 theorem にすると dependent endpoint が重いかもしれぬ。
だから、賢狼の推論では **二段階化** が安全じゃ。

第一段階は、mapping 後の seam をそのまま使った canonical mapped four-path を作る。

```text id="e8wd4y"
mapped quotient via-edge four path:
  map each quotient edge
  glue by mapped quotient seam proofs
```

第二段階で、それを finite seam を使う observed via-edge path へ寄せる。

```text id="gj6hlf"
mapped seam proof
  と
finite seam proof
  は proof term が違うだけ

shiftedPath_cast_proof_irrel
  で吸収する
```

これが一番筋が良い。

## TODO の意味

いま残っている TODO は、次の形じゃ。

```text id="ajzt5m"
map shiftedCyclicFourPathViaEdges
  equals
shiftedSemanticObservedCyclicFourPathViaEdges
```

より具体的には、

```text id="tmn2ki"
Path.map が four concat を通過する

mapped edge が observed edge へ変換される

mapped seam proof が finite seam proof へ置き換わる
```

この三つを一度にやろうとすると Lean が詰まる。
だから分割する。

```text id="reiqul"
1:
  four concat map theorem

2:
  four concat congr theorem with proof-irrelevant casts

3:
  edge-level bridge theorem の適用
```

この順序がよい。

## 次の方針

次は、`shiftedFourPathConcatWithSeams_congr` の強化版を狙うのがよい。

既存の `shiftedFourPathConcatWithSeams_congr` は、同じ seam proof を使う場合に component path の equality から全体 equality を出すものじゃ。

しかし今ほしいのは、seam proof が違っても、endpoint value が同じなら path は同じ、という版じゃ。

候補はこう。

```lean id="cwijb8"
theorem shiftedFourPathConcatWithSeams_congr_cast_irrel
```

意味は、

```text id="f56dax"
p0 = q0
p1 = q1
p2 = q2
p3 = q3

seam proofs are possibly different

then:
  concat p0 p1 p2 p3 with seams h
  equals
  concat q0 q1 q2 q3 with seams k
```

これが通れば、mapped edge equality 四本を一気に持ち上げられる。

## おまけ実験

一歩先の実験として、`shiftedFourPathConcatWithSeams_map_congr` を完全汎用でなく、まず **same-shape specialized theorem** として書くのがよい。

狙いはこれ。

```text id="y9yqyn"
map of shiftedFourPathConcatWithSeams
  equals
shiftedFourPathConcatWithSeams of mapped paths
```

ただし seam proof は map 後のものを使う。

その後で、finite seam proof へ置き換える。

つまり、直接これを証明するのではなく、

```text id="kkz3a8"
map old quotient four concat
  equals mapped-seam four concat

mapped-seam four concat
  equals finite-seam observed four concat
```

に分ける。

これは Lean 的にも、数学的にもかなり自然じゃ。

## 結論

132 は採用でよい。

```text id="xbx0x3"
実装:
  良い。single-edge semantic mapping bridge が完全に通った。

数学:
  良い。semantic obstruction は消え、残るのは four-path packaging だけになった。

設計:
  良い。新規 report で次の obstruction が path-packaging theorem だと明記されている。

次:
  shiftedFourPathConcatWithSeams_map_congr または
  shiftedFourPathConcatWithSeams_congr_cast_irrel を作り、
  mapped-edge equality 四本を four-path equality へ持ち上げる。
```

ぬしよ、これは終盤戦じゃ。
四本の橋板はもう揃った。残っているのは、その四枚を一つの橋として固定する金具、つまり concatenator lifting theorem じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index c7d3e7c4..7e9f0b29 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -243,7 +243,10 @@ proof-irrelevance helper isolate the seam proof bookkeeping. The remaining
 bridge is to commute descended semantic evaluation with the nested
 `Path.trans` and `Path.cast` structure of the canonical four-path concatenator
 for this endpoint-cast observed path, including seam proof alignment after
-mapping.
+mapping. The edge-level mapping bridge is now proved: each quotient edge path
+mapped by descended semantic evaluation is the corresponding observed
+semantic edge path after endpoint relabelling. The next target is lifting
+these edge-level comparisons through the canonical four-edge concatenator.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 720ca2fa..51bdd199 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -2051,6 +2051,89 @@ theorem shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
   rw [shiftedSemanticObservedCyclicEdgePath_apply]
   rw [shiftedSemanticFinLevelPath_apply_eq_levelEdge]
 
+/--
+Mapping a quotient edge by descended semantic evaluation recovers the
+observed semantic edge after endpoint relabelling.
+
+This is the edge-level bridge from quotient traversal to fixed-boundary
+observation.
+-/
+theorem shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    ((shiftedCyclicChartEdgePath i).map
+      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+        (shiftedSemanticCyclicChartEval_left hcore z i).symm
+        (shiftedSemanticCyclicChartEval_right hcore z i).symm =
+      shiftedSemanticObservedCyclicEdgePath hcore z i := by
+  apply Path.ext
+  funext t
+  rfl
+
+/-- Pointwise form of the mapped quotient edge comparison. -/
+theorem shiftedSemanticCyclicChartEval_mappedEdge_apply
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
+    (((shiftedCyclicChartEdgePath i).map
+      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+        (shiftedSemanticCyclicChartEval_left hcore z i).symm
+        (shiftedSemanticCyclicChartEval_right hcore z i).symm) t =
+      shiftedSemanticObservedCyclicEdgePath hcore z i t :=
+  congrFun
+    (congrArg DFunLike.coe
+      (shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge hcore z i))
+    t
+
+/-- Edge `0` mapped by semantic evaluation is the observed edge `0`. -/
+theorem shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    ((shiftedCyclicChartEdgePath (0 : Fin 4)).map
+      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+        (shiftedSemanticCyclicChartEval_left hcore z (0 : Fin 4)).symm
+        (shiftedSemanticCyclicChartEval_right hcore z (0 : Fin 4)).symm =
+      shiftedSemanticObservedCyclicEdgePath hcore z (0 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge hcore z (0 : Fin 4)
+
+/-- Edge `1` mapped by semantic evaluation is the observed edge `1`. -/
+theorem shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    ((shiftedCyclicChartEdgePath (1 : Fin 4)).map
+      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+        (shiftedSemanticCyclicChartEval_left hcore z (1 : Fin 4)).symm
+        (shiftedSemanticCyclicChartEval_right hcore z (1 : Fin 4)).symm =
+      shiftedSemanticObservedCyclicEdgePath hcore z (1 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge hcore z (1 : Fin 4)
+
+/-- Edge `2` mapped by semantic evaluation is the observed edge `2`. -/
+theorem shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    ((shiftedCyclicChartEdgePath (2 : Fin 4)).map
+      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+        (shiftedSemanticCyclicChartEval_left hcore z (2 : Fin 4)).symm
+        (shiftedSemanticCyclicChartEval_right hcore z (2 : Fin 4)).symm =
+      shiftedSemanticObservedCyclicEdgePath hcore z (2 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge hcore z (2 : Fin 4)
+
+/-- Edge `3` mapped by semantic evaluation is the observed edge `3`. -/
+theorem shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    ((shiftedCyclicChartEdgePath (3 : Fin 4)).map
+      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
+        (shiftedSemanticCyclicChartEval_left hcore z (3 : Fin 4)).symm
+        (shiftedSemanticCyclicChartEval_right hcore z (3 : Fin 4)).symm =
+      shiftedSemanticObservedCyclicEdgePath hcore z (3 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge hcore z (3 : Fin 4)
+
 /--
 Canonical four-edge concatenation with explicit seam equalities.
 
@@ -2652,6 +2735,9 @@ Mathlib's `Path.map_trans` is exposed through a local wrapper, and a local
 packaging step. Quotient endpoint evaluation aliases, finite seam value
 alignment aliases, and a path-cast proof-irrelevance helper isolate the
 remaining seam proof alignment problem.
+Mapped quotient edge paths are now identified with their observed semantic
+edge paths after endpoint relabelling, uniformly over `Fin 4` and through
+four concrete edge aliases.
 
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
@@ -2666,7 +2752,8 @@ endpoint. The endpoint mismatch is solved; the remaining obstruction is the
 compatibility of descended semantic evaluation with the nested `Path.trans`
 and `Path.cast` structure of `shiftedFourPathConcatWithSeams`, including seam
 proof alignment after mapping. The current stable route prefers value-level
-seam alignment over direct equality of seam proof terms.
+seam alignment over direct equality of seam proof terms. The next expected
+normalization target is the mapped canonical quotient four-edge path.
 
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index da8bc4f2..dc636e67 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -510,6 +510,12 @@ shiftedCyclicFourPath_eq_viaEdges
 shiftedCyclicFourPath_source
 shiftedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_edgePath
+shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_apply
+shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge
 shiftedPath_cast_apply
 shiftedPath_cast_proof_irrel
 shiftedPath_map_cast
@@ -761,6 +767,24 @@ shiftedSemanticObservedCyclicEdgePath_apply
 shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
 ```
 
+The mapped quotient edge form is also connected to the observed semantic edge.
+After endpoint relabelling, mapping a quotient edge path by descended semantic
+evaluation gives the corresponding observed edge path:
+
+```text
+shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_apply
+shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge
+```
+
+This closes the edge-level mapping bridge. The remaining four-edge bridge is
+now a concatenator-lifting problem: transport these four mapped-edge
+comparisons through `shiftedFourPathConcatWithSeams` while aligning seam cast
+proofs.
+
 The four-edge packaging has also been standardized. The helper
 `shiftedFourPathConcatWithSeams` glues four paths by explicit endpoint seam
 equalities, exposes source and target aliases, and has a congruence theorem
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-132.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-132.md
new file mode 100644
index 00000000..ad498f14
--- /dev/null
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-132.md
@@ -0,0 +1,67 @@
+# Codex report 132: mapped edge bridge and next inference
+
+## Implemented result
+
+The edge-level mapping bridge is now formalized in
+`DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`.
+
+The main theorem is:
+
+```lean
+shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
+```
+
+It states that mapping a quotient chart edge path by the descended semantic
+evaluation, then relabelling endpoints to the finite fixed-boundary endpoint
+API, gives exactly the corresponding observed semantic edge path.
+
+Concrete aliases were also added for edges `0`, `1`, `2`, and `3`:
+
+```lean
+shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge
+shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge
+```
+
+## Experimental result
+
+A direct four-edge theorem was tested:
+
+```lean
+map shiftedCyclicFourPathViaEdges = shiftedSemanticObservedCyclicFourPathViaEdges
+```
+
+The proof did not close by unfolding and simplification. The remaining goal is
+not semantic: each mapped edge already agrees with the observed edge. The
+remaining obstruction is transporting those four edge equalities through the
+nested `Path.trans` and `Path.cast` structure of
+`shiftedFourPathConcatWithSeams`.
+
+## Inference for the next implementation
+
+The next useful theorem should not re-open the semantic definitions. It should
+be a path-packaging theorem:
+
+```lean
+shiftedFourPathConcatWithSeams_map_congr
+```
+
+Expected role:
+
+1. Map each of the four component paths.
+2. Rewrite mapped component paths using edge-level bridge theorems.
+3. Use `shiftedPath_cast_proof_irrel` to ignore differences between mapped
+   quotient seam proof terms and finite seam proof terms.
+
+This should turn the current problem from a semantic evaluation theorem into a
+generic four-path concatenator normalization theorem.
+
+## Current safe conclusion
+
+Endpoint mismatch is solved.
+
+Single-edge semantic mapping is solved.
+
+The remaining checkpoint is four-edge seam proof alignment under the common
+concatenator.
````
`````
