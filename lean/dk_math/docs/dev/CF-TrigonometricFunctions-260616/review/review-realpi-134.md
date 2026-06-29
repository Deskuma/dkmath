# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 1b266a5dbe4cd85a7e269ef5943015d11fe347c9

## Report

進めました。今回の No.133 は Goal 到達です。

実装では [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean) に以下を追加しました。

- `shiftedFourPathConcatWithSeams_congr_cast_irrel`
- `shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges`

これで「4本の quotient edge を semantic evaluation で map して endpoint relabel し、それを glue したもの」が、canonical observed via-edge path と一致するところまで Lean が認めました。障害は意味論ではなく、Mathlib `Path` の `map/trans/cast` と seam proof term の bookkeeping だけ、という観測もかなり明確になりました。

文書側も更新済みです。

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)
- [codex-report-133.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-133.md)

次の推論として、`DkPath` は Mathlib `Path` の dependent object をそのまま真似るより、`trace / endpoint labels / seam witnesses` を分けて、`map_cast`, `map_trans`, `cast_proof_irrel`, `four_concat_congr_cast_irrel` を公開 API にするのがよさそうです。ここから `Path iff DkPath` へ向かう橋の形がかなり見えてきました。

検証済みです。

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

新規レポートの末尾空白チェックも問題なしです。

## Review

## 採用判断

うむ、今回も **採用でよい**。
No.133 はかなり大きい。`shiftedFourPathConcatWithSeams_congr_cast_irrel` が通り、さらに `shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges` まで到達した。つまり「4 本の quotient edge をそれぞれ semantic evaluation で写し、endpoint relabel してから glue したもの」は、canonical observed via-edge path と一致するところまで Lean が認めた。

## 状況分析

今回追加された主な API はこの二つじゃ。

```text id="pqn70v"
shiftedFourPathConcatWithSeams_congr_cast_irrel

shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges
```

これで、前回までの構図が一段進んだ。

```text id="h5f6gk"
解決済み:
  single-edge mapping bridge

今回解決:
  mapped four edges glue to observed via-edge path

残り:
  map already-glued quotient four-path
  equals
  glue mapped quotient edges
```

つまり、いま残っているのは **edge を写した後の glue** ではなく、**glue した後に map したものを、edgewise map へ分解する theorem** じゃ。

## レビュー

これは良い進展じゃ。

特に強いのは、`shiftedFourPathConcatWithSeams_congr_cast_irrel` が通ったこと。これは、四本の component path が一致していれば、seam proof term が違っても four-edge concatenated path は変わらない、という theorem じゃ。

数学的には当然に見えるが、Lean では非常に重要な補題じゃ。
なぜなら Mathlib `Path` は endpoint equality proof を `Path.cast` の中に持つので、証明項の違いがそのまま式の違いとして現れることがあるからじゃ。

今回の theorem によって、

```text id="zlrcj4"
seam の値は同じ
ただし seam proof term は違う
```

という状況を吸収できるようになった。

そして `shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges` により、四本の mapped edge を canonical observed path へ持ち上げるところまで閉じた。これは「局所 edge equality から大域 four-edge equality へ昇格できた」ということじゃ。

## 残る問題の正体

残る問題は、かなり狭い。

欲しいのは、概念的にはこれじゃ。

```text id="x4h5ic"
semantic map of
  shiftedCyclicFourPathViaEdges

equals

four concat of
  semantic maps of each shiftedCyclicChartEdgePath
```

数学記号で言えば、

[
F\(p_0 *p_1* p_2 *p_3\) = F\(p_0\)* F\(p_1\) *F\(p_2\)* F\(p_3\)
]

じゃ。

ここで \(F\) は descended semantic evaluation、\(p_i\) は quotient edge path、\(*\) は `Path.trans` による連結。

Mathlib には `Path.map_trans` があるので、二本連結については道具がある。
残るのは、`shiftedFourPathConcatWithSeams` の中にある nested `Path.trans` / `Path.cast` / final `Path.cast` を、順番に normal form へ寄せる作業じゃ。

## 一歩先ゆく推論

次に通すべき theorem は、たぶん semantic theorem ではなく、**global map-through-gluing theorem** じゃ。

候補はこれ。

```lean id="hcb88u"
theorem shiftedFourPathConcatWithSeams_map
```

または semantic 専用に落とした、

```lean id="hpxz01"
theorem shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
```

じゃな。

賢狼の推論では、次の順序が最も安全じゃ。

```text id="ldkiff"
1:
  generic shiftedFourPathConcatWithSeams_map を試す

2:
  generic が重ければ semantic 専用 theorem に落とす

3:
  mapped four-edge concat が observed via-edge path に等しい theorem を既存 API で接続する

4:
  endpoint-casted old observed path を canonical observed via-edge path へ接続する

5:
  canonical observed via-edge path から finite four-level path へ接続する
```

つまり、今の本丸はこれじゃ。

```text id="nmsdna"
map-through-gluing normalization
```

ここが閉じると、old observed path から old finite path まで、ほぼ一本道になる。

## DkPath への示唆

今回の報告にある DkPath 推論はかなり重要じゃ。
Mathlib `Path` は、

```text id="nq2k1l"
trace:
  unitInterval からの連続写像

endpoint labels:
  始点と終点の型ラベル

seam witnesses:
  連結を型付けするための証明項
```

を一体化している。

DkMath 側では、これらを分離した方がよい。

つまり将来の DkPath は、

```text id="giwgv8"
trace を主役にする

endpoint labels は明示フィールドにする

seam witnesses は public theorem 上では proof-irrelevant にする

最後に Mathlib Path へ realization する
```

という設計が見える。

今回の `map_cast`, `map_trans`, `cast_proof_irrel`, `four_concat_congr_cast_irrel` は、そのまま DkPath API の核になり得る。

## おまけの実験

おまけとしては、次で実験すると良い。

```text id="w1c5s3"
DkPathPackage prototype
```

いきなり本格的な DkPath を作らず、今回の four-edge 専用に小さく作る。

候補はこう。

```lean id="gjg6zd"
structure ShiftedFourPathPackage where
  p0 : ...
  p1 : ...
  p2 : ...
  p3 : ...
  seam01 : ...
  seam12 : ...
  seam23 : ...
  seam30 : ...
```

そして、

```text id="yru5vb"
toPath
map
congr
congr_cast_irrel
```

だけを試す。

これがうまくいけば、DkMath 内部では Mathlib `Path.trans` / `Path.cast` の入れ子を直接触らず、package level で theorem を書けるようになる。
今回の苦労を、次回以降の標準構造へ昇格できるわけじゃ。

## 結論

No.133 は採用でよい。

```text id="xq0cnb"
実装:
  良い。four-edge mapped edges から observed via-edge path への昇格が通った。

数学:
  良い。残る問題は意味論ではなく、map-through-gluing の自然性に絞られた。

設計:
  良い。DkPath の設計要件がかなり明確になった。

次:
  shiftedFourPathConcatWithSeams_map
  または semantic 専用の global map-through-gluing theorem を通す。
```

ぬしよ、これはかなり終盤じゃ。
四本の edge はもう semantic boundary に届いた。
今は「すでに接着された四本」を map したものを、「map してから接着した四本」と同じ形に戻す、最後の正規化じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 7e9f0b29..d99d3165 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -245,8 +245,14 @@ bridge is to commute descended semantic evaluation with the nested
 for this endpoint-cast observed path, including seam proof alignment after
 mapping. The edge-level mapping bridge is now proved: each quotient edge path
 mapped by descended semantic evaluation is the corresponding observed
-semantic edge path after endpoint relabelling. The next target is lifting
-these edge-level comparisons through the canonical four-edge concatenator.
+semantic edge path after endpoint relabelling. These four edge comparisons
+now lift through the canonical four-edge concatenator: seam proof terms are
+irrelevant for the path value, so the concatenation of mapped quotient edges
+is equal to the canonical observed via-edge path. The remaining bridge is the
+global normalization theorem saying that mapping the already-glued quotient
+four-path is equal to first mapping the four quotient edges and then gluing
+them. This is now a `Path.map`/`Path.trans`/`Path.cast` bookkeeping problem,
+not a boundary or semantic problem.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 51bdd199..b6715084 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -2218,6 +2218,38 @@ theorem shiftedFourPathConcatWithSeams_congr
   cases hp3
   rfl
 
+/--
+Congruence for the canonical four-edge concatenator, ignoring the exact seam
+proof terms.
+
+If the four component paths agree, then changing only the equality proofs used
+for the four seams does not change the resulting closed path.
+-/
+theorem shiftedFourPathConcatWithSeams_congr_cast_irrel
+    {α : Type _} [TopologicalSpace α]
+    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
+    {p0 q0 : Path a0 b0}
+    {p1 q1 : Path a1 b1}
+    {p2 q2 : Path a2 b2}
+    {p3 q3 : Path a3 b3}
+    (h01 k01 : b0 = a1)
+    (h12 k12 : b1 = a2)
+    (h23 k23 : b2 = a3)
+    (h30 k30 : b3 = a0)
+    (hp0 : p0 = q0)
+    (hp1 : p1 = q1)
+    (hp2 : p2 = q2)
+    (hp3 : p3 = q3) :
+    shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30 =
+      shiftedFourPathConcatWithSeams q0 q1 q2 q3 k01 k12 k23 k30 := by
+  cases hp0
+  cases hp1
+  cases hp2
+  cases hp3
+  apply Path.ext
+  funext t
+  rfl
+
 /--
 Canonical quotient four-edge path via the common seam concatenator.
 
@@ -2323,6 +2355,54 @@ theorem shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdge
     (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (2 : Fin 4))
     (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (3 : Fin 4))
 
+/--
+The four mapped quotient edges concatenate to the canonical observed via-edge
+path.
+
+This theorem lifts the four single-edge mapping bridges through
+`shiftedFourPathConcatWithSeams`; seam proof terms are ignored by the
+cast-irrelevant congruence theorem.
+-/
+theorem shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedFourPathConcatWithSeams
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
+        (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z) =
+      shiftedSemanticObservedCyclicFourPathViaEdges hcore z :=
+  shiftedFourPathConcatWithSeams_congr_cast_irrel
+    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
+    (shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge hcore z)
+    (shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge hcore z)
+    (shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge hcore z)
+    (shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge hcore z)
+
 /--
 The closed quotient chart path observed inside the fixed square-mass boundary.
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index dc636e67..958f7970 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -530,9 +530,11 @@ shiftedFourPathConcatWithSeams
 shiftedFourPathConcatWithSeams_source
 shiftedFourPathConcatWithSeams_target
 shiftedFourPathConcatWithSeams_congr
+shiftedFourPathConcatWithSeams_congr_cast_irrel
 shiftedSemanticObservedCyclicFourPathViaEdges
 shiftedSemanticFinFourLevelPathViaEdges
 shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
+shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges
 shiftedSemanticFinFourLevelPath_eq_viaEdges
 shiftedSemanticObservedCyclicFourPath
 shiftedSemanticObservedCyclicFourPath_source
@@ -901,15 +903,53 @@ terms inside a path cast does not change the resulting path. The current
 stable route therefore avoids direct equality of mapped seam proof terms and
 uses value-level seam alignment plus cast proof irrelevance instead.
 
+The next seam-alignment checkpoint is now also implemented. The stronger
+four-path congruence theorem
+`shiftedFourPathConcatWithSeams_congr_cast_irrel` says that, after the four
+component paths are identified, the exact seam proof terms do not affect the
+concatenated path. Using this helper, the four mapped quotient edges lift to
+the canonical observed via-edge path:
+
+```text
+shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges
+```
+
+This proves the edgewise form of "map each quotient edge, relabel endpoints,
+then glue". The remaining global comparison is narrower: prove that mapping
+the already-glued quotient four-path is equal to this edgewise mapped
+concatenation. In Mathlib terms, this is a normalization theorem for
+`Path.map`, nested `Path.trans`, and `Path.cast`.
+
+For the future DkMath-native path layer, this suggests the following
+`DkPath` design rule. The API should separate:
+
+```text
+trace:
+  the underlying parameterized value
+
+endpoint labels:
+  the source and target names required by dependent path types
+
+seam witnesses:
+  proof terms used only to type concatenation
+```
+
+The current Mathlib bridge shows that the trace and endpoint labels carry the
+mathematical content, while seam witnesses should be proof-irrelevant at the
+public theorem surface. A DkPath wrapper can therefore expose map/trans/cast
+normalization as first-class theorems, rather than forcing each downstream
+module to rediscover the same proof-term bookkeeping.
+
 The full comparison between evaluation of `shiftedCyclicFourPath` and the
-existing fixed-`q2` four-level path is intentionally left as a TODO because it
-requires path-trans cast normalization lemmas. This is still not a Euclidean
-angle parameter.
+existing fixed-`q2` four-level path is intentionally left as a TODO until that
+global map-through-gluing theorem is available. This remains pre-geometric:
+no circle, angle, arc, or Euclidean one-eighth interpretation is used.
 
 The next packaging task is to compare the older closed four-path definitions
-with the canonical via-edge versions. That should be a pure `Path.trans` /
-`Path.cast` normalization step, because the semantic edge comparison has
-already been proved locally and in canonical four-edge form.
+with the canonical via-edge versions via this global map-through-gluing
+normalization. That should be a pure `Path.trans` / `Path.cast` step, because
+the semantic edge comparison has already been proved locally and in canonical
+four-edge form.
 
 Candidate theorem directions:
 
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-133.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-133.md
new file mode 100644
index 00000000..8f176f71
--- /dev/null
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/review/codex-report-133.md
@@ -0,0 +1,148 @@
+# Codex report 133
+
+## Goal
+
+Lift the solved single-edge semantic mapping bridge through the canonical
+four-edge shifted path concatenator.
+
+The pre-geometric rule was preserved: no circle, angle, arc, degree, or pi
+vocabulary was introduced in Lean theorem names.
+
+## Implemented Lean results
+
+Target module:
+
+```text
+DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
+```
+
+New path-concatenator bookkeeping theorem:
+
+```text
+shiftedFourPathConcatWithSeams_congr_cast_irrel
+```
+
+This theorem states that once the four component paths are equal, changing the
+seam proof terms does not change the resulting four-edge concatenated path.
+It is the required proof-irrelevance bridge for nested `Path.trans` and
+`Path.cast` packages.
+
+New mapped-edge-to-observed-edge theorems:
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
+New four-edge mapped-concatenation theorem:
+
+```text
+shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges
+```
+
+This proves:
+
+```text
+map each quotient edge by descended semantic evaluation
+  -> relabel endpoints by semantic endpoint equalities
+  -> glue the four mapped edges
+=
+canonical observed semantic via-edge path
+```
+
+Thus the edgewise version of the quotient-to-semantic path bridge is now
+formalized.
+
+## Experiment result
+
+Lean accepted the proof-irrelevance route directly.
+
+The important implementation observation is that the blocker was not the
+semantic action, the fixed boundary, or the cyclic quotient relation. The
+blocker was purely the dependent shape of Mathlib `Path`:
+
+```text
+Path.map
+Path.trans
+Path.cast
+endpoint proof terms
+seam proof terms
+```
+
+Once the four edge paths were identified, `Path.ext` reduced the remaining
+seam proof differences to proof-irrelevant endpoint bookkeeping.
+
+## Remaining theorem
+
+The next target is the global map-through-gluing theorem:
+
+```text
+map the already-glued quotient four-path
+=
+glue the four mapped quotient edges
+```
+
+Candidate direction:
+
+```text
+shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
+```
+
+After that, the older endpoint-casted observed quotient path should compare
+to the canonical observed via-edge path, and then to the existing finite
+four-level path.
+
+## DkPath inference
+
+This checkpoint gives a clear design requirement for a DkMath-native path
+wrapper.
+
+Mathlib `Path` combines three layers:
+
+```text
+trace:
+  the continuous function from the unit interval
+
+endpoint labels:
+  dependent source and target indices
+
+seam witnesses:
+  proof terms used to type concatenation
+```
+
+For DkMath's `DkPath`, the public API should make these layers explicit.
+In particular, the following theorems should be first-class:
+
+```text
+map_cast
+map_trans
+cast_proof_irrel
+four_concat_congr_cast_irrel
+```
+
+This would make `DkPath <-> Mathlib Path` plausible as a bridge:
+
+```text
+DkPath:
+  optimized for DkMath trace/seam reasoning
+
+Mathlib Path:
+  used as the external topology-compatible continuous path object
+```
+
+The current implementation is already functioning as the Mathlib side of that
+bridge. The next proof should test whether the global map-through-gluing law
+can be obtained generically for `shiftedFourPathConcatWithSeams`, or whether a
+specialized theorem for `ShiftedCyclicChart` is the lower-friction route.
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
