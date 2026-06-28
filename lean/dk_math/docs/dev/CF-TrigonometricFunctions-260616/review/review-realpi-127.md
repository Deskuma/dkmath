# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 2b7729c0da254d4a6b152016be565d089313154d

## Report

進めました。今回は 126 の主題どおり、共通の four-edge concatenator を導入し、observed 側と direct finite 側を同じ packaging に載せました。

追加した主な Lean API:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedFourPathConcatWithSeams`
  - `shiftedFourPathConcatWithSeams_source`
  - `shiftedFourPathConcatWithSeams_target`
  - `shiftedFourPathConcatWithSeams_congr`
  - `shiftedSemanticObservedCyclicFourPathViaEdges`
  - `shiftedSemanticFinFourLevelPathViaEdges`
  - `shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges`

これで、canonical via-edge 版では observed/direct の closed four path equality まで Lean が通りました。残る比較は、既存の `shiftedSemanticObservedCyclicFourPath` / `shiftedSemanticFinFourLevelPath` をこの canonical via-edge 版へ寄せる、純粋な `Path.trans` / `Path.cast` packaging 正規化です。

Docs も同期済み:

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)

確認:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift` 成功
- `lake build DkMath.Analysis.DkReal` 成功
- `git diff --check` 成功

## Review

うむ、今回も **採用でよい**。
これはかなり良い。共通の `shiftedFourPathConcatWithSeams` を導入し、observed 側と direct finite 側を同じ canonical packaging に載せたうえで、via-edge 版の closed four path equality まで Lean が通っている。これで残る比較は、ほぼ完全に「古い定義を canonical via-edge 版へ寄せる」だけになった。

## 1. 状況分析

今回追加された主な API はこれじゃ。

```text id="b48wca"
shiftedFourPathConcatWithSeams
shiftedFourPathConcatWithSeams_source
shiftedFourPathConcatWithSeams_target
shiftedFourPathConcatWithSeams_congr
shiftedSemanticObservedCyclicFourPathViaEdges
shiftedSemanticFinFourLevelPathViaEdges
shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
```

今回の到達点は大きい。

```text id="uq2rv7"
single edge:
  observed quotient edge path = direct finite level path

canonical four-edge:
  observed via-edge four path = finite via-edge four path

remaining:
  existing old closed four-path definitions = canonical via-edge versions
```

つまり、意味の比較はもう通っている。
残るのは、古い closed path 定義が、新しい標準 four-edge concatenator と同じ包装であることの確認じゃ。

## 2. レビュー

実装方針は正しい。

特に良いのは、`shiftedFourPathConcatWithSeams_congr` を入れたことじゃ。

```lean id="a6mtcx"
theorem shiftedFourPathConcatWithSeams_congr
```

これにより、四つの component path がそれぞれ等しければ、同じ seam で閉じた four-path 全体も等しい、と言える。

これは今後かなり効く。
`Path.trans` の入れ子を毎回ほどくのではなく、共通コンストラクタを使って比較できるようになった。

docs 側にも、canonical via-edge equality は四つの single-edge equality から従い、古い closed four-path 定義との比較はまだ無理に押していない、と整理されている。

## 3. 今回の本丸

今回の本丸はこれじゃ。

```lean id="yz4nca"
theorem shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
```

この theorem により、observed quotient edge を一つずつ観測して四本連結したものと、direct finite edge を四本連結したものが等しいと証明された。

意味はこう。

```text id="fqof2n"
quotient edge を観測する
  equals
finite level edge

therefore:
  four observed edges concatenated
  equals
  four finite level edges concatenated
```

これは、full comparison の中核そのものじゃ。

## 4. 残る TODO の正体

いま残っている TODO は、以前よりかなり狭い。

比較したい古い定義はこれ。

```lean id="d9cjzy"
shiftedSemanticObservedCyclicFourPath
```

```lean id="xghrrv"
shiftedSemanticFinFourLevelPath
```

一方で、今回作った canonical 版はこれ。

```lean id="f3z2lb"
shiftedSemanticObservedCyclicFourPathViaEdges
```

```lean id="f7baew"
shiftedSemanticFinFourLevelPathViaEdges
```

すでに canonical 同士の equality はある。
したがって残る道はこれじゃ。

```text id="n29u5g"
old observed path
  equals
canonical observed via-edge path

old finite four-level path
  equals
canonical finite via-edge path
```

この二つが通れば、最終的に古い定義同士も等しい。

```text id="urks8s"
old observed
  = canonical observed
  = canonical finite
  = old finite
```

ここまで見えた。

## 5. 次の一歩

次に狙うべきは、古い定義と canonical via-edge 定義の比較じゃ。

まずは finite 側が狙いやすい可能性が高い。

```lean id="ylp6ij"
shiftedSemanticFinFourLevelPath_eq_viaEdges
```

もし古い `shiftedSemanticFinFourLevelPath` も、今回の `shiftedFourPathConcatWithSeams` と同じ形の `Path.trans` / `Path.cast` で定義されているなら、これは `rfl` や `simp` で通る可能性がある。

同様に、quotient 側も試せる。

```lean id="deh1yx"
shiftedCyclicFourPath_eq_viaEdges
```

ただし observed 側は `shiftedSemanticObservedCyclicFourPath` が「quotient four path を evaluation で写したもの」なので、canonical observed via-edge path との比較は少し重いかもしれぬ。
その場合は、まず quotient 側の old path と via-edge path の一致を通すのがよい。

## 6. 一歩先ゆくおまけ実験

おまけとして試す価値が高いのは、**quotient four path の canonical 版** を作ることじゃ。

今あるのは、

```lean id="n5z0nn"
shiftedCyclicFourPath
```

だが、これを共通 concatenator で再定義した版を作る。

```lean id="e46rs5"
shiftedCyclicFourPathViaEdges
```

そして、

```lean id="anr3mg"
shiftedCyclicFourPath_eq_viaEdges
```

を試す。

これが通れば、observed old path は

```text id="y5ixmw"
evaluation of shiftedCyclicFourPath
```

なので、次に

```text id="ijjm11"
evaluation of shiftedCyclicFourPathViaEdges
```

へ寄せられる。
そこから single-edge observed path との比較が使いやすくなる。

これは次の breakthrough になりそうじゃ。

## 7. 結論

今回の差分は採用でよい。

```text id="v08er1"
実装:
  良い。共通 four-edge concatenator と congr theorem が入った。

数学:
  良い。canonical via-edge 版では observed/direct の closed path equality が通った。

設計:
  良い。古い closed path 定義との比較を残し、semantic obstruction ではなく packaging normalization として整理できている。

次:
  old closed four-path definitions を canonical via-edge versions へ寄せる。
```

ぬしよ、これはかなり強い。
「同じものを見ている」は、もう canonical 版では Lean が認めた。残るのは古い包装と新しい標準包装を揃える作業じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index f0cecd6c..27c60b7f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -228,7 +228,10 @@ wrapper for the later full path comparison. A single observed quotient edge
 is also packaged as a fixed-boundary path and proved equal to the direct
 finite fixed-boundary edge path. The remaining four-edge comparison is
 therefore a normalization problem for nested `Path.trans` and endpoint casts,
-not a semantic obstruction.
+not a semantic obstruction. A reusable four-edge concatenator with explicit
+seams now packages canonical via-edge observed and direct finite closed
+paths, and those two canonical paths are equal by the four single-edge
+equalities.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 35396d4e..054aa5df 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -2001,6 +2001,159 @@ theorem shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
   rw [shiftedSemanticObservedCyclicEdgePath_apply]
   rw [shiftedSemanticFinLevelPath_apply_eq_levelEdge]
 
+/--
+Canonical four-edge concatenation with explicit seam equalities.
+
+This helper fixes one standard packaging for a closed four-edge traversal.
+It is intentionally generic and pre-geometric: it only records how four paths
+are glued by endpoint equalities.
+-/
+def shiftedFourPathConcatWithSeams
+    {α : Type _} [TopologicalSpace α]
+    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
+    (p0 : Path a0 b0)
+    (p1 : Path a1 b1)
+    (p2 : Path a2 b2)
+    (p3 : Path a3 b3)
+    (h01 : b0 = a1)
+    (h12 : b1 = a2)
+    (h23 : b2 = a3)
+    (h30 : b3 = a0) :
+    Path a0 a0 :=
+  (((p0.trans (p1.cast h01 rfl)).trans
+    (p2.cast h12 rfl)).trans
+    (p3.cast h23 rfl)).cast rfl h30.symm
+
+/-- The canonical four-edge concatenator starts at its first source. -/
+theorem shiftedFourPathConcatWithSeams_source
+    {α : Type _} [TopologicalSpace α]
+    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
+    (p0 : Path a0 b0)
+    (p1 : Path a1 b1)
+    (p2 : Path a2 b2)
+    (p3 : Path a3 b3)
+    (h01 : b0 = a1)
+    (h12 : b1 = a2)
+    (h23 : b2 = a3)
+    (h30 : b3 = a0) :
+    shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30 0 =
+      a0 :=
+  (shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30).source
+
+/-- The canonical four-edge concatenator returns to its first source. -/
+theorem shiftedFourPathConcatWithSeams_target
+    {α : Type _} [TopologicalSpace α]
+    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
+    (p0 : Path a0 b0)
+    (p1 : Path a1 b1)
+    (p2 : Path a2 b2)
+    (p3 : Path a3 b3)
+    (h01 : b0 = a1)
+    (h12 : b1 = a2)
+    (h23 : b2 = a3)
+    (h30 : b3 = a0) :
+    shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30 1 =
+      a0 :=
+  (shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30).target
+
+/--
+Congruence for the canonical four-edge concatenator with fixed seams.
+
+Once two edge packages use the same endpoint equalities, equality of the four
+component paths is enough to identify the closed concatenations.
+-/
+theorem shiftedFourPathConcatWithSeams_congr
+    {α : Type _} [TopologicalSpace α]
+    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
+    {p0 q0 : Path a0 b0}
+    {p1 q1 : Path a1 b1}
+    {p2 q2 : Path a2 b2}
+    {p3 q3 : Path a3 b3}
+    (h01 : b0 = a1)
+    (h12 : b1 = a2)
+    (h23 : b2 = a3)
+    (h30 : b3 = a0)
+    (hp0 : p0 = q0)
+    (hp1 : p1 = q1)
+    (hp2 : p2 = q2)
+    (hp3 : p3 = q3) :
+    shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30 =
+      shiftedFourPathConcatWithSeams q0 q1 q2 q3 h01 h12 h23 h30 := by
+  cases hp0
+  cases hp1
+  cases hp2
+  cases hp3
+  rfl
+
+/--
+Canonical four-edge path obtained by observing quotient edges individually.
+
+This avoids comparing against the older closed quotient path packaging
+directly. The four single-edge observations are first put into one standard
+concatenation shape.
+-/
+def shiftedSemanticObservedCyclicFourPathViaEdges
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path
+      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4))
+      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)) :=
+  shiftedFourPathConcatWithSeams
+    (shiftedSemanticObservedCyclicEdgePath hcore z (0 : Fin 4))
+    (shiftedSemanticObservedCyclicEdgePath hcore z (1 : Fin 4))
+    (shiftedSemanticObservedCyclicEdgePath hcore z (2 : Fin 4))
+    (shiftedSemanticObservedCyclicEdgePath hcore z (3 : Fin 4))
+    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
+
+/--
+Canonical four-edge path obtained from direct finite fixed-boundary edges.
+
+It uses the same concatenator and the same seam equalities as the observed
+quotient-edge version.
+-/
+def shiftedSemanticFinFourLevelPathViaEdges
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path
+      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4))
+      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)) :=
+  shiftedFourPathConcatWithSeams
+    (shiftedSemanticFinLevelPath hcore z (0 : Fin 4))
+    (shiftedSemanticFinLevelPath hcore z (1 : Fin 4))
+    (shiftedSemanticFinLevelPath hcore z (2 : Fin 4))
+    (shiftedSemanticFinLevelPath hcore z (3 : Fin 4))
+    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
+
+/--
+The canonical observed four-edge path equals the canonical direct finite path.
+
+Because both sides use the same four-path concatenator, the proof reduces to
+the four single-edge observed/direct equalities.
+-/
+theorem shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticObservedCyclicFourPathViaEdges hcore z =
+      shiftedSemanticFinFourLevelPathViaEdges hcore z :=
+  shiftedFourPathConcatWithSeams_congr
+    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
+    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
+    (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (0 : Fin 4))
+    (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (1 : Fin 4))
+    (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (2 : Fin 4))
+    (shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath hcore z (3 : Fin 4))
+
 /--
 The closed quotient chart path observed inside the fixed square-mass boundary.
 
@@ -2218,11 +2371,18 @@ The source/target comparison is also exposed after `Subtype.val`. A single
 observed quotient edge is packaged as a fixed-boundary path and proved equal
 to the direct finite fixed-boundary edge path, so the remaining four-edge
 comparison is only nested path-packaging normalization.
+A canonical four-edge concatenator with explicit seams now packages both the
+observed-edge and direct finite-edge versions. These canonical via-edge
+closed paths are equal by the four single-edge equalities.
 
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
 path after path-trans cast normalization lemmas are available.
 
+[TODO: semantic-cf2d/shifted-cyclic-via-edge-compare]
+Compare the older closed four-path definitions with the canonical via-edge
+versions after the common concatenator is stable.
+
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
 continuous evaluation API has downstream consumers.
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index c17d123d..04e0fabe 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -515,6 +515,13 @@ shiftedSemanticCyclicChartEval_edgePath_zero
 shiftedSemanticObservedCyclicEdgePath
 shiftedSemanticObservedCyclicEdgePath_apply
 shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
+shiftedFourPathConcatWithSeams
+shiftedFourPathConcatWithSeams_source
+shiftedFourPathConcatWithSeams_target
+shiftedFourPathConcatWithSeams_congr
+shiftedSemanticObservedCyclicFourPathViaEdges
+shiftedSemanticFinFourLevelPathViaEdges
+shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
 shiftedSemanticObservedCyclicFourPath
 shiftedSemanticObservedCyclicFourPath_source
 shiftedSemanticObservedCyclicFourPath_target
@@ -726,6 +733,32 @@ shiftedSemanticObservedCyclicEdgePath_apply
 shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
 ```
 
+The four-edge packaging has also been standardized. The helper
+`shiftedFourPathConcatWithSeams` glues four paths by explicit endpoint seam
+equalities, exposes source and target aliases, and has a congruence theorem
+for replacing all four component paths at once:
+
+```text
+shiftedFourPathConcatWithSeams
+shiftedFourPathConcatWithSeams_source
+shiftedFourPathConcatWithSeams_target
+shiftedFourPathConcatWithSeams_congr
+```
+
+Using that common concatenator, the observed quotient-edge package and the
+direct finite-edge package are now available as canonical via-edge closed
+paths:
+
+```text
+shiftedSemanticObservedCyclicFourPathViaEdges
+shiftedSemanticFinFourLevelPathViaEdges
+shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
+```
+
+The canonical via-edge equality follows from the four single-edge equalities.
+The older closed four-path definitions are intentionally not forced into this
+shape yet.
+
 Value-level source and target comparisons are also available for the closed
 four-edge paths:
 
@@ -745,6 +778,11 @@ existing fixed-`q2` four-level path is intentionally left as a TODO because it
 requires path-trans cast normalization lemmas. This is still not a Euclidean
 angle parameter.
 
+The next packaging task is to compare the older closed four-path definitions
+with the canonical via-edge versions. That should be a pure `Path.trans` /
+`Path.cast` normalization step, because the semantic edge comparison has
+already been proved locally and in canonical four-edge form.
+
 Candidate theorem directions:
 
 ```text
````
`````
