# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 88d8bf9878b511eb96e1be6cd38d9b6f403b5faa

## Report

進めました。127 では、旧定義と canonical via-edge 版の比較を安定するところまで入れています。

追加した主な Lean API:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedCyclicFourPathViaEdges`
  - `shiftedCyclicFourPath_eq_viaEdges`
  - `shiftedSemanticFinFourLevelPath_eq_viaEdges`

結果として、旧 quotient closed path と旧 finite four-level path は、それぞれ canonical via-edge 版へ `rfl` で落ちることが確定しました。

一方で、旧 observed path と canonical observed via-edge path の full equality / pointwise equality は今回は止めました。理由は明確で、旧 observed path は「closed quotient path を評価する」形、canonical observed via-edge は「edge ごとに評価してから concat する」形です。ここには descended semantic evaluation と `Path.trans`/`Path.cast` concatenator の可換性 lemma が必要です。コード内 TODO と docs にこの障害点を明記しました。

Docs 同期済み:

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)

確認:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift` 成功
- `lake build DkMath.Analysis.DkReal` 成功
- `git diff --check` 成功

## Review

## 採用判断

うむ、今回も **採用でよい**。
127 は非常に良い進め方じゃ。旧 quotient closed path と旧 finite four-level path が、それぞれ canonical via-edge 版へ `rfl` で落ちることが確認された。これで、残る障害はかなり明確になった。旧 observed path だけが「closed quotient path を評価してから path にする」形なので、ここには **semantic evaluation と four-path concatenator の可換性** が必要になる。

## 状況分析

今回追加された主な API はこれじゃ。

```text id="numjwn"
shiftedCyclicFourPathViaEdges
shiftedCyclicFourPath_eq_viaEdges
shiftedSemanticFinFourLevelPath_eq_viaEdges
```

現在の構図はこうなった。

```text id="ducg68"
old quotient closed path:
  shiftedCyclicFourPath

canonical quotient via-edge path:
  shiftedCyclicFourPathViaEdges

old finite four-level path:
  shiftedSemanticFinFourLevelPath

canonical finite via-edge path:
  shiftedSemanticFinFourLevelPathViaEdges

canonical observed via-edge path:
  shiftedSemanticObservedCyclicFourPathViaEdges
```

すでに通っているものはこれ。

```text id="ycb4jl"
shiftedCyclicFourPath = shiftedCyclicFourPathViaEdges

shiftedSemanticFinFourLevelPath = shiftedSemanticFinFourLevelPathViaEdges

shiftedSemanticObservedCyclicFourPathViaEdges =
  shiftedSemanticFinFourLevelPathViaEdges
```

つまり、finite 側と quotient 側の old-to-canonical はかなり整理された。

残るのはこの一点じゃ。

```text id="kjxb8o"
shiftedSemanticObservedCyclicFourPath
  を
shiftedSemanticObservedCyclicFourPathViaEdges
  へ寄せる
```

## レビュー

今回の判断は正しい。

特に、旧 observed path と canonical observed via-edge path の full equality を無理に押さなかった点がよい。
ここは単なる `Path.trans` 正規化だけではなく、写像 `shiftedSemanticCyclicChartEval` と four-path concatenation の可換性が絡む。

旧 observed path はこういう形じゃ。

```text id="tom2t5"
first:
  quotient closed path を作る

then:
  semantic evaluation で fixed-boundary へ写す
```

一方、canonical observed via-edge path はこうじゃ。

```text id="ynguvn"
first:
  quotient edge ごとに semantic evaluation する

then:
  fixed-boundary edge path として四本を連結する
```

これは数学的には同じはずじゃが、Lean では「map が `Path.trans` と `Path.cast` を保つ」補題が必要になる。

Docs にも、残る bridge は descended semantic evaluation と canonical four-path concatenator の可換性である、と明記されている。これは非常に良い整理じゃ。

## TODO の意味

今回で TODO の正体はさらに細くなった。

以前の TODO は広く、

```text id="zwzyfv"
observed closed quotient path
  と
finite four-level path
  を比較する
```

だった。

今はこう分解できる。

```text id="hul59d"
old observed path
  compared with
canonical observed via-edge path

canonical observed via-edge path
  already equals
canonical finite via-edge path

canonical finite via-edge path
  already equals
old finite path
```

つまり、次の bridge が通れば終わりが見える。

```lean id="mx481v"
theorem shiftedSemanticObservedCyclicFourPath_cast_eq_viaEdges
```

あるいは endpoint 型をそろえた形で、

```lean id="b5t8ya"
theorem shiftedSemanticObservedCyclicFourPath_eq_viaEdges_after_cast
```

という方向じゃ。

## 次の方針

次は、旧 observed path を直接 `shiftedSemanticObservedCyclicFourPathViaEdges` と比較するのではなく、まず endpoint 型をそろえるのがよい。

理由は、旧 observed path の endpoint は、

```lean id="cfdpwa"
shiftedSemanticCyclicChartEval hcore z
  (shiftedCyclicChartLeft (0 : Fin 4))
```

であり、canonical observed via-edge path の endpoint は、

```lean id="akhxm7"
shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)
```

じゃ。

この二つはすでに

```lean id="wkevjq"
shiftedSemanticCyclicChartEval_left_zero
```

で等しい。

だから、旧 observed path を `Path.cast` で finite endpoint 型へ寄せた版を作るのが自然じゃ。

```text id="kpi93n"
old observed path
  cast endpoints to finite left endpoint

then compare:
  casted old observed path
  with canonical observed via-edge path
```

これが次の最短路に見える。

## 一歩先ゆくおまけ実験

おまけとして試す価値が高いのは、汎用の **map-concat lemma** じゃ。

つまり、連続写像 \(f\) が path concatenation と可換である、という補題。

ただし、いきなり完全汎用にすると dependent endpoint が重くなる。
だから、最初は今回の構造専用にするのが良い。

狙いはこうじゃ。

```text id="txpdio"
evaluating
  shiftedFourPathConcatWithSeams on quotient paths

is equal to
  shiftedFourPathConcatWithSeams on evaluated paths
```

これが通れば、旧 observed path から canonical observed via-edge path へ一気に橋がかかる可能性がある。

## 結論

今回の差分は採用でよい。

```text id="zl0tbg"
実装:
  良い。old quotient path と old finite path が canonical via-edge 版へ rfl で落ちた。

数学:
  良い。canonical via-edge 版では observed/direct equality がすでに成立している。

設計:
  良い。残る障害を evaluation と four-path concatenator の可換性へ絞った。

次:
  observed old path を endpoint cast で canonical observed path と比較し、
  必要なら map-concat lemma を局所的に作る。
```

ぬしよ、ここまで来るとかなり詰まってきた。
いま残っているのは「同じ道を、先に写してから貼るか、貼ってから写すか」の交換法則じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 27c60b7f..507db4d0 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -231,7 +231,10 @@ therefore a normalization problem for nested `Path.trans` and endpoint casts,
 not a semantic obstruction. A reusable four-edge concatenator with explicit
 seams now packages canonical via-edge observed and direct finite closed
 paths, and those two canonical paths are equal by the four single-edge
-equalities.
+equalities. The older quotient closed path and the older finite four-level
+path are definitionally equal to their canonical via-edge versions. The
+remaining bridge is to commute descended semantic evaluation with the
+canonical four-path concatenator for the older observed path.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 054aa5df..7c316e21 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -2085,6 +2085,29 @@ theorem shiftedFourPathConcatWithSeams_congr
   cases hp3
   rfl
 
+/--
+Canonical quotient four-edge path via the common seam concatenator.
+
+This is the quotient-chart version of the canonical via-edge packaging used
+for semantic observations below.
+-/
+def shiftedCyclicFourPathViaEdges :
+    Path (shiftedCyclicChartLeft (0 : Fin 4))
+      (shiftedCyclicChartLeft (0 : Fin 4)) :=
+  shiftedFourPathConcatWithSeams
+    (shiftedCyclicChartEdgePath (0 : Fin 4))
+    (shiftedCyclicChartEdgePath (1 : Fin 4))
+    (shiftedCyclicChartEdgePath (2 : Fin 4))
+    (shiftedCyclicChartEdgePath (3 : Fin 4))
+    shiftedCyclicChartRight_zero_eq_one_left
+    shiftedCyclicChartRight_one_eq_two_left
+    shiftedCyclicChartRight_two_eq_three_left
+    shiftedCyclicChartRight_three_eq_zero_left
+
+/-- The older quotient closed path is definitionally the canonical via-edge path. -/
+theorem shiftedCyclicFourPath_eq_viaEdges :
+    shiftedCyclicFourPath = shiftedCyclicFourPathViaEdges := rfl
+
 /--
 Canonical four-edge path obtained by observing quotient edges individually.
 
@@ -2132,6 +2155,19 @@ def shiftedSemanticFinFourLevelPathViaEdges
     (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
     (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
 
+/--
+The older finite four-level path is the canonical direct finite via-edge path.
+
+The `Fin 4` wrappers are thin aliases for the indexed paths and seams used by
+the older definition.
+-/
+theorem shiftedSemanticFinFourLevelPath_eq_viaEdges
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinFourLevelPath hcore z =
+      shiftedSemanticFinFourLevelPathViaEdges hcore z := rfl
+
 /--
 The canonical observed four-edge path equals the canonical direct finite path.
 
@@ -2374,14 +2410,18 @@ comparison is only nested path-packaging normalization.
 A canonical four-edge concatenator with explicit seams now packages both the
 observed-edge and direct finite-edge versions. These canonical via-edge
 closed paths are equal by the four single-edge equalities.
+The older quotient closed path is definitionally equal to its canonical
+via-edge form, and the older finite fixed-boundary four-level path is
+definitionally equal to the canonical direct finite via-edge form.
 
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
 path after path-trans cast normalization lemmas are available.
 
 [TODO: semantic-cf2d/shifted-cyclic-via-edge-compare]
-Compare the older closed four-path definitions with the canonical via-edge
-versions after the common concatenator is stable.
+The quotient-side closed path and finite closed path match their canonical
+via-edge versions. The observed quotient path still needs a lemma commuting
+descended semantic evaluation with the canonical four-path concatenator.
 
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 04e0fabe..d1d32024 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -505,6 +505,8 @@ shiftedCyclicChartEdgePath_apply
 shiftedCyclicChartEdgePath_source
 shiftedCyclicChartEdgePath_target
 shiftedCyclicFourPath
+shiftedCyclicFourPathViaEdges
+shiftedCyclicFourPath_eq_viaEdges
 shiftedCyclicFourPath_source
 shiftedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_edgePath
@@ -522,6 +524,7 @@ shiftedFourPathConcatWithSeams_congr
 shiftedSemanticObservedCyclicFourPathViaEdges
 shiftedSemanticFinFourLevelPathViaEdges
 shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
+shiftedSemanticFinFourLevelPath_eq_viaEdges
 shiftedSemanticObservedCyclicFourPath
 shiftedSemanticObservedCyclicFourPath_source
 shiftedSemanticObservedCyclicFourPath_target
@@ -756,8 +759,21 @@ shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
 ```
 
 The canonical via-edge equality follows from the four single-edge equalities.
-The older closed four-path definitions are intentionally not forced into this
-shape yet.
+The older quotient closed path is also definitionally equal to its canonical
+via-edge quotient path, and the older finite four-level path is definitionally
+equal to the canonical direct finite via-edge path:
+
+```text
+shiftedCyclicFourPathViaEdges
+shiftedCyclicFourPath_eq_viaEdges
+shiftedSemanticFinFourLevelPath_eq_viaEdges
+```
+
+The older observed closed path is intentionally not forced into this shape
+yet. It is typed at the observed quotient left endpoint, while the canonical
+observed via-edge path is typed at the finite left endpoint. Even pointwise,
+the remaining theorem must commute descended semantic evaluation with the
+canonical four-path concatenator.
 
 Value-level source and target comparisons are also available for the closed
 four-edge paths:
@@ -773,6 +789,11 @@ normalizing the nested `Path.trans` and endpoint `Path.cast` structure used by
 the two closed four-path packages, without asserting any circle, angle, arc,
 or Euclidean one-eighth reading.
 
+More precisely, the quotient-side closed path and finite closed path now match
+their canonical via-edge versions. The observed quotient path still needs a
+lemma commuting descended semantic evaluation with the canonical four-path
+concatenator.
+
 The full comparison between evaluation of `shiftedCyclicFourPath` and the
 existing fixed-`q2` four-level path is intentionally left as a TODO because it
 requires path-trans cast normalization lemmas. This is still not a Euclidean
````
`````
