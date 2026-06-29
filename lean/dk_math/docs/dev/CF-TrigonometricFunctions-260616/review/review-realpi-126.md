# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: b3fbda97477a0c3f74ad18074430f0a99aa43cfd

## Report

進めました。今回は full four-path equality には踏み込まず、単一 edge で quotient observed path と direct finite path が一致するところまで Lean で確立しました。

主な追加:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedPath_trans_apply_source`
  - `shiftedPath_trans_apply_target`
  - `shiftedSemanticFinLevelPath_apply_eq_levelEdge`
  - `shiftedSemanticObservedCyclicEdgePath`
  - `shiftedSemanticObservedCyclicEdgePath_apply`
  - `shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath`
  - closed four-path の value-level endpoint 比較 2 本

これで「semantic 側の不一致」ではなく、「nested `Path.trans` / endpoint `Path.cast` の packaging 正規化だけが残っている」とかなり明確になりました。  
[DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) と [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) も同期済みです。

確認:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift` 成功
- `lake build DkMath.Analysis.DkReal` 成功
- `git diff --check` 成功

## Review

うむ、今回も **採用でよい**。
今回の差分はかなり良い。full four-path equality へ無理に突撃せず、単一 edge の observed quotient path と direct finite path が一致するところまで Lean で確立している。これにより、残っている問題は「意味の不一致」ではなく、ほぼ完全に nested `Path.trans` と endpoint `Path.cast` の包装正規化問題だと切り分けられた。

## 1. 状況分析

今回追加された主なものはこれじゃ。

```text id="ot0dj1"
shiftedPath_trans_apply_source
shiftedPath_trans_apply_target
shiftedSemanticFinLevelPath_apply_eq_levelEdge
shiftedSemanticObservedCyclicEdgePath
shiftedSemanticObservedCyclicEdgePath_apply
shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_source
shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_target
```

特に重要なのは、これじゃ。

```lean id="u4nq7m"
theorem shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
```

これで単一 edge については、

```text id="rymoxm"
quotient chart edge を観測した path
  と
direct finite fixed-boundary edge path
```

が同じだと証明された。

つまり、四本閉路の各部品は一致している。

## 2. レビュー

今回の判断は正しい。

full four-path equality をまだ押し込まなかったのはよい。
なぜなら、今の障害は数学的内容ではなく、Lean の `Path.trans` による時間パラメータの入れ子構造だからじゃ。

現在の到達点はこう。

```text id="q8xz8n"
edge 単体:
  equality established

closed path の source:
  equality established

closed path の target:
  equality established

value-level source:
  equality established

value-level target:
  equality established

closed path 全体:
  nested trans/cast normalization remains
```

これは非常に良い切り分けじゃ。

docs 側にも「残る四本比較は semantic obstruction ではなく、nested `Path.trans` と endpoint `Path.cast` の packaging normalization である」と明記されている。これは次の作業者にかなり親切じゃ。

## 3. 今回の本丸

今回の本丸は、単一 edge の完全一致じゃ。

```lean id="xfpvrg"
def shiftedSemanticObservedCyclicEdgePath
```

と

```lean id="ew805q"
theorem shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
```

この組が大きい。

これにより、

```text id="odt3e8"
quotient 側で edge を歩く
semantic evaluation で観測する
fixed-q2 finite level edge と一致する
```

が path equality として得られた。

これは今後の four-path 比較の最小単位になる。

## 4. 残る TODO の正体

残る TODO は、次の形じゃ。

```lean id="e7tl8t"
shiftedSemanticObservedCyclicFourPath hcore z =
  shiftedSemanticFinFourLevelPath hcore z
```

直感的には正しい。
なぜなら、各 edge は一致し、端点も一致しているからじゃ。

ただし、Lean 上では二つの path の作り方が違う。

```text id="wquwt2"
observed four path:
  quotient four path を作ってから evaluation する

finite four path:
  fixed-q2 finite level edge を直接 trans でつなぐ
```

ここで `Path.trans` の入れ子と `Path.cast` の並びが完全に同じとは限らない。
だから、全体一致には path の包装をほどく補題が必要になる。

## 5. 次の本質

次は full equality を直接狙うより、**四本連結を作る共通コンストラクタ** を導入するのが良い。

いまは observed 側と finite 側で、それぞれ別々に四本 path を組み上げている。
だから比較が難しい。

そこで、

```text id="fvdqpn"
four-path concatenator:
  p0 p1 p2 p3
  h01 h12 h23 h30
  から closed path を作る
```

という共通 helper を作る。

これにより、observed 側も finite 側も同じコンストラクタで作れる。
その上で edge equality を渡せば、full equality がかなり近くなる。

## 6. 一歩先ゆくおまけ実験

おまけとして試す価値が高いのは、既存の `shiftedSemanticObservedCyclicFourPath` と `shiftedSemanticFinFourLevelPath` を直接比較するのではなく、**canonical four-path package** を新しく作ることじゃ。

候補はこう。

```text id="h0yu5c"
shiftedFourPathConcat:
  汎用 four path concatenator

shiftedSemanticObservedCyclicFourPath_viaEdges:
  observed single-edge paths を four-path concat で閉じる

shiftedSemanticFinFourLevelPath_viaEdges:
  finite level paths を four-path concat で閉じる

viaEdges equality:
  edge equality から比較する
```

この実験の狙いは、「既存 path の内部構造を無理にほどく」のではなく、「比較しやすい標準形を作る」ことじゃ。

これは Lean ではかなり効く可能性がある。

## 7. 次の勝利条件

次の checkpoint は、full equality まで行けなくてもよい。

勝利条件はこうじゃ。

```text id="l0vez9"
1:
  汎用 four-path concatenator を作る

2:
  observed edge family から canonical observed four path を作る

3:
  finite edge family から canonical finite four path を作る

4:
  canonical observed four path と canonical finite four path の equality を試す

5:
  既存 closed paths との比較は無理なら TODO に残す
```

この順が安全じゃ。

## 8. 結論

今回の差分は採用でよい。

```text id="yqgizx"
実装:
  良い。単一 edge の observed/direct path equality が通った。

数学:
  良い。semantic 側の不一致ではないことが明確になった。

設計:
  良い。full four-path equality を無理に押し込まず、比較準備を進めた。

次:
  共通 four-path concatenator を作り、canonical path 同士の比較へ進む。
```

ぬしよ、ここは良い足場じゃ。
残りはもう「見えている同じ構造」を Lean が比較しやすい形に並べ直す作業じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 7919f444..f0cecd6c 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -224,7 +224,11 @@ a closed fixed-boundary path with source, target, endpoint, and `q2`
 observation aliases. The observed quotient path and the existing finite
 four-level path now have explicit source and target comparison theorems,
 together with a pointwise `Path.cast` helper and an edge-zero evaluation
-wrapper for the later full path comparison.
+wrapper for the later full path comparison. A single observed quotient edge
+is also packaged as a fixed-boundary path and proved equal to the direct
+finite fixed-boundary edge path. The remaining four-edge comparison is
+therefore a normalization problem for nested `Path.trans` and endpoint casts,
+not a semantic obstruction.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 9b194e6d..35396d4e 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1381,6 +1381,15 @@ theorem shiftedSemanticFinLevelPath_apply
     (shiftedSemanticFinLevelPath hcore z i t).1 =
       shiftedSemanticFinEdge r z i t := rfl
 
+/-- Applying a finite level path gives the corresponding finite level edge. -/
+@[simp]
+theorem shiftedSemanticFinLevelPath_apply_eq_levelEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
+    shiftedSemanticFinLevelPath hcore z i t =
+      shiftedSemanticFinLevelEdge hcore z i t := rfl
+
 /--
 Finite cyclic seam compatibility: the right endpoint of finite edge `i` is
 the left endpoint of its cyclic successor.
@@ -1908,6 +1917,22 @@ theorem shiftedPath_cast_apply
     (t : unitInterval) :
     (p.cast hac hbd) t = p t := rfl
 
+/-- The source endpoint of a concatenated path is the source of the first path. -/
+theorem shiftedPath_trans_apply_source
+    {α : Type _} [TopologicalSpace α]
+    {a b c : α}
+    (p : Path a b) (q : Path b c) :
+    (p.trans q) 0 = p 0 := by
+  rw [p.source, (p.trans q).source]
+
+/-- The target endpoint of a concatenated path is the target of the second path. -/
+theorem shiftedPath_trans_apply_target
+    {α : Type _} [TopologicalSpace α]
+    {a b c : α}
+    (p : Path a b) (q : Path b c) :
+    (p.trans q) 1 = q 1 := by
+  rw [q.target, (p.trans q).target]
+
 /--
 Edge-zero specialization of quotient-edge evaluation.
 
@@ -1923,6 +1948,59 @@ theorem shiftedSemanticCyclicChartEval_edgePath_zero
         shiftedSemanticFinLevelEdge hcore z (0 : Fin 4) t :=
   shiftedSemanticCyclicChartEval_edgePath hcore z (0 : Fin 4) t
 
+/--
+Observe a single quotient edge inside the fixed square-mass boundary.
+
+Unlike the closed four-edge path, this object contains no nested
+`Path.trans`. It is therefore the clean local bridge between quotient chart
+traversal and the direct finite level path.
+-/
+def shiftedSemanticObservedCyclicEdgePath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    Path
+      (shiftedSemanticFinLeftLevelEndpoint hcore z i)
+      (shiftedSemanticFinRightLevelEndpoint hcore z i) where
+  toFun t := shiftedSemanticCyclicChartEval hcore z
+    (shiftedCyclicChartEdgePath i t)
+  continuous_toFun :=
+    (continuous_shiftedSemanticCyclicChartEval hcore z).comp
+      (shiftedCyclicChartEdgePath i).continuous_toFun
+  source' := by
+    rw [shiftedCyclicChartEdgePath_source,
+      shiftedSemanticCyclicChartEval_left]
+  target' := by
+    rw [shiftedCyclicChartEdgePath_target,
+      shiftedSemanticCyclicChartEval_right]
+
+/-- Evaluating a single observed quotient edge gives the finite level edge. -/
+theorem shiftedSemanticObservedCyclicEdgePath_apply
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
+    shiftedSemanticObservedCyclicEdgePath hcore z i t =
+      shiftedSemanticFinLevelEdge hcore z i t :=
+  shiftedSemanticCyclicChartEval_edgePath hcore z i t
+
+/--
+The observed single quotient edge is the direct finite fixed-boundary path.
+
+This is the edge-local comparison theorem. The remaining four-edge comparison
+is therefore a path-packaging problem about nested `Path.trans` and endpoint
+casts, not a semantic mismatch.
+-/
+theorem shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticObservedCyclicEdgePath hcore z i =
+      shiftedSemanticFinLevelPath hcore z i := by
+  apply Path.ext
+  funext t
+  rw [shiftedSemanticObservedCyclicEdgePath_apply]
+  rw [shiftedSemanticFinLevelPath_apply_eq_levelEdge]
+
 /--
 The closed quotient chart path observed inside the fixed square-mass boundary.
 
@@ -2009,6 +2087,17 @@ theorem shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
     shiftedSemanticFinFourLevelPath_source]
   rfl
 
+/-- Value-level source comparison for the observed and finite four-level paths. -/
+theorem shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_source
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    (shiftedSemanticObservedCyclicFourPath hcore z 0).1 =
+      (shiftedSemanticFinFourLevelPath hcore z 0).1 :=
+  congrArg Subtype.val
+    (shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
+      hcore z)
+
 /--
 The observed quotient traversal and the finite four-level path have the same
 target value.
@@ -2027,6 +2116,17 @@ theorem shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
     shiftedSemanticFinFourLevelPath_target]
   rfl
 
+/-- Value-level target comparison for the observed and finite four-level paths. -/
+theorem shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_target
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    (shiftedSemanticObservedCyclicFourPath hcore z 1).1 =
+      (shiftedSemanticFinFourLevelPath hcore z 1).1 :=
+  congrArg Subtype.val
+    (shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
+      hcore z)
+
 /--
 The quotiented chart evaluation still lands on the original `q2` boundary.
 
@@ -2114,6 +2214,10 @@ The observed quotient path and the finite four-level path now have explicit
 source and target comparison theorems. A local `Path.cast` pointwise helper
 and an edge-zero evaluation wrapper prepare the later full comparison without
 forcing `Path.trans` interval-splitting normalization yet.
+The source/target comparison is also exposed after `Subtype.val`. A single
+observed quotient edge is packaged as a fixed-boundary path and proved equal
+to the direct finite fixed-boundary edge path, so the remaining four-edge
+comparison is only nested path-packaging normalization.
 
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index db349515..c17d123d 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -509,7 +509,12 @@ shiftedCyclicFourPath_source
 shiftedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_edgePath
 shiftedPath_cast_apply
+shiftedPath_trans_apply_source
+shiftedPath_trans_apply_target
 shiftedSemanticCyclicChartEval_edgePath_zero
+shiftedSemanticObservedCyclicEdgePath
+shiftedSemanticObservedCyclicEdgePath_apply
+shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
 shiftedSemanticObservedCyclicFourPath
 shiftedSemanticObservedCyclicFourPath_source
 shiftedSemanticObservedCyclicFourPath_target
@@ -517,6 +522,8 @@ shiftedSemanticCyclicChartEval_left_zero
 shiftedSemanticObservedCyclicFourPath_q2
 shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
 shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
+shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_source
+shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_target
 shiftedSemanticCyclicChartEval_q2
 ```
 
@@ -697,17 +704,41 @@ shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
 ```
 
 A small pointwise `Path.cast` helper records that endpoint-type casts do not
-change path values, and the edge-zero wrapper specializes the local quotient
-edge evaluation theorem to the first finite edge:
+change path values. Source and target helpers for `Path.trans` record the
+endpoint behavior of path concatenation, and the edge-zero wrapper specializes
+the local quotient edge evaluation theorem to the first finite edge:
 
 ```text
 shiftedPath_cast_apply
+shiftedPath_trans_apply_source
+shiftedPath_trans_apply_target
 shiftedSemanticCyclicChartEval_edgePath_zero
 ```
 
-These facts keep the comparison pre-geometric. They prepare the full
-`Path.trans` normalization step without asserting any circle, angle, arc, or
-Euclidean one-eighth reading.
+The edge-local bridge is now stronger than an endpoint comparison. A single
+quotient edge observed through the descended semantic evaluation is packaged
+as a fixed-boundary path and proved equal to the direct finite fixed-boundary
+edge path:
+
+```text
+shiftedSemanticObservedCyclicEdgePath
+shiftedSemanticObservedCyclicEdgePath_apply
+shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
+```
+
+Value-level source and target comparisons are also available for the closed
+four-edge paths:
+
+```text
+shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_source
+shiftedSemanticObservedCyclicFourPath_val_eq_finFourLevelPath_val_at_target
+```
+
+These facts keep the comparison pre-geometric. The remaining obstruction is
+not semantic: each local edge comparison is available. The remaining task is
+normalizing the nested `Path.trans` and endpoint `Path.cast` structure used by
+the two closed four-path packages, without asserting any circle, angle, arc,
+or Euclidean one-eighth reading.
 
 The full comparison between evaluation of `shiftedCyclicFourPath` and the
 existing fixed-`q2` four-level path is intentionally left as a TODO because it
````
`````
