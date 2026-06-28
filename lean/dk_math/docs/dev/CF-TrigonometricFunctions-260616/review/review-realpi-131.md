# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 45d0e58fb541ccd83d44cbbc11036bcdd154975d

## Report

進めました。130 では Mathlib 側の `Path.map` API を調査し、使える部品を DkMath 側に固定しました。

追加した Lean API:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedPath_map_cast`
  - `shiftedPath_map_trans`

調査結果:

- Mathlib には既に `Path.map` と `Path.map_trans` がありました。
- 不足していた `Path.map` と `Path.cast` の互換性を `shiftedPath_map_cast` として追加しました。
- `shiftedPath_map_trans` は Mathlib の `Path.map_trans` を DkMath 名で包んだ wrapper です。

four-concat full bridge も実験しましたが、最後は seam proof alignment が残りました。つまり、部品としての `map_trans` / `map_cast` は揃いましたが、`shiftedFourPathConcatWithSeams` 全体に map を通すには、4 本の seam equality が mapping 後に finite seam equality と一致することを整理する補題が次の焦点です。

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
130 はかなり重要な土台整備じゃ。Mathlib に `Path.map` と `Path.map_trans` があることを確認し、DkMath 側では不足していた `Path.map` と `Path.cast` の互換性を `shiftedPath_map_cast` として固定できた。これで、残る問題はかなり具体的に **seam proof alignment** へ絞られた。

## 状況分析

今回追加された API はこの二つじゃ。

```text id="b4wqmu"
shiftedPath_map_cast
shiftedPath_map_trans
```

意味としてはこう。

```text id="q578c7"
shiftedPath_map_cast:
  endpoint cast してから map する
  と
  map してから endpoint cast する
  が一致する

shiftedPath_map_trans:
  trans してから map する
  と
  map してから trans する
  が一致する
```

これで、前回まで残っていた大きな問題、

```text id="x7676k"
semantic evaluation of nested Path.trans / Path.cast

nested Path.trans / Path.cast of semantic edge evaluations
```

に対して、主要な分解部品は揃った。

ただし、four-concat 全体ではまだ最後に seam equality の対応が残る。
これは自然な止まり方じゃ。

## レビュー

実装判断は良い。

特に、`shiftedPath_map_trans` を Mathlib の `Path.map_trans` の wrapper として置いたのは正しい。DkMath 側の theorem 名で呼べるので、今後の phase-shift package 内で読みやすくなる。

また、`shiftedPath_map_cast` は今回の文脈にかなり効く。
`shiftedFourPathConcatWithSeams` は endpoint seam を `Path.cast` で処理しているため、map 後の endpoint がどう relabel されるかが問題になる。ここを補題化したのは良い。

現在の obstruction はこうじゃ。

```text id="mytd91"
quotient seam equality:
  shiftedCyclicChartRight i = shiftedCyclicChartLeft (succ i)

map 後の seam equality:
  semantic evaluation of right endpoint
  =
  semantic evaluation of successor left endpoint

finite seam equality:
  shiftedSemanticFinRightLevelEndpoint i
  =
  shiftedSemanticFinLeftLevelEndpoint (succ i)
```

Lean が欲しがっているのは、この三者の alignment じゃな。

## TODO の意味

残る TODO は、もはや `Path.map` でも `Path.trans` でも `Path.cast` でもない。
それらは今回で部品が揃った。

残るのは、map 後に発生する seam proof が、既存の finite seam proof と同じ endpoint equality として使えるかどうかじゃ。

つまり、次に必要なのはこういう補題じゃ。

```text id="qqxs1a"
semantic evaluation maps quotient seam equality
to finite level seam equality
```

より具体的には、

```text id="gbicfl"
map of shiftedCyclicChartRight_zero_eq_one_left
  corresponds to
shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left
```

同じものが `0→1`, `1→2`, `2→3`, `3→0` の四本ぶん必要になる。

## 次の方針

次は、いきなり four-concat compatibility を押すより、まず seam alignment theorem を四本作るのがよい。

すでに endpoint evaluation theorem はあるはずじゃ。

```text id="slbjtm"
shiftedSemanticCyclicChartEval_left
shiftedSemanticCyclicChartEval_right
shiftedSemanticCyclicChartEval_right_eq_succ_left
```

これらを使って、map 後の seam を finite seam theorem に寄せる。

この層が通れば、次に

```text id="vlbwxd"
map of shiftedFourPathConcatWithSeams
  =
shiftedFourPathConcatWithSeams of mapped edges
```

がかなり現実的になる。

## 一歩先ゆくおまけ実験

一歩先の実験としては、四本個別の seam alignment だけでなく、`Fin 4` 一般形で書けるかを試す価値がある。

候補の意味はこうじゃ。

```text id="i6nsdy"
for any i : Fin 4,
semantic evaluation maps
  right endpoint of quotient edge i
to
  finite right endpoint i,

and maps
  left endpoint of quotient edge succ i
to
  finite left endpoint succ i.
```

すでに `shiftedSemanticCyclicChartEval_right_eq_succ_left` があるなら、一般形で seam compatibility が出せる可能性がある。

ただし、四本の concrete seam theorem が今後の concat に必要なら、一般形にこだわりすぎず、まず concrete four theorem を作るのが安全じゃ。

## 結論

130 は採用でよい。

```text id="l4wknc"
実装:
  良い。Path.map_trans と Path.map_cast の互換性が DkMath 側に固定された。

数学:
  良い。残る問題が map/trans/cast ではなく seam proof alignment だと分離された。

設計:
  良い。four-concat full bridge を無理に押さず、次の焦点を明記している。

次:
  semantic evaluation が quotient seam equalities を finite seam equalities へ運ぶ補題を作る。
```

ぬしよ、ここはかなり良い詰めじゃ。
「貼ってから写す」と「写してから貼る」の大問題が、いよいよ「seam 証明の対応表」まで縮んだ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 15b1e6b9..2f4d672f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -236,9 +236,11 @@ path are definitionally equal to their canonical via-edge versions. The
 older observed closed path is also endpoint-cast to the finite left endpoint,
 with source, target, and apply aliases proving that only endpoint labels
 changed. The casted observed path also preserves the fixed-`q2` boundary.
-The remaining bridge is to commute descended semantic evaluation with the
-nested `Path.trans` and `Path.cast` structure of the canonical four-path
-concatenator for this endpoint-cast observed path.
+Mathlib's path-map/trans compatibility and a local path-map/cast compatibility
+theorem are now exposed for this package. The remaining bridge is to commute
+descended semantic evaluation with the nested `Path.trans` and `Path.cast`
+structure of the canonical four-path concatenator for this endpoint-cast
+observed path, including seam proof alignment after mapping.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index ac32ba6b..55294fc5 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1917,6 +1917,38 @@ theorem shiftedPath_cast_apply
     (t : unitInterval) :
     (p.cast hac hbd) t = p t := rfl
 
+/--
+Mapping a casted path is the same pointwise as casting the mapped path.
+
+Mathlib already provides `Path.map` and `Path.map_trans`; this is the local
+companion needed for endpoint bookkeeping in seam-glued path packages.
+-/
+theorem shiftedPath_map_cast
+    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
+    {a b c d : α}
+    (p : Path a b)
+    (f : α → β) (hf : Continuous f)
+    (hac : c = a) (hbd : d = b) :
+    (p.cast hac hbd).map hf =
+      (p.map hf).cast (by rw [hac]) (by rw [hbd]) := by
+  apply Path.ext
+  funext t
+  rfl
+
+/--
+Mapping a concatenated path agrees with concatenating the mapped paths.
+
+This is a DkMath-named wrapper around Mathlib's `Path.map_trans`, used to keep
+the phase-shift packaging API self-contained.
+-/
+theorem shiftedPath_map_trans
+    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
+    {a b c : α}
+    (p : Path a b) (q : Path b c)
+    (f : α → β) (hf : Continuous f) :
+    (p.trans q).map hf = (p.map hf).trans (q.map hf) :=
+  Path.map_trans p q hf
+
 /-- The source endpoint of a concatenated path is the source of the first path. -/
 theorem shiftedPath_trans_apply_source
     {α : Type _} [TopologicalSpace α]
@@ -2486,6 +2518,9 @@ The older observed closed path can now be endpoint-cast to the same finite
 endpoint type, with source, target, and pointwise apply aliases showing that
 only endpoint labels changed. Its fixed-`q2` boundary observation is preserved
 by the cast.
+Mathlib's `Path.map_trans` is exposed through a local wrapper, and a local
+`Path.map`/`Path.cast` compatibility theorem is available for the next
+packaging step.
 
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
@@ -2498,7 +2533,8 @@ descended semantic evaluation with the canonical four-path concatenator, after
 endpoint casting from the observed quotient-left endpoint to the finite left
 endpoint. The endpoint mismatch is solved; the remaining obstruction is the
 compatibility of descended semantic evaluation with the nested `Path.trans`
-and `Path.cast` structure of `shiftedFourPathConcatWithSeams`.
+and `Path.cast` structure of `shiftedFourPathConcatWithSeams`, including seam
+proof alignment after mapping.
 
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index ad3ca5f4..88a1f66c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -511,6 +511,8 @@ shiftedCyclicFourPath_source
 shiftedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_edgePath
 shiftedPath_cast_apply
+shiftedPath_map_cast
+shiftedPath_map_trans
 shiftedPath_trans_apply_source
 shiftedPath_trans_apply_target
 shiftedSemanticCyclicChartEval_edgePath_zero
@@ -719,12 +721,17 @@ shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
 ```
 
 A small pointwise `Path.cast` helper records that endpoint-type casts do not
-change path values. Source and target helpers for `Path.trans` record the
-endpoint behavior of path concatenation, and the edge-zero wrapper specializes
-the local quotient edge evaluation theorem to the first finite edge:
+change path values. Mathlib's path-map/trans compatibility is exposed through
+a local wrapper, and the local path-map/cast compatibility theorem handles
+endpoint relabelling under mapping. Source and target helpers for
+`Path.trans` record the endpoint behavior of path concatenation, and the
+edge-zero wrapper specializes the local quotient edge evaluation theorem to
+the first finite edge:
 
 ```text
 shiftedPath_cast_apply
+shiftedPath_map_cast
+shiftedPath_map_trans
 shiftedPath_trans_apply_source
 shiftedPath_trans_apply_target
 shiftedSemanticCyclicChartEval_edgePath_zero
@@ -830,7 +837,8 @@ nested Path.trans / Path.cast of semantic edge evaluations
 
 So the endpoint mismatch is solved. The remaining obstruction is the
 compatibility of descended semantic evaluation with the nested `Path.trans`
-and `Path.cast` structure of `shiftedFourPathConcatWithSeams`.
+and `Path.cast` structure of `shiftedFourPathConcatWithSeams`, including seam
+proof alignment after mapping.
 
 The full comparison between evaluation of `shiftedCyclicFourPath` and the
 existing fixed-`q2` four-level path is intentionally left as a TODO because it
````
`````
