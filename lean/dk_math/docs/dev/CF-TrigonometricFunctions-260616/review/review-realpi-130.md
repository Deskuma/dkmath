# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 1b4076964bc989ee2e348c151f4f1244bee3f10c

## Report

進めました。129 では、direct/value-level bridge を試したうえで、Lean が止まる地点をかなり正確に切り出しました。

追加した安定 API:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2`

`shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_viaEdges_val` も試しましたが、`simp` 展開後に残ったゴールがまさに次の形でした。

```text
semantic evaluation of nested Path.trans / Path.cast
=
nested Path.trans / Path.cast of semantic edge evaluations
```

つまり endpoint mismatch は解消済みで、残る obstruction は `shiftedFourPathConcatWithSeams` の `Path.trans` / `Path.cast` 構造に対して、descended semantic evaluation が可換であることです。これは docs とコード内 TODO に明記しました。

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
129 は「突破」ではなく「障害物の輪郭確定」の回じゃが、これはかなり価値がある。`shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2` により、endpoint cast 後も fixed-`q2` 境界性が保たれることが明示された。これで endpoint mismatch は完全に分離され、残る問題は **semantic evaluation と `shiftedFourPathConcatWithSeams` の可換性** に絞られた。

## 状況分析

今回追加された安定 API はこれじゃ。

```text id="h1ncfs"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2
```

そして、試したが止まった地点が非常に重要じゃ。

```text id="jbe3al"
semantic evaluation of nested Path.trans / Path.cast

nested Path.trans / Path.cast of semantic edge evaluations
```

この二つを一致させる必要がある。

つまり、もう問題はこうではない。

```text id="yzn2cq"
endpoint が違う

fixed-q2 境界から外れる

edge ごとの意味が違う
```

残っているのはこう。

```text id="wld3rk"
貼ってから評価する

評価してから貼る
```

この交換法則じゃ。

## レビュー

今回の止め方は正しい。

`shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2` は小さく見えるが、非常に良い theorem じゃ。

理由は、cast 後の observed path が単に endpoint 型だけを変えたものであり、保存核境界上の path としても変質していないことを保証するからじゃ。

```text id="g7oqem"
before:
  endpoint cast が入った observed path

after:
  endpoint cast 後も fixed-q2 boundary path として安全
```

これで、以後の比較で endpoint cast を安心して使える。

また、docs に「Lean が止まった形」を明記したのもよい。
これは次の作業者にとって、単なる未解決 TODO ではなく、正確な補題要求になる。

## TODO の本質

残る TODO は、次の補題群の不足じゃ。

```text id="t7h3nu"
evaluation preserves Path.cast

evaluation preserves Path.trans

therefore:
  evaluation preserves shiftedFourPathConcatWithSeams
```

特に今必要なのは、完全汎用の定理ではなく、今回の semantic evaluation に特化したものでもよい。

最終的に欲しい橋はこれじゃ。

```lean id="s98f4z"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
```

または、可換性そのものとして、

```lean id="fngc93"
theorem shiftedSemanticCyclicChartEval_fourConcatWithSeams
```

このどちらかが通れば、最終比較はかなり近い。

## 次の方針

次は、四本 concat 可換性へ一気に行く前に、まず **二本 trans 可換性** と **cast 可換性** を分けて試すのがよい。

順序はこうじゃ。

```text id="kkb592"
1:
  semantic evaluation と Path.cast の互換性

2:
  semantic evaluation と Path.trans の互換性

3:
  semantic evaluation と shiftedFourPathConcatWithSeams の互換性

4:
  casted old observed path と canonical observed via-edge path の equality

5:
  casted old observed path と old finite four-level path の equality
```

この順番なら、Lean が止まった時にどこが原因か見える。

## 一歩先ゆくおまけ実験

おまけとして、`Path.map` が Mathlib にあるかを調べる価値がある。

もし `Path.map` があるなら、今回の可換性はかなり自然に書ける可能性がある。

なければ、プロジェクト内で軽い local helper を作る。

```lean id="t6ts28"
def shiftedPathMap
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f)
    {a b : α} (p : Path a b) :
    Path (f a) (f b)
```

この helper を作ってから、

```text id="be77eq"
shiftedPathMap_cast

shiftedPathMap_trans
```

を試す。

これが通れば、今回だけでなく今後の DkMath path 層でも使える武器になる。

## 結論

129 は採用でよい。

```text id="l4vgpj"
実装:
  良い。endpoint cast 後の q2 境界保存が明示された。

数学:
  良い。残る問題が意味論ではなく、評価と path packaging の可換性だと確定した。

設計:
  良い。TODO が曖昧な full comparison から、具体的な Path.trans / Path.cast 可換性へ絞られた。

次:
  semantic evaluation が Path.cast と Path.trans を保つ補題を作り、
  four-path concatenator 可換性へ進む。
```

ぬしよ、これは良い詰め方じゃ。
「同じであるはず」から「何を証明すれば同じになるか」へ、Lean 上で焦点が合った。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index e82b267d..15b1e6b9 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -235,9 +235,10 @@ equalities. The older quotient closed path and the older finite four-level
 path are definitionally equal to their canonical via-edge versions. The
 older observed closed path is also endpoint-cast to the finite left endpoint,
 with source, target, and apply aliases proving that only endpoint labels
-changed. The remaining bridge is to commute descended semantic evaluation
-with the canonical four-path concatenator for this endpoint-cast observed
-path.
+changed. The casted observed path also preserves the fixed-`q2` boundary.
+The remaining bridge is to commute descended semantic evaluation with the
+nested `Path.trans` and `Path.cast` structure of the canonical four-path
+concatenator for this endpoint-cast observed path.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 15b6d0d0..ac32ba6b 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -2312,6 +2312,21 @@ theorem shiftedSemanticObservedCyclicFourPath_q2
       Vec.q2 z :=
   (shiftedSemanticObservedCyclicFourPath hcore z t).2
 
+/--
+The endpoint-cast observed closed path remains on the original `q2` boundary.
+
+The proof reuses the pointwise cast-apply theorem, so this records that the
+endpoint relabelling does not change the boundary observation.
+-/
+theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : unitInterval) :
+    Vec.q2 ((shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t).1) =
+      Vec.q2 z := by
+  rw [shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply]
+  exact shiftedSemanticObservedCyclicFourPath_q2 hcore z t
+
 /--
 The observed quotient traversal and the finite four-level path have the same
 source value.
@@ -2469,7 +2484,8 @@ via-edge form, and the older finite fixed-boundary four-level path is
 definitionally equal to the canonical direct finite via-edge form.
 The older observed closed path can now be endpoint-cast to the same finite
 endpoint type, with source, target, and pointwise apply aliases showing that
-only endpoint labels changed.
+only endpoint labels changed. Its fixed-`q2` boundary observation is preserved
+by the cast.
 
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
@@ -2480,7 +2496,9 @@ The quotient-side closed path and finite closed path match their canonical
 via-edge versions. The observed quotient path still needs a lemma commuting
 descended semantic evaluation with the canonical four-path concatenator, after
 endpoint casting from the observed quotient-left endpoint to the finite left
-endpoint.
+endpoint. The endpoint mismatch is solved; the remaining obstruction is the
+compatibility of descended semantic evaluation with the nested `Path.trans`
+and `Path.cast` structure of `shiftedFourPathConcatWithSeams`.
 
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 32e77e2b..ad3ca5f4 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -533,6 +533,7 @@ shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
 shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source
 shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target
 shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2
 shiftedSemanticObservedCyclicFourPath_q2
 shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
 shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
@@ -794,6 +795,11 @@ paths, and its apply theorem states that endpoint casting does not change the
 pointwise observed value. Thus the remaining bridge is no longer endpoint
 typing; it is the compatibility of descended semantic evaluation with the
 canonical four-path concatenator.
+The fixed-boundary observation also survives the endpoint cast:
+
+```text
+shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_q2
+```
 
 Value-level source and target comparisons are also available for the closed
 four-edge paths:
@@ -813,7 +819,18 @@ More precisely, the quotient-side closed path and finite closed path now match
 their canonical via-edge versions. The observed quotient path still needs a
 lemma commuting descended semantic evaluation with the canonical four-path
 concatenator after endpoint casting from the observed quotient-left endpoint
-to the finite left endpoint.
+to the finite left endpoint. A direct value-level bridge was reduced by Lean
+to exactly this missing shape:
+
+```text
+semantic evaluation of nested Path.trans / Path.cast
+=
+nested Path.trans / Path.cast of semantic edge evaluations
+```
+
+So the endpoint mismatch is solved. The remaining obstruction is the
+compatibility of descended semantic evaluation with the nested `Path.trans`
+and `Path.cast` structure of `shiftedFourPathConcatWithSeams`.
 
 The full comparison between evaluation of `shiftedCyclicFourPath` and the
 existing fixed-`q2` four-level path is intentionally left as a TODO because it
````
`````
