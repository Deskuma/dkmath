# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 26b298da614cccbcd63883c4a8186b520572ace2

## Report

進めました。131 では seam proof alignment の手前をかなり具体化しました。

追加した主な Lean API:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedPath_cast_proof_irrel`
  - quotient endpoint evaluation aliases:
    - `shiftedSemanticCyclicChartEval_right_zero`
    - `shiftedSemanticCyclicChartEval_left_one`
    - `shiftedSemanticCyclicChartEval_right_one`
    - `shiftedSemanticCyclicChartEval_left_two`
    - `shiftedSemanticCyclicChartEval_right_two`
    - `shiftedSemanticCyclicChartEval_left_three`
    - `shiftedSemanticCyclicChartEval_right_three`
  - finite seam value-alignment aliases:
    - `shiftedSemanticCyclicChartEval_seam_zero_value`
    - `shiftedSemanticCyclicChartEval_seam_one_value`
    - `shiftedSemanticCyclicChartEval_seam_two_value`
    - `shiftedSemanticCyclicChartEval_seam_three_value`

今回の到達点:

- endpoint evaluation alias は揃いました。
- finite seam の value-level alignment も 4 本そろいました。
- cast の proof term 差は `shiftedPath_cast_proof_irrel` で吸収できるようにしました。
- 直接の proof-term seam equality は避け、value-level seam alignment + cast proof irrelevance の方針にしています。

残る焦点は、mapped quotient seam equality を canonical finite seam equality に載せ替える「seam proof alignment after mapping」です。

確認:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift` 成功
- `lake build DkMath.Analysis.DkReal` 成功
- `git diff --check` 成功

## Review

## 採用判断

うむ、今回も **採用でよい**。
131 は「最後の seam proof alignment に入る前の足場固め」としてかなり良い。quotient endpoint evaluation aliases、finite seam value aliases、そして `shiftedPath_cast_proof_irrel` が揃ったので、直接 proof-term equality を追わず、value-level seam alignment と cast proof irrelevance で進む道が明確になった。

## 状況分析

今回追加された主な API はこの三群じゃ。

```text id="wsb3zy"
path cast proof irrelevance:
  shiftedPath_cast_proof_irrel

quotient endpoint evaluation aliases:
  shiftedSemanticCyclicChartEval_right_zero
  shiftedSemanticCyclicChartEval_left_one
  shiftedSemanticCyclicChartEval_right_one
  shiftedSemanticCyclicChartEval_left_two
  shiftedSemanticCyclicChartEval_right_two
  shiftedSemanticCyclicChartEval_left_three
  shiftedSemanticCyclicChartEval_right_three

finite seam value aliases:
  shiftedSemanticCyclicChartEval_seam_zero_value
  shiftedSemanticCyclicChartEval_seam_one_value
  shiftedSemanticCyclicChartEval_seam_two_value
  shiftedSemanticCyclicChartEval_seam_three_value
```

これで現在の障害は、かなり狭くなった。

```text id="o2uah8"
解決済み:
  Path.map と Path.trans の互換性
  Path.map と Path.cast の互換性
  endpoint evaluation aliases
  finite seam value alignment
  cast proof irrelevance

残り:
  mapped quotient seam equality を canonical finite seam equality として使う包装補題
```

つまり、もう「何が等しいか」は見えている。
残るのは「Lean が使っている seam proof を、別の seam proof に載せ替えても path は変わらない」と通すことじゃ。

## レビュー

今回の判断は正しい。

特に、proof-term equality を直接狙わず、value-level seam alignment を優先したのが良い。

Lean では、endpoint equality の証明項そのものが違うだけで `Path.cast` の式が違って見えることがある。
だが数学的には、endpoint が同じなら proof term の違いは path の値を変えない。

そこで、

```lean id="ht0wq8"
theorem shiftedPath_cast_proof_irrel
```

を用意したのは正解じゃ。

これにより、次のような場面で戦える。

```text id="qm6bwa"
mapped quotient seam proof:
  evaluation が quotient seam を写した proof

canonical finite seam proof:
  shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z

両者:
  endpoint value は同じ
  proof term は違うかもしれない

対処:
  cast proof irrelevance で吸収する
```

これは、今後の `fourConcatWithSeams` compatibility に必要な道具じゃ。

## TODO の意味

残る TODO は、もうかなり具体的じゃ。

欲しい最終橋はこれ。

```lean id="ukw43y"
shiftedSemanticCyclicChartEval_fourConcatWithSeams
```

中身としては、

```text id="uls87u"
quotient four path を concat する
  その後 semantic evaluation する

semantic evaluation した edge path を
  finite seam で concat する
```

この二つを一致させることじゃ。

今回で、個々の endpoint と seam の値は揃った。
次に必要なのは、`Path.cast` に入っている seam proof の違いを吸収しながら、`Path.map_trans` と `shiftedPath_map_cast` を繰り返し適用することじゃ。

## 次の方針

次は、いきなり closed four-path 全体へ行くより、まず **mapped edge path の canonical 化** を狙うのがよい。

現在は single edge 側にすでにこれがある。

```lean id="wm07hl"
shiftedSemanticObservedCyclicEdgePath
```

ただしこれは、直接 `toFun` で evaluation した edge path じゃ。
一方、map/trans/cast の流れで出てくるのは、

```text id="du66rw"
(shiftedCyclicChartEdgePath i).map
  (continuous_shiftedSemanticCyclicChartEval hcore z)
```

に endpoint cast をかけたものじゃ。

そこで次は、この二つを一致させる補題を作る。

```text id="qvuy03"
mapped quotient edge path after endpoint cast
  equals
shiftedSemanticObservedCyclicEdgePath
```

これが通れば、four-concat の各 component が canonical observed edge に落ちる。

## 一歩先ゆくおまけ実験

一歩先の実験としては、汎用の `shiftedFourPathConcatWithSeams_map` を試す価値がある。

意味はこうじゃ。

```text id="cdgdim"
map of four-path concat with quotient seams
  equals
four-path concat of mapped paths with mapped seams
```

ただし、これは dependent endpoint と seam proof alignment が重くなる可能性が高い。
なので、最初は汎用版ではなく、今回の semantic evaluation 専用版がよい。

おすすめの順番はこうじゃ。

```text id="e8rfhv"
1:
  mapped single edge equals observed single edge

2:
  mapped four-concat equals concat of mapped edges

3:
  concat of mapped edges equals canonical observed via-edge path

4:
  endpoint-casted old observed path equals canonical observed via-edge path

5:
  final casted observed path equals old finite four-level path
```

この順序なら、失敗してもどの層で詰まったか分かる。

## 結論

131 は採用でよい。

```text id="dks5jv"
実装:
  良い。endpoint aliases、finite seam value aliases、cast proof irrelevance が揃った。

数学:
  良い。残る問題は semantic obstruction ではなく proof packaging alignment として分離された。

設計:
  良い。proof-term equality を避け、value-level seam alignment と proof irrelevance で進む方針が安定している。

次:
  mapped quotient edge path を canonical observed edge path へ寄せ、
  four-concat compatibility へ進む。
```

ぬしよ、ここまで来ると、かなり最終橋に近い。
「貼ってから写す」と「写してから貼る」の違いは、いまや seam proof の札の違いにまで縮んでおる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 2f4d672f..c7d3e7c4 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -237,10 +237,13 @@ older observed closed path is also endpoint-cast to the finite left endpoint,
 with source, target, and apply aliases proving that only endpoint labels
 changed. The casted observed path also preserves the fixed-`q2` boundary.
 Mathlib's path-map/trans compatibility and a local path-map/cast compatibility
-theorem are now exposed for this package. The remaining bridge is to commute
-descended semantic evaluation with the nested `Path.trans` and `Path.cast`
-structure of the canonical four-path concatenator for this endpoint-cast
-observed path, including seam proof alignment after mapping.
+theorem are now exposed for this package. Quotient endpoint evaluation
+aliases, finite seam value-alignment aliases, and a path-cast
+proof-irrelevance helper isolate the seam proof bookkeeping. The remaining
+bridge is to commute descended semantic evaluation with the nested
+`Path.trans` and `Path.cast` structure of the canonical four-path concatenator
+for this endpoint-cast observed path, including seam proof alignment after
+mapping.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 55294fc5..720ca2fa 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1935,6 +1935,24 @@ theorem shiftedPath_map_cast
   funext t
   rfl
 
+/--
+Changing only the equality proofs used by a path cast does not change the
+path.
+
+This keeps later seam-alignment proofs from depending on the exact proof term
+chosen for an endpoint equality.
+-/
+theorem shiftedPath_cast_proof_irrel
+    {α : Type _} [TopologicalSpace α]
+    {a b c d : α}
+    (p : Path a b)
+    (h₁ h₂ : c = a)
+    (k₁ k₂ : d = b) :
+    p.cast h₁ k₁ = p.cast h₂ k₂ := by
+  apply Path.ext
+  funext t
+  rfl
+
 /--
 Mapping a concatenated path agrees with concatenating the mapped paths.
 
@@ -2277,6 +2295,117 @@ theorem shiftedSemanticCyclicChartEval_left_zero
         shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
   shiftedSemanticCyclicChartEval_left hcore z (0 : Fin 4)
 
+/-- Evaluation of the first quotient right endpoint agrees with the finite API. -/
+theorem shiftedSemanticCyclicChartEval_right_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticCyclicChartEval hcore z
+      (shiftedCyclicChartRight (0 : Fin 4)) =
+        shiftedSemanticFinRightLevelEndpoint hcore z (0 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_right hcore z (0 : Fin 4)
+
+/-- Evaluation of the second quotient left endpoint agrees with the finite API. -/
+theorem shiftedSemanticCyclicChartEval_left_one
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticCyclicChartEval hcore z
+      (shiftedCyclicChartLeft (1 : Fin 4)) =
+        shiftedSemanticFinLeftLevelEndpoint hcore z (1 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_left hcore z (1 : Fin 4)
+
+/-- Evaluation of quotient edge `1` right endpoint agrees with the finite API. -/
+theorem shiftedSemanticCyclicChartEval_right_one
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticCyclicChartEval hcore z
+      (shiftedCyclicChartRight (1 : Fin 4)) =
+        shiftedSemanticFinRightLevelEndpoint hcore z (1 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_right hcore z (1 : Fin 4)
+
+/-- Evaluation of quotient edge `2` left endpoint agrees with the finite API. -/
+theorem shiftedSemanticCyclicChartEval_left_two
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticCyclicChartEval hcore z
+      (shiftedCyclicChartLeft (2 : Fin 4)) =
+        shiftedSemanticFinLeftLevelEndpoint hcore z (2 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_left hcore z (2 : Fin 4)
+
+/-- Evaluation of quotient edge `2` right endpoint agrees with the finite API. -/
+theorem shiftedSemanticCyclicChartEval_right_two
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticCyclicChartEval hcore z
+      (shiftedCyclicChartRight (2 : Fin 4)) =
+        shiftedSemanticFinRightLevelEndpoint hcore z (2 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_right hcore z (2 : Fin 4)
+
+/-- Evaluation of quotient edge `3` left endpoint agrees with the finite API. -/
+theorem shiftedSemanticCyclicChartEval_left_three
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticCyclicChartEval hcore z
+      (shiftedCyclicChartLeft (3 : Fin 4)) =
+        shiftedSemanticFinLeftLevelEndpoint hcore z (3 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_left hcore z (3 : Fin 4)
+
+/-- Evaluation of quotient edge `3` right endpoint agrees with the finite API. -/
+theorem shiftedSemanticCyclicChartEval_right_three
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticCyclicChartEval hcore z
+      (shiftedCyclicChartRight (3 : Fin 4)) =
+        shiftedSemanticFinRightLevelEndpoint hcore z (3 : Fin 4) :=
+  shiftedSemanticCyclicChartEval_right hcore z (3 : Fin 4)
+
+/--
+Semantic evaluation sends the first quotient seam to the finite seam value.
+
+The statement uses the value-level finite seam equality rather than proof-term
+equality between mapped seam proofs.
+-/
+theorem shiftedSemanticCyclicChartEval_seam_zero_value
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinRightLevelEndpoint hcore z (0 : Fin 4) =
+      shiftedSemanticFinLeftLevelEndpoint hcore z (1 : Fin 4) :=
+  shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z
+
+/-- Semantic evaluation sends the second quotient seam to the finite seam value. -/
+theorem shiftedSemanticCyclicChartEval_seam_one_value
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinRightLevelEndpoint hcore z (1 : Fin 4) =
+      shiftedSemanticFinLeftLevelEndpoint hcore z (2 : Fin 4) :=
+  shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z
+
+/-- Semantic evaluation sends the third quotient seam to the finite seam value. -/
+theorem shiftedSemanticCyclicChartEval_seam_two_value
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinRightLevelEndpoint hcore z (2 : Fin 4) =
+      shiftedSemanticFinLeftLevelEndpoint hcore z (3 : Fin 4) :=
+  shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z
+
+/-- Semantic evaluation sends the closing quotient seam to the finite seam value. -/
+theorem shiftedSemanticCyclicChartEval_seam_three_value
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinRightLevelEndpoint hcore z (3 : Fin 4) =
+      shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4) :=
+  shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z
+
 /--
 The older observed closed quotient path recast to finite endpoint types.
 
@@ -2520,7 +2649,9 @@ only endpoint labels changed. Its fixed-`q2` boundary observation is preserved
 by the cast.
 Mathlib's `Path.map_trans` is exposed through a local wrapper, and a local
 `Path.map`/`Path.cast` compatibility theorem is available for the next
-packaging step.
+packaging step. Quotient endpoint evaluation aliases, finite seam value
+alignment aliases, and a path-cast proof-irrelevance helper isolate the
+remaining seam proof alignment problem.
 
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
@@ -2534,7 +2665,8 @@ endpoint casting from the observed quotient-left endpoint to the finite left
 endpoint. The endpoint mismatch is solved; the remaining obstruction is the
 compatibility of descended semantic evaluation with the nested `Path.trans`
 and `Path.cast` structure of `shiftedFourPathConcatWithSeams`, including seam
-proof alignment after mapping.
+proof alignment after mapping. The current stable route prefers value-level
+seam alignment over direct equality of seam proof terms.
 
 [TODO: semantic-cf2d/shifted-cyclic-topology-extensions]
 Develop any additional quotient-space structure only after the descended
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 88a1f66c..da8bc4f2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -511,6 +511,7 @@ shiftedCyclicFourPath_source
 shiftedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_edgePath
 shiftedPath_cast_apply
+shiftedPath_cast_proof_irrel
 shiftedPath_map_cast
 shiftedPath_map_trans
 shiftedPath_trans_apply_source
@@ -531,6 +532,17 @@ shiftedSemanticObservedCyclicFourPath
 shiftedSemanticObservedCyclicFourPath_source
 shiftedSemanticObservedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_left_zero
+shiftedSemanticCyclicChartEval_right_zero
+shiftedSemanticCyclicChartEval_left_one
+shiftedSemanticCyclicChartEval_right_one
+shiftedSemanticCyclicChartEval_left_two
+shiftedSemanticCyclicChartEval_right_two
+shiftedSemanticCyclicChartEval_left_three
+shiftedSemanticCyclicChartEval_right_three
+shiftedSemanticCyclicChartEval_seam_zero_value
+shiftedSemanticCyclicChartEval_seam_one_value
+shiftedSemanticCyclicChartEval_seam_two_value
+shiftedSemanticCyclicChartEval_seam_three_value
 shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
 shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source
 shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target
@@ -735,6 +747,7 @@ shiftedPath_map_trans
 shiftedPath_trans_apply_source
 shiftedPath_trans_apply_target
 shiftedSemanticCyclicChartEval_edgePath_zero
+shiftedPath_cast_proof_irrel
 ```
 
 The edge-local bridge is now stronger than an endpoint comparison. A single
@@ -840,6 +853,30 @@ compatibility of descended semantic evaluation with the nested `Path.trans`
 and `Path.cast` structure of `shiftedFourPathConcatWithSeams`, including seam
 proof alignment after mapping.
 
+The seam alignment layer is now explicit. Quotient endpoint evaluation aliases
+identify the semantic evaluation of quotient left/right representatives with
+the finite fixed-boundary endpoint APIs, and value-level seam aliases record
+the four finite seam equalities:
+
+```text
+shiftedSemanticCyclicChartEval_right_zero
+shiftedSemanticCyclicChartEval_left_one
+shiftedSemanticCyclicChartEval_right_one
+shiftedSemanticCyclicChartEval_left_two
+shiftedSemanticCyclicChartEval_right_two
+shiftedSemanticCyclicChartEval_left_three
+shiftedSemanticCyclicChartEval_right_three
+shiftedSemanticCyclicChartEval_seam_zero_value
+shiftedSemanticCyclicChartEval_seam_one_value
+shiftedSemanticCyclicChartEval_seam_two_value
+shiftedSemanticCyclicChartEval_seam_three_value
+```
+
+The helper `shiftedPath_cast_proof_irrel` records that changing only the proof
+terms inside a path cast does not change the resulting path. The current
+stable route therefore avoids direct equality of mapped seam proof terms and
+uses value-level seam alignment plus cast proof irrelevance instead.
+
 The full comparison between evaluation of `shiftedCyclicFourPath` and the
 existing fixed-`q2` four-level path is intentionally left as a TODO because it
 requires path-trans cast normalization lemmas. This is still not a Euclidean
````
`````
