# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 40ec84496c29cc59d26d498516b48993a87332dd

## Report

進めました。今回の 124 は full path equality までは押し込まず、比較準備を Lean が通る形で確立しています。

変更点:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedPath_cast_apply`
  - `shiftedSemanticCyclicChartEval_edgePath_zero`
  - `shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source`
  - `shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target`
  - 実装済みタグ `[IMPLEMENTED: semantic-cf2d/shifted-cyclic-path-compare-prep]` を追加

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
  - 公開入口の説明に、観測 quotient path と finite four-level path の endpoint 比較が入ったことを追記

- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)
  - theorem 一覧と設計説明を更新
  - full comparison は `Path.trans` 正規化後の TODO として維持

確認:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift` 成功
- `lake build DkMath.Analysis.DkReal` 成功
- `git diff --check` 成功

## Review

うむ、今回も **採用でよい**。
今回の 124 は「full path equality を無理に押し込まず、比較準備を固めた」差分じゃ。判断として正しい。`shiftedPath_cast_apply`、edge-zero wrapper、source / target 比較 theorem が入り、TODO の本質がかなり絞られた。

## 1. 状況分析

今回追加された主なものはこれじゃ。

```text id="wilul1"
shiftedPath_cast_apply
shiftedSemanticCyclicChartEval_edgePath_zero
shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
```

いまの構図はこう。

```text id="extnxl"
quotient chart path:
  shiftedCyclicFourPath

observed quotient path:
  shiftedSemanticObservedCyclicFourPath

fixed-boundary direct path:
  shiftedSemanticFinFourLevelPath

local edge comparison:
  already available

source / target comparison:
  now available

remaining:
  interior parameterization comparison
```

つまり、端点は一致した。
局所 edge の評価も一致している。
残るのは、四本連結された `Path.trans` の内部パラメータを、どう既存の four-level path と同期させるかじゃ。

## 2. レビュー

今回の止め方は良い。

特に、full equality を無理に通さなかったのが正解じゃ。
`Path.trans` は単なるリスト結合ではなく、`unitInterval` の時間パラメータを折り畳む。四本を連結すると、Lean の内部では入れ子の時間分割になる。

```text id="o3i8s6"
first trans:
  first half / second half

nested trans:
  quarter-like nested subdivision

casts:
  endpoint type alignment
```

だから、いきなり

```lean id="x2fq9a"
shiftedSemanticObservedCyclicFourPath hcore z =
  shiftedSemanticFinFourLevelPath hcore z
```

を狙うと、`Path.trans` の評価展開と `Path.cast` の除去が同時に出てくる。
これは Lean 的にはやや重い。

今回 `shiftedPath_cast_apply` を先に置いたのはよい。
これで endpoint cast は「点ごとの値を変えない」と切り離せる。

## 3. 今回の本丸

一番重要なのは source / target 比較じゃ。

```lean id="xut5bw"
theorem shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
```

```lean id="rpb259"
theorem shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
```

これで、二つの closed path は少なくとも同じ始点・終点を持つことが明示された。

数学的には、

```text id="uoynmr"
observed quotient path:
  quotient traversal を semantic boundary へ写したもの

finite four-level path:
  semantic boundary 側で直接四本を連結したもの
```

この二つが同じ閉路を見ている、という主張の端点部分が固まった。

## 4. TODO の正体

残っている TODO は、数学的な不一致ではなく、ほぼ path packaging の正規化問題じゃ。

比較したいものはこれ。

```lean id="b03rw2"
shiftedSemanticObservedCyclicFourPath hcore z
```

と

```lean id="x7jqne"
shiftedSemanticFinFourLevelPath hcore z
```

この二つは、どちらも四本の edge を同じ seam でつないだ closed fixed-boundary path のはずじゃ。

ただし作り方が違う。

```text id="p39a8c"
route A:
  quotient chart four-path を作る
  evaluation で fixed-boundary path に写す

route B:
  fixed-boundary finite edge path を直接 four-path にする
```

各 edge ではすでに一致している。
端点でも一致した。
残りは、`Path.trans` の時間分割が両者で同じ形に展開できるか、という問題じゃ。

## 5. 次の方針

次は full equality に再挑戦する前に、`Path.trans` の観測補題を作るのが良い。

欲しいのはこういう補題じゃ。

```text id="kb4z4u"
Path.cast:
  pointwise value does not change

Path.trans:
  source and target are readable

Path.trans left branch:
  first segment is first path

Path.trans right branch:
  second segment is second path

nested trans:
  four-path の first edge / second edge / third edge / fourth edge を読む
```

ただし、`Path.trans` の中間時刻の具体式は Mathlib の定義に依存する。
だから最初は、全 \(t\) ではなく、**分割点だけ** を狙うのが安全じゃ。

たとえば、

```text id="y4j1rs"
t = 0
t = 1
t = middle
```

のような点評価から始める。

## 6. 次の勝利条件

次の checkpoint は、full equality ではなく、次の小成果でよい。

```text id="b6ep6b"
1:
  Path.trans / Path.cast の既存 simp theorem を確認する

2:
  shiftedPath_cast_apply を使う theorem を一つ増やす

3:
  observed path と finite four-level path の edge-zero 側比較を少し進める

4:
  full equality が難しければ、障害を docs に明記する
```

特に、次は `edgePath_zero` を活かして、observed four-path の最初の構成要素と finite edge zero の関係を試すのがよい。

ただし、`Path.trans` の内部 parameter が面倒なら、無理しない。

## 7. 結論

今回の差分は採用でよい。

```text id="w1bc3i"
実装:
  良い。比較準備として必要な cast helper、edge-zero wrapper、source/target 比較が入った。

数学:
  良い。二つの closed fixed-boundary path の端点一致が確立した。

設計:
  良い。full path equality は Path.trans 正規化待ちとして残している。

次:
  Path.trans の評価正規化補題、または first segment 比較に進む。
```

ぬしよ、ここは焦らなくてよい。
もう「同じものを見ている」ことは端点と局所 edge でかなり見えている。残りは Lean の path 連結機構をどうほどくか、という技術戦じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index ca06207f..7919f444 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -221,7 +221,10 @@ four-edge quotient path are packaged in the glued chart space, and evaluating
 one quotient edge recovers the corresponding fixed-`q2` finite level edge.
 Observing the closed quotient path through the descended evaluation now gives
 a closed fixed-boundary path with source, target, endpoint, and `q2`
-observation aliases.
+observation aliases. The observed quotient path and the existing finite
+four-level path now have explicit source and target comparison theorems,
+together with a pointwise `Path.cast` helper and an edge-zero evaluation
+wrapper for the later full path comparison.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index e9e3dcc5..9b194e6d 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1895,6 +1895,34 @@ theorem shiftedSemanticCyclicChartEval_edgePath
     shiftedSemanticCyclicChartEval_mk]
   rfl
 
+/--
+Applying a casted path does not change its pointwise value.
+
+This local helper isolates the endpoint-type bookkeeping used when quotient
+seams are inserted into `Path.trans` chains.
+-/
+theorem shiftedPath_cast_apply
+    {α : Type _} [TopologicalSpace α]
+    {a b c d : α}
+    (p : Path a b) (hac : c = a) (hbd : d = b)
+    (t : unitInterval) :
+    (p.cast hac hbd) t = p t := rfl
+
+/--
+Edge-zero specialization of quotient-edge evaluation.
+
+This is the first local comparison needed before normalizing the full
+four-edge `Path.trans` chain.
+-/
+theorem shiftedSemanticCyclicChartEval_edgePath_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : unitInterval) :
+    shiftedSemanticCyclicChartEval hcore z
+      (shiftedCyclicChartEdgePath (0 : Fin 4) t) =
+        shiftedSemanticFinLevelEdge hcore z (0 : Fin 4) t :=
+  shiftedSemanticCyclicChartEval_edgePath hcore z (0 : Fin 4) t
+
 /--
 The closed quotient chart path observed inside the fixed square-mass boundary.
 
@@ -1963,6 +1991,42 @@ theorem shiftedSemanticObservedCyclicFourPath_q2
       Vec.q2 z :=
   (shiftedSemanticObservedCyclicFourPath hcore z t).2
 
+/--
+The observed quotient traversal and the finite four-level path have the same
+source value.
+
+This does not identify the whole paths yet; it records that both constructions
+start at the same fixed-boundary semantic state.
+-/
+theorem shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticObservedCyclicFourPath hcore z 0 =
+      shiftedSemanticFinFourLevelPath hcore z 0 := by
+  rw [shiftedSemanticObservedCyclicFourPath_source,
+    shiftedSemanticCyclicChartEval_left_zero,
+    shiftedSemanticFinFourLevelPath_source]
+  rfl
+
+/--
+The observed quotient traversal and the finite four-level path have the same
+target value.
+
+Both paths close at the initial fixed-boundary semantic state; later full path
+comparison can focus only on the interior `Path.trans` parameterization.
+-/
+theorem shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticObservedCyclicFourPath hcore z 1 =
+      shiftedSemanticFinFourLevelPath hcore z 1 := by
+  rw [shiftedSemanticObservedCyclicFourPath_target,
+    shiftedSemanticCyclicChartEval_left_zero,
+    shiftedSemanticFinFourLevelPath_target]
+  rfl
+
 /--
 The quotiented chart evaluation still lands on the original `q2` boundary.
 
@@ -2045,6 +2109,12 @@ The closed quotient path is observed through the descended semantic
 evaluation as a fixed-`q2` path. Source, target, endpoint-evaluation, and
 boundary-observation aliases are exposed.
 
+[IMPLEMENTED: semantic-cf2d/shifted-cyclic-path-compare-prep]
+The observed quotient path and the finite four-level path now have explicit
+source and target comparison theorems. A local `Path.cast` pointwise helper
+and an edge-zero evaluation wrapper prepare the later full comparison without
+forcing `Path.trans` interval-splitting normalization yet.
+
 [TODO: semantic-cf2d/shifted-cyclic-path-eval]
 Compare evaluation of the closed quotient path with the fixed-`q2` four-level
 path after path-trans cast normalization lemmas are available.
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index d562f3c3..db349515 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -508,11 +508,15 @@ shiftedCyclicFourPath
 shiftedCyclicFourPath_source
 shiftedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_edgePath
+shiftedPath_cast_apply
+shiftedSemanticCyclicChartEval_edgePath_zero
 shiftedSemanticObservedCyclicFourPath
 shiftedSemanticObservedCyclicFourPath_source
 shiftedSemanticObservedCyclicFourPath_target
 shiftedSemanticCyclicChartEval_left_zero
 shiftedSemanticObservedCyclicFourPath_q2
+shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
+shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
 shiftedSemanticCyclicChartEval_q2
 ```
 
@@ -683,6 +687,28 @@ Thus the quotient traversal is already connected to a fixed-boundary
 observation path, even before comparing the whole concatenated path with the
 existing finite four-level path.
 
+The first comparison layer is now also formalized. The observed quotient path
+and the existing finite four-level path are proved to agree at their source
+and target values:
+
+```text
+shiftedSemanticObservedCyclicFourPath_source_eq_finFourLevelPath_source
+shiftedSemanticObservedCyclicFourPath_target_eq_finFourLevelPath_target
+```
+
+A small pointwise `Path.cast` helper records that endpoint-type casts do not
+change path values, and the edge-zero wrapper specializes the local quotient
+edge evaluation theorem to the first finite edge:
+
+```text
+shiftedPath_cast_apply
+shiftedSemanticCyclicChartEval_edgePath_zero
+```
+
+These facts keep the comparison pre-geometric. They prepare the full
+`Path.trans` normalization step without asserting any circle, angle, arc, or
+Euclidean one-eighth reading.
+
 The full comparison between evaluation of `shiftedCyclicFourPath` and the
 existing fixed-`q2` four-level path is intentionally left as a TODO because it
 requires path-trans cast normalization lemmas. This is still not a Euclidean
````
`````
