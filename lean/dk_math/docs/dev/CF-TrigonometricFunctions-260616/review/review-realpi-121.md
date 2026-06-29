# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: f64638e6df2e2db51c87707e122073996b62efa5

## Report

実装完了です。`ShiftedCyclicChart` の代表元 API を強化しました。

追加した主なもの:

- `shiftedCyclicChartMk`
- `shiftedCyclicChartLeft`
- `shiftedCyclicChartRight`
- `shiftedCyclicChartRight_eq_succ_left`
- `shiftedCyclicChartRight_zero_eq_one_left` など 4 つの seam alias
- `shiftedSemanticCyclicChartEval_left`
- `shiftedSemanticCyclicChartEval_right`
- `shiftedSemanticCyclicChartEval_right_eq_succ_left`

おまけとして、quotient seam equality と evaluation seam compatibility の対応が明確に読める形にしてあります。topology/path 構造は予定通り未着手で、TODO を「representative and seam-equality API が安定した後」に更新しました。

Docs も同期済みです。

確認済み:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功しています。

## Review

うむ、今回も **採用でよい**。
これは `ShiftedCyclicChart` が「ただ存在する quotient」から、「代表元・左右端点・seam equality・evaluation が読める quotient API」へ進んだ差分じゃ。`shiftedCyclicChartLeft` / `Right`、quotient 内の seam equality、endpoint evaluation theorem、そして evaluation seam compatibility まで揃っている。topology/path 構造にはまだ進まず、代数的 quotient の可読 API を固めた判断も良い。

## 1. 状況分析

今回追加された主な層はこれじゃ。

```text id="qv86xx"
shiftedCyclicChartMk
shiftedCyclicChartLeft
shiftedCyclicChartRight
shiftedCyclicChartRight_eq_succ_left
shiftedCyclicChartRight_zero_eq_one_left
shiftedCyclicChartRight_one_eq_two_left
shiftedCyclicChartRight_two_eq_three_left
shiftedCyclicChartRight_three_eq_zero_left
shiftedSemanticCyclicChartEval_left
shiftedSemanticCyclicChartEval_right
shiftedSemanticCyclicChartEval_right_eq_succ_left
```

これで quotient の中で、

```text id="hwwmou"
edge i の右端点:
  edge succ i の左端点と同じ quotient point

evaluation:
  quotient endpoint representative から finite level endpoint へ戻る
```

と読めるようになった。

## 2. 今回の本丸

一番大事なのはこれじゃ。

```lean id="vu4cee"
theorem shiftedCyclicChartRight_eq_succ_left (i : Fin 4) :
    shiftedCyclicChartRight i =
      shiftedCyclicChartLeft (finFourSucc i)
```

これは、quotient の中で seam が本当に等式になっていることを言っている。

前回までは、finite chart の seam relation と evaluation compatibility だった。
今回は、quotient point 自体が貼り合わさった。

```text id="u1w1i3"
before:
  seam relation 上で evaluation が一致する

now:
  quotient 内で seam endpoints が同じ点になる
```

ここは大きい。

## 3. evaluation theorem も良い

次も良い。

```lean id="l78g5m"
shiftedSemanticCyclicChartEval_left
shiftedSemanticCyclicChartEval_right
```

これにより、quotient endpoint representative を評価すると、finite level endpoint に戻る。

つまり、quotient を使う側が representative を開かずに、

```text id="g7j5is"
left endpoint representative:
  finite left level endpoint を観測する

right endpoint representative:
  finite right level endpoint を観測する
```

と読める。

さらに、

```lean id="xth7o3"
shiftedSemanticCyclicChartEval_right_eq_succ_left
```

があるので、quotient seam equality と evaluation seam compatibility が対応している。
これは下流 API としてかなり使いやすい。

## 4. レビュー

実装判断は良い。

`Quot.sound` と `Relation.EqvGen.rel` を使い、生成 seam から quotient equality を作っている。
これは正攻法じゃ。

```text id="o9wvmz"
raw seam:
  shiftedFiniteSeamRel

generated equivalence:
  shiftedFiniteChartRel

quotient equality:
  shiftedCyclicChartRight_eq_succ_left
```

この順序がきれい。

docs も、representative constructor aliases、endpoint representatives、quotient seam equality、endpoint evaluation theorem が実装済みとして反映され、Remaining TODO は `shifted-cyclic-topology` に整理されている。

## 5. 次の本質

次はいよいよ topology/path に入れる段階じゃ。

ただし、いきなり大きい path theory を作るより、まずは quotient topology の最小 API を確認するのがよい。

狙う順序はこうじゃ。

```text id="q9xdr6"
first:
  ShiftedCyclicChart の quotient topology が使えるか確認する

second:
  representative map が continuous であることを確認する

third:
  shiftedSemanticCyclicChartEval が continuous か試す

fourth:
  できれば closed path との関係を薄く接続する
```

ここで無理に path object を作らなくてよい。
まずは continuity of evaluation じゃ。

## 6. 注意点

`ShiftedCyclicChart` は `Quot shiftedFiniteChartSetoid` なので、topology を載せるには Mathlib の quotient topology API に寄せる必要がある。

ここは Lean API 名が少し読みにくい可能性がある。
だから次の指示では「既存 API を調査して、通れば入れる。重ければ TODO で止める」がよい。

特に、`LevelSet` 側の topology、`unitInterval`、`Fin 4 × unitInterval`、`Quot` の topology がすべて噛み合う必要がある。

## 7. 賢狼のおまけ方針

おまけとして、次は「topology に挑む」だけでなく、失敗しても成果が残るようにしたい。

つまり、Codex にはこう言わせる。

```text id="m5faxl"
If topology works:
  continuous quotient evaluation を実装する

If topology is noisy:
  quotient topology design note と required missing lemma を残す

In either case:
  no Euclidean reading
```

これが省エネでよい。
Lean が通るなら進む。通らないなら、次の足場を docs に残す。

## 8. 結論

今回の差分は採用でよい。

```text id="iix3qj"
実装:
  良い。quotient representative API が整った。

数学:
  良い。seam relation が quotient equality として読める。

設計:
  良い。evaluation は quotient に降り、topology はまだ後段に残している。

次:
  quotient topology と continuous evaluation を試す。
```

ぬしよ、ここまで来ると checkpoint 104 はかなり育った。
四本の path から有限 chart、seam relation、quotient、代表元 API まで進んだ。
次は、いよいよ quotient を位相的に読む段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 03567132..0f8fc911 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -211,8 +211,11 @@ states are also packaged directly as points of the fixed square-mass level
 set. Finally, the finite chart layer evaluates `Fin 4 × unitInterval` into
 the same fixed boundary, closes the finite seam relation under
 `Relation.EqvGen`, packages the quotient as `ShiftedCyclicChart`, and
-descends chart evaluation to that quotient. Topology and path structure on
-the quotient are deliberately left to a later layer.
+descends chart evaluation to that quotient. Representative constructor
+aliases, left and right endpoint representatives, quotient seam equality, and
+endpoint evaluation theorems make the quotient readable without opening its
+representatives. Topology and path structure on the quotient are deliberately
+left to a later layer.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index e5254045..3bc1774d 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1608,6 +1608,60 @@ selected here.
 abbrev ShiftedCyclicChart :=
   Quot shiftedFiniteChartSetoid
 
+/-- Constructor alias for representatives of `ShiftedCyclicChart`. -/
+def shiftedCyclicChartMk (p : ShiftedFiniteChart) : ShiftedCyclicChart :=
+  Quot.mk shiftedFiniteChartSetoid p
+
+/-- The constructor alias is definitionally the quotient representative map. -/
+@[simp]
+theorem shiftedCyclicChartMk_eq_mk (p : ShiftedFiniteChart) :
+    shiftedCyclicChartMk p = Quot.mk shiftedFiniteChartSetoid p := rfl
+
+/-- Left endpoint representative of a finite shifted chart in the quotient. -/
+def shiftedCyclicChartLeft (i : Fin 4) : ShiftedCyclicChart :=
+  shiftedCyclicChartMk (i, (0 : unitInterval))
+
+/-- Right endpoint representative of a finite shifted chart in the quotient. -/
+def shiftedCyclicChartRight (i : Fin 4) : ShiftedCyclicChart :=
+  shiftedCyclicChartMk (i, (1 : unitInterval))
+
+/--
+The generating seam is an equality inside the shifted cyclic chart quotient.
+
+This is the quotient-side form of the finite seam law: the right endpoint of
+edge `i` and the left endpoint of its finite successor are the same cyclic
+chart point.
+-/
+theorem shiftedCyclicChartRight_eq_succ_left (i : Fin 4) :
+    shiftedCyclicChartRight i =
+      shiftedCyclicChartLeft (finFourSucc i) := by
+  apply Quot.sound
+  exact Relation.EqvGen.rel _ _ ⟨i, rfl, rfl⟩
+
+/-- The quotient seam sends finite edge `0` to finite edge `1`. -/
+theorem shiftedCyclicChartRight_zero_eq_one_left :
+    shiftedCyclicChartRight (0 : Fin 4) =
+      shiftedCyclicChartLeft (1 : Fin 4) := by
+  simpa using shiftedCyclicChartRight_eq_succ_left ⟨0, by norm_num⟩
+
+/-- The quotient seam sends finite edge `1` to finite edge `2`. -/
+theorem shiftedCyclicChartRight_one_eq_two_left :
+    shiftedCyclicChartRight (1 : Fin 4) =
+      shiftedCyclicChartLeft (2 : Fin 4) := by
+  simpa using shiftedCyclicChartRight_eq_succ_left ⟨1, by norm_num⟩
+
+/-- The quotient seam sends finite edge `2` to finite edge `3`. -/
+theorem shiftedCyclicChartRight_two_eq_three_left :
+    shiftedCyclicChartRight (2 : Fin 4) =
+      shiftedCyclicChartLeft (3 : Fin 4) := by
+  simpa using shiftedCyclicChartRight_eq_succ_left ⟨2, by norm_num⟩
+
+/-- The quotient seam sends finite edge `3` back to finite edge `0`. -/
+theorem shiftedCyclicChartRight_three_eq_zero_left :
+    shiftedCyclicChartRight (3 : Fin 4) =
+      shiftedCyclicChartLeft (0 : Fin 4) := by
+  simpa using shiftedCyclicChartRight_eq_succ_left ⟨3, by norm_num⟩
+
 /--
 Chart evaluation is compatible with the generated seam equivalence.
 
@@ -1662,6 +1716,42 @@ theorem shiftedSemanticCyclicChartEval_mk
     shiftedSemanticCyclicChartEval hcore z (Quot.mk _ p) =
       shiftedSemanticFinChartEval hcore z p := rfl
 
+/-- Quotient evaluation at a left endpoint representative. -/
+theorem shiftedSemanticCyclicChartEval_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartLeft i) =
+      shiftedSemanticFinLeftLevelEndpoint hcore z i := by
+  rw [shiftedCyclicChartLeft, shiftedCyclicChartMk_eq_mk,
+    shiftedSemanticCyclicChartEval_mk,
+    shiftedSemanticFinChartEval_at_left]
+
+/-- Quotient evaluation at a right endpoint representative. -/
+theorem shiftedSemanticCyclicChartEval_right
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartRight i) =
+      shiftedSemanticFinRightLevelEndpoint hcore z i := by
+  rw [shiftedCyclicChartRight, shiftedCyclicChartMk_eq_mk,
+    shiftedSemanticCyclicChartEval_mk,
+    shiftedSemanticFinChartEval_at_right]
+
+/--
+Quotient evaluation has matching values across the quotient seam.
+
+This is the evaluation-side reading of `shiftedCyclicChartRight_eq_succ_left`.
+-/
+theorem shiftedSemanticCyclicChartEval_right_eq_succ_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticCyclicChartEval hcore z (shiftedCyclicChartRight i) =
+      shiftedSemanticCyclicChartEval hcore z
+        (shiftedCyclicChartLeft (finFourSucc i)) := by
+  rw [shiftedCyclicChartRight_eq_succ_left]
+
 /--
 The quotiented chart evaluation still lands on the original `q2` boundary.
 
@@ -1723,10 +1813,13 @@ proved.
 The finite seam relation is closed under `Relation.EqvGen`, packaged as a
 setoid quotient `ShiftedCyclicChart`, and chart evaluation descends to the
 quotient as a fixed-`q2` boundary-valued function.
+Representative constructor aliases, left and right endpoint representatives,
+quotient seam equality, endpoint evaluation theorems, and quotient evaluation
+seam compatibility are also exposed.
 
 [TODO: semantic-cf2d/shifted-cyclic-topology]
-Add topology/path structure to the shifted cyclic chart quotient only after
-the quotient evaluation API is stable.
+Add topology/path structure to `ShiftedCyclicChart` after the quotient
+representative and seam-equality API is stable.
 -/
 
 /-!
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 92bad1f5..641aed69 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -481,9 +481,21 @@ shiftedSemanticFinChartEval_eq_of_seamRel
 shiftedFiniteChartRel
 shiftedFiniteChartSetoid
 ShiftedCyclicChart
+shiftedCyclicChartMk
+shiftedCyclicChartMk_eq_mk
+shiftedCyclicChartLeft
+shiftedCyclicChartRight
+shiftedCyclicChartRight_eq_succ_left
+shiftedCyclicChartRight_zero_eq_one_left
+shiftedCyclicChartRight_one_eq_two_left
+shiftedCyclicChartRight_two_eq_three_left
+shiftedCyclicChartRight_three_eq_zero_left
 shiftedSemanticFinChartEval_eq_of_chartRel
 shiftedSemanticCyclicChartEval
 shiftedSemanticCyclicChartEval_mk
+shiftedSemanticCyclicChartEval_left
+shiftedSemanticCyclicChartEval_right
+shiftedSemanticCyclicChartEval_right_eq_succ_left
 shiftedSemanticCyclicChartEval_q2
 ```
 
@@ -594,6 +606,21 @@ and `shiftedSemanticCyclicChartEval_q2` records that the descended value still
 lies on the original fixed boundary. This is only an algebraic seam quotient;
 no quotient topology or quotient path structure has been selected yet.
 
+The quotient representative API is now explicit. `shiftedCyclicChartMk` names
+the representative constructor, while `shiftedCyclicChartLeft` and
+`shiftedCyclicChartRight` name the endpoint representatives. Lean proves the
+quotient seam equality:
+
+```text
+shiftedCyclicChartRight i =
+  shiftedCyclicChartLeft (finFourSucc i)
+```
+
+and also exposes the four concrete seam aliases `0 -> 1`, `1 -> 2`,
+`2 -> 3`, and `3 -> 0`. Evaluation at quotient endpoint representatives
+computes back to the finite left and right level endpoints, and quotient
+evaluation is seam-compatible by rewriting through the quotient equality.
+
 Candidate theorem directions:
 
 ```text
@@ -678,8 +705,13 @@ depend on that reading.
 31. Implemented: package the generated relation as `ShiftedCyclicChart`.
 32. Implemented: descend chart evaluation to the quotient and expose its
     representative computation theorem.
-33. Later: add topology/path structure to the shifted cyclic chart quotient.
-34. Later: add a Euclidean bridge that reads `1/8` full-cycle
+33. Implemented: add quotient representative constructor aliases.
+34. Implemented: add quotient left/right endpoint representatives.
+35. Implemented: prove quotient seam equality and four finite seam aliases.
+36. Implemented: expose quotient evaluation at endpoint representatives and
+    quotient evaluation seam compatibility.
+37. Later: add topology/path structure to the shifted cyclic chart quotient.
+38. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -747,14 +779,17 @@ Close the finite seam relation under `Relation.EqvGen`, package it as the
 setoid quotient `ShiftedCyclicChart`, and descend chart evaluation to a
 fixed-`q2` boundary-valued quotient evaluation. The computation theorem on
 representatives and the descended `q2` observation are also exposed.
+Representative constructor aliases, endpoint representatives, quotient seam
+equality, concrete seam aliases, endpoint evaluation theorems, and quotient
+evaluation seam compatibility are also exposed.
 ```
 
 ## Remaining TODO Tags
 
 ```text
 [TODO: semantic-cf2d/shifted-cyclic-topology]
-Add topology/path structure to the shifted cyclic chart quotient only after
-the quotient evaluation API is stable.
+Add topology/path structure to `ShiftedCyclicChart` after the quotient
+representative and seam-equality API is stable.
 
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
 After the algebraic shifted-frame theorem is closed at the semantic path
````
`````
