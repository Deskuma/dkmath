# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 6217ae04824ff29eeef56f2f0ecf28eaa7a42d33

## Report

完了しました。今回は Fin 4 API の補強に加えて、＋αで `finFourSucc_four_cycle` と finite seam sequence aliases まで入れました。

実装:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `finFourSucc_zero/one/two/three`
  - `finFourSucc_four_cycle`
  - `shiftedSemanticFinEdge_leftEndpoint/rightEndpoint`
  - `shiftedSemanticFinEdge_center_eq_succ_base_of_core_eq_zero`
  - level-set 版 center-to-successor-base theorem
  - `shiftedSemanticFourLevelPath_source/target`
  - finite seam aliases `0→1`, `1→2`, `2→3`, `3→0`
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) と [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) も同期済みです。

検証:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`
- `lake build DkMath.Analysis.DkReal`
- `git diff --check`

すべて通っています。continuous cyclic quotient はまだ作らず、有限 `Fin 4` cyclic skeleton の可読 API と observation API を固めました。

## Review

うむ、今回も **採用でよい**。
これはかなり良い補強じゃ。前回までで `Fin 4` wrapper はできていたが、今回はその可読 API がかなり整った。`finFourSucc` の小ステップ、四回 successor で戻る定理、finite edge の endpoint alias、center-to-successor-base、finite seam sequence、closed path の source / target alias まで入っている。報告どおり、continuous cyclic quotient にはまだ進まず、有限 `Fin 4` cyclic skeleton の観測 API を固めた段階じゃ。

## 1. 状況分析

今回で、`Fin 4` 層が「ただの wrapper」から「下流が読める有限周期 API」になった。

追加された主なものはこれじゃ。

```text id="j1mpec"
finFourSucc_zero
finFourSucc_one
finFourSucc_two
finFourSucc_three
finFourSucc_four_cycle

shiftedSemanticFinEdge_leftEndpoint
shiftedSemanticFinEdge_rightEndpoint
shiftedSemanticFinEdge_center_eq_succ_base_of_core_eq_zero

shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero

shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left
shiftedSemanticFinRightLevelEndpoint_one_eq_two_left
shiftedSemanticFinRightLevelEndpoint_two_eq_three_left
shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left

shiftedSemanticFourLevelPath_source
shiftedSemanticFourLevelPath_target
```

これで有限四状態の読みはかなり明確になった。

```text id="lglqgn"
0 -> 1
1 -> 2
2 -> 3
3 -> 0
```

この successor 構造が theorem 名として表に出たのは良い。

## 2. 今回の本丸

今回の本丸はこれじゃ。

```lean id="tenmcj"
theorem finFourSucc_four_cycle (i : Fin 4) :
    finFourSucc (finFourSucc (finFourSucc (finFourSucc i))) = i
```

これは小さいが、意味は大きい。

`Nat` index では、四歩戻りは theorem で扱う。
`Fin 4` index では、successor を四回適用すると型の中で戻る。

つまり、有限 cyclic skeleton が明示された。

これはまだ quotient phase ではない。
だが、quotient phase の前段としては十分に強い。

## 3. finite center-to-successor-base が良い

特に良いのはこれじゃ。

```lean id="flahcs"
theorem shiftedSemanticFinEdge_center_eq_succ_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinEdge r z i phaseCenter =
      shiftedSemanticFinBase r z (finFourSucc i)
```

これは、finite edge の中心が cyclic successor base に到達するという定理じゃ。

言葉にするとこう。

```text id="sc1zix"
edge i の中心:
  base (succ i)
```

これは非常に良い。
「端点だったものが中心になる」という構造が、`Fin 4` の successor として読めるようになった。

## 4. level-set 版も良い

level-set 版 center-to-successor-base も入っている。

```lean id="s41igx"
shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero
```

ここで fixed `q2` boundary 内でも、中心が successor base point へ到達することを言える。

これは後で cyclic quotient や observation API を作る時に効く。
`Vec ℝ` 側だけでなく、境界型の内部で語れるのが良い。

## 5. finite seam sequence aliases が良い

次も良い。

```text id="h8xk96"
shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left
shiftedSemanticFinRightLevelEndpoint_one_eq_two_left
shiftedSemanticFinRightLevelEndpoint_two_eq_three_left
shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left
```

これはやや冗長に見えるが、下流の proof では効く。

`fin_cases` で毎回展開しなくても、四つの seam が名前で読める。

```text id="l7n5qc"
edge 0 -> edge 1
edge 1 -> edge 2
edge 2 -> edge 3
edge 3 -> edge 0
```

この可読性は大事じゃ。

## 6. closed path source / target alias も良い

```lean id="dr42y3"
shiftedSemanticFourLevelPath_source
shiftedSemanticFourLevelPath_target
```

これも地味だが良い。

`Path.source` / `Path.target` を直接使えば済むとも言えるが、DkMath の public API としては名前付きの方が読みやすい。

特に後で documentation や theorem statement に出す時、

```text id="y0gk57"
closed shifted four-level path starts at the finite boundary point
closed shifted four-level path ends at the same finite boundary point
```

と説明しやすくなる。

## 7. レビュー

実装判断はかなり良い。

今回の方針は「continuous quotient へ行かず、有限 cyclic skeleton を固める」だった。
結果として、その方針通りに進んでいる。

docs も、`Fin 4` wrapper、successor small facts、four-cycle theorem、finite endpoint alias、center-to-successor-base、source/target alias まで反映されている。

これは checkpoint 104 の読解性をかなり上げている。

## 8. 気になる点

大きな問題はない。

一点だけ将来の整理として、`shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero` の target が `shiftedSemanticIndexedBaseLevelPoint r z (finFourSucc i).val` になっている。

これは正しいが、`Fin` API としては、いつか

```lean id="afhl3u"
shiftedSemanticFinBaseLevelPoint r z (finFourSucc i)
```

のような finite 版 base level point が欲しくなるかもしれぬ。

今は問題ない。
ただ、下流で finite API に寄せるなら、次に thin wrapper を足す価値がある。

## 9. 次の本質

次は、いよいよ `shifted-cyclic-quotient` に行ける段階ではある。

ただし、いきなり本格的な quotient type を作るより、まず **有限観測表** を完成させるとよい。

なぜなら、連続 quotient parameter を作る前に、有限四状態の観測点が完全に読めている方が安全だからじゃ。

次に欲しいのは、`Fin 4` 版の base level point と、finite closed path observation API。

```text id="pbtuub"
Fin base level point
Fin edge center level point
Fin successor base level point
closed path source/target in Fin wording
four finite seams as a named chain
```

これで有限骨格が完全に外部 API として読める。

その次に、continuous cyclic quotient を設計する。

## 10. 結論

今回の差分は採用でよい。

```text id="xrtjx9"
実装:
  良い。Fin 4 cyclic API がかなり読みやすくなった。

数学:
  良い。finite successor、four-cycle、center-to-successor-base が揃った。

設計:
  良い。continuous quotient に進まず、有限 skeleton の観測 API を固めている。

次:
  finite level-point wrapper と closed path observation API を整え、
  その後に cyclic quotient 設計へ進む。
```

ぬしよ、ここまで来ると checkpoint 104 はかなり太い。
「円」と言わず、「角度」と言わず、固定 `q2` 境界上の有限四状態閉路が Lean API として読める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index ef84e282..9948fb1c 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -203,7 +203,10 @@ fixed-`q2` path object; the closing seam is supplied by the core-zero
 four-step return law. The same finite cyclic layer is also exposed through
 `Fin 4` wrappers for bases, edges, level edges, and paths, with a finite
 successor seam law for downstream code that wants a bounded index rather than
-raw natural-number indices.
+raw natural-number indices. The finite successor has named small-step facts
+and a four-cycle law. Finite edges expose endpoint aliases and
+center-to-successor-base compatibility, and the closed shifted path exposes
+source and target aliases.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 70c0db6f..b99a8388 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1129,6 +1129,35 @@ def finFourSucc (i : Fin 4) : Fin 4 :=
 theorem finFourSucc_val (i : Fin 4) :
     (finFourSucc i).val = (i.val + 1) % 4 := rfl
 
+/-- The finite successor sends `0` to `1`. -/
+@[simp]
+theorem finFourSucc_zero :
+    finFourSucc ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩ := by
+  rfl
+
+/-- The finite successor sends `1` to `2`. -/
+@[simp]
+theorem finFourSucc_one :
+    finFourSucc ⟨1, by norm_num⟩ = ⟨2, by norm_num⟩ := by
+  rfl
+
+/-- The finite successor sends `2` to `3`. -/
+@[simp]
+theorem finFourSucc_two :
+    finFourSucc ⟨2, by norm_num⟩ = ⟨3, by norm_num⟩ := by
+  rfl
+
+/-- The finite successor sends `3` back to `0`. -/
+@[simp]
+theorem finFourSucc_three :
+    finFourSucc ⟨3, by norm_num⟩ = ⟨0, by norm_num⟩ := by
+  rfl
+
+/-- Applying the finite successor four times returns to the starting index. -/
+theorem finFourSucc_four_cycle (i : Fin 4) :
+    finFourSucc (finFourSucc (finFourSucc (finFourSucc i))) = i := by
+  fin_cases i <;> rfl
+
 /-- The shifted base state indexed by `Fin 4`. -/
 def shiftedSemanticFinBase
     (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) : Vec ℝ :=
@@ -1157,6 +1186,20 @@ theorem shiftedSemanticFinEdge_eq_indexed
     shiftedSemanticFinEdge r z i t =
       shiftedSemanticIndexedEdge r z i.val t := rfl
 
+/-- The finite shifted edge starts at its finite left endpoint. -/
+theorem shiftedSemanticFinEdge_leftEndpoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinEdge r z i 0 =
+      shiftedSemanticLeftEndpoint r (shiftedSemanticFinBase r z i) := by
+  simp [shiftedSemanticFinEdge, shiftedSemanticIndexedEdge]
+
+/-- The finite shifted edge ends at its finite right endpoint. -/
+theorem shiftedSemanticFinEdge_rightEndpoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinEdge r z i 1 =
+      shiftedSemanticRightEndpoint r (shiftedSemanticFinBase r z i) := by
+  simp [shiftedSemanticFinEdge, shiftedSemanticIndexedEdge]
+
 /-- The finite shifted edge stays on the original square-mass boundary. -/
 theorem shiftedSemanticFinEdge_q2_of_core_eq_zero
     {r : UnitKernel DkNNRealQ}
@@ -1176,6 +1219,25 @@ theorem shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero
       shiftedSemanticIndexedBase r z (i.val + 1) :=
   shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero hcore z i.val
 
+/-- The finite shifted edge center reaches the cyclic successor base. -/
+theorem shiftedSemanticFinEdge_center_eq_succ_base_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinEdge r z i phaseCenter =
+      shiftedSemanticFinBase r z (finFourSucc i) := by
+  fin_cases i
+  · exact shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨0, by norm_num⟩
+  · exact shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨1, by norm_num⟩
+  · exact shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨2, by norm_num⟩
+  · calc
+      shiftedSemanticFinEdge r z ⟨3, by norm_num⟩ phaseCenter =
+          shiftedSemanticIndexedBase r z (3 + 1) :=
+        shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨3, by norm_num⟩
+      _ = shiftedSemanticFinBase r z (finFourSucc ⟨3, by norm_num⟩) := by
+        norm_num
+        exact semanticAct_four_of_core_eq_zero hcore z
+
 /-- The finite shifted normalized edge as a path. -/
 def shiftedSemanticFinPath
     (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
@@ -1252,6 +1314,28 @@ theorem shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero
       shiftedSemanticIndexedBaseLevelPoint r z (i.val + 1) :=
   shiftedSemanticIndexedLevelEdge_center_eq_next_base_of_core_eq_zero hcore z i.val
 
+/-- The finite level edge center reaches the cyclic successor base point. -/
+theorem shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinLevelEdge hcore z i phaseCenter =
+      shiftedSemanticIndexedBaseLevelPoint r z (finFourSucc i).val := by
+  fin_cases i
+  · exact shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨0, by norm_num⟩
+  · exact shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨1, by norm_num⟩
+  · exact shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero hcore z ⟨2, by norm_num⟩
+  · apply Subtype.ext
+    calc
+      (shiftedSemanticFinLevelEdge hcore z ⟨3, by norm_num⟩ phaseCenter).1 =
+          shiftedSemanticIndexedBase r z (3 + 1) :=
+        congrArg Subtype.val
+          (shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero
+            hcore z ⟨3, by norm_num⟩)
+      _ = (shiftedSemanticIndexedBaseLevelPoint r z (finFourSucc ⟨3, by norm_num⟩).val).1 := by
+        norm_num
+        exact semanticAct_four_of_core_eq_zero hcore z
+
 /-- The finite shifted normalized edge as a fixed-boundary path. -/
 def shiftedSemanticFinLevelPath
     {r : UnitKernel DkNNRealQ}
@@ -1285,6 +1369,44 @@ theorem shiftedSemanticFinRightLevelEndpoint_eq_succ_left
   · exact shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 2
   · exact shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left hcore z
 
+/-- Finite seam compatibility from edge `0` to edge `1`. -/
+theorem shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinRightLevelEndpoint hcore z ⟨0, by norm_num⟩ =
+      shiftedSemanticFinLeftLevelEndpoint hcore z ⟨1, by norm_num⟩ :=
+  shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z ⟨0, by norm_num⟩
+
+/-- Finite seam compatibility from edge `1` to edge `2`. -/
+theorem shiftedSemanticFinRightLevelEndpoint_one_eq_two_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinRightLevelEndpoint hcore z ⟨1, by norm_num⟩ =
+      shiftedSemanticFinLeftLevelEndpoint hcore z ⟨2, by norm_num⟩ :=
+  shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z ⟨1, by norm_num⟩
+
+/-- Finite seam compatibility from edge `2` to edge `3`. -/
+theorem shiftedSemanticFinRightLevelEndpoint_two_eq_three_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinRightLevelEndpoint hcore z ⟨2, by norm_num⟩ =
+      shiftedSemanticFinLeftLevelEndpoint hcore z ⟨3, by norm_num⟩ :=
+  shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z ⟨2, by norm_num⟩
+
+/-- Finite seam compatibility from edge `3` back to edge `0`. -/
+theorem shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFinRightLevelEndpoint hcore z ⟨3, by norm_num⟩ =
+      shiftedSemanticFinLeftLevelEndpoint hcore z ⟨0, by norm_num⟩ :=
+  by
+    simpa using
+      shiftedSemanticFinRightLevelEndpoint_eq_succ_left hcore z ⟨3, by norm_num⟩
+
 /-- Finite-index alias for the closed four shifted level path. -/
 def shiftedSemanticFinFourLevelPath
     {r : UnitKernel DkNNRealQ}
@@ -1295,6 +1417,24 @@ def shiftedSemanticFinFourLevelPath
       (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0) :=
   shiftedSemanticFourLevelPath hcore z
 
+/-- Source endpoint of the closed shifted four-level path. -/
+theorem shiftedSemanticFourLevelPath_source
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFourLevelPath hcore z 0 =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 :=
+  (shiftedSemanticFourLevelPath hcore z).source
+
+/-- Target endpoint of the closed shifted four-level path. -/
+theorem shiftedSemanticFourLevelPath_target
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticFourLevelPath hcore z 1 =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 :=
+  (shiftedSemanticFourLevelPath hcore z).target
+
 /-!
 [IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
 The shifted semantic edge uses the normalized center states of neighboring
@@ -1322,7 +1462,10 @@ core-zero four-step return law, not any geometric angle reading.
 [IMPLEMENTED: semantic-cf2d/shifted-fin-four]
 The shifted indexed layer now has `Fin 4` wrappers for bases, edges, paths,
 fixed-`q2` level edges, and level paths. A finite cyclic successor records the
-four-state seam law without introducing a continuous quotient parameter.
+four-state seam law without introducing a continuous quotient parameter. The
+successor has named small-step facts and a four-cycle law, finite edges expose
+endpoint and center-to-successor facts, and the closed shifted path exposes
+source and target aliases.
 
 [TODO: semantic-cf2d/shifted-cyclic-quotient]
 Introduce a quotient phase parameter only after the four-edge closed path is
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 93d60b8b..bdb01c6b 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -441,15 +441,30 @@ shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left
 shiftedSemanticIndexedLevelEdge_add_four_of_core_eq_zero
 shiftedSemanticFourLevelPath
 finFourSucc
+finFourSucc_zero
+finFourSucc_one
+finFourSucc_two
+finFourSucc_three
+finFourSucc_four_cycle
 shiftedSemanticFinBase
 shiftedSemanticFinEdge
+shiftedSemanticFinEdge_leftEndpoint
+shiftedSemanticFinEdge_rightEndpoint
 shiftedSemanticFinEdge_q2_of_core_eq_zero
 shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero
+shiftedSemanticFinEdge_center_eq_succ_base_of_core_eq_zero
 shiftedSemanticFinPath
 shiftedSemanticFinLevelEdge
+shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero
 shiftedSemanticFinLevelPath
 shiftedSemanticFinRightLevelEndpoint_eq_succ_left
+shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left
+shiftedSemanticFinRightLevelEndpoint_one_eq_two_left
+shiftedSemanticFinRightLevelEndpoint_two_eq_three_left
+shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left
 shiftedSemanticFinFourLevelPath
+shiftedSemanticFourLevelPath_source
+shiftedSemanticFourLevelPath_target
 ```
 
 The shifted normalized edge starts at the left normalized center candidate,
@@ -515,7 +530,10 @@ right endpoint of finite edge i = left endpoint of finite edge (finFourSucc i)
 ```
 
 This is still a finite cyclic index, not a continuous quotient phase
-parameter.
+parameter. The successor has named values for `0 -> 1 -> 2 -> 3 -> 0` and a
+four-cycle theorem. Finite shifted edges also expose endpoint aliases and a
+center-to-successor-base theorem. The closed shifted four-level path exposes
+named source and target aliases for downstream observation code.
 
 Candidate theorem directions:
 
@@ -590,7 +608,10 @@ depend on that reading.
 20. Implemented: concatenate the four indexed shifted level paths into a closed fixed-`q2` path.
 21. Implemented: add `Fin 4` wrappers for shifted bases, edges, paths, level edges, and level paths.
 22. Implemented: prove the finite successor seam law on `Fin 4`.
-23. Later: add a Euclidean bridge that reads `1/8` full-cycle
+23. Implemented: add small-step and four-cycle API for `finFourSucc`.
+24. Implemented: add finite endpoint aliases and center-to-successor-base compatibility.
+25. Implemented: add source and target aliases for the closed shifted four-level path.
+26. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -638,7 +659,10 @@ shifted normalized level paths into one closed fixed-`q2` path object.
 [IMPLEMENTED: semantic-cf2d/shifted-fin-four]
 Expose the shifted cyclic index through `Fin 4` wrappers for bases, edges,
 paths, fixed-`q2` level edges, and fixed-`q2` level paths. Add a finite
-successor and prove the corresponding cyclic seam law.
+successor and prove the corresponding cyclic seam law. The successor has
+named small-step facts and a four-cycle law, finite edges expose endpoint and
+center-to-successor-base compatibility, and the closed shifted path has named
+source and target aliases.
 ```
 
 ## Remaining TODO Tags
````
`````
