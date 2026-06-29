# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: cc1c10e7a6dd1879734fae354d554bf220ca7321

## Report

完了しました。今回は指示内容の `Fin 4` wrapper に加えて、＋αで finite successor seam law まで通しました。

実装:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `finFourSucc`
  - `shiftedSemanticFinBase`
  - `shiftedSemanticFinEdge`
  - `shiftedSemanticFinPath`
  - `shiftedSemanticFinLevelEdge`
  - `shiftedSemanticFinLevelPath`
  - `shiftedSemanticFinEdge_q2_of_core_eq_zero`
  - `shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero`
  - `shiftedSemanticFinRightLevelEndpoint_eq_succ_left`
  - `shiftedSemanticFinFourLevelPath`
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) と [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) も同期済みです。

検証:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`
- `lake build DkMath.Analysis.DkReal`
- `git diff --check`

すべて通っています。今回も continuous quotient phase や Euclidean 読みには進めず、有限 `Fin 4` cyclic index として閉じました。

## Review

うむ、今回も **採用でよい**。
かなり良い流れじゃ。`Nat` index で固めた四状態 shifted path 層を、今度は `Fin 4` wrapper と finite successor seam law まで持ち上げている。つまり、まだ連続 quotient phase には行かず、有限四状態の cyclic index として安全に閉じた。報告でも、`finFourSucc`、`shiftedSemanticFinBase`、`shiftedSemanticFinEdge`、`shiftedSemanticFinLevelPath`、`shiftedSemanticFinRightLevelEndpoint_eq_succ_left`、`shiftedSemanticFinFourLevelPath` が追加され、検証も通っている。

## 1. 状況分析

今回で、shifted-frame route は次の段階まで来た。

```text id="wrmh0k"
Nat indexed layer:
  shiftedSemanticIndexedBase
  shiftedSemanticIndexedEdge
  shiftedSemanticIndexedLevelPath
  shiftedSemanticFourLevelPath

Fin 4 wrapper layer:
  finFourSucc
  shiftedSemanticFinBase
  shiftedSemanticFinEdge
  shiftedSemanticFinPath
  shiftedSemanticFinLevelEdge
  shiftedSemanticFinLevelPath
  shiftedSemanticFinFourLevelPath
```

これで、下位の source of truth は `Nat` indexed API のまま保ちつつ、下流コードには有限四状態 index を渡せるようになった。

これは良い設計じゃ。

```text id="vov73u"
Nat index:
  証明しやすい

Fin 4 index:
  使いやすい

continuous quotient:
  まだ入れない
```

この分離はかなり安全。

## 2. 今回の本丸

今回の中心は、有限 successor seam law じゃ。

```lean id="sjth74"
theorem shiftedSemanticFinRightLevelEndpoint_eq_succ_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinRightLevelEndpoint hcore z i =
      shiftedSemanticFinLeftLevelEndpoint hcore z (finFourSucc i)
```

これは、`Fin 4` の中で edge \(i\) の右端点が successor edge の左端点に一致する、という定理じゃ。

$$
\mathrm{rightEndpoint}(i)=\mathrm{leftEndpoint}(\mathrm{succ}(i))
$$

これで、四状態の接続関係が bounded index 上で読める。

`Nat` の \(k+1\) や \(k+4\) を意識せず、`Fin 4` の successor として読めるようになったのが大きい。

## 3. `finFourSucc` の位置づけが良い

```lean id="lzk3ze"
def finFourSucc (i : Fin 4) : Fin 4 :=
  ⟨(i.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩
```

これは、連続 quotient phase ではなく、有限四状態の successor じゃ。

ここが良い。

まだ `ℝ / ℤ` 的な quotient は要らない。
まずは `Fin 4` で十分。

```text id="bmcy6o"
今あるもの:
  finite cyclic successor

まだ入れないもの:
  continuous quotient phase parameter
```

この順序が正しい。

## 4. レビュー

実装判断は良い。

特に良いのは、`Fin 4` wrapper を source of truth にしなかったことじゃ。
既存の `shiftedSemanticIndexedBase r z i.val` に橋をかけているだけなので、証明資産を再利用できる。

```lean id="kmq5y3"
def shiftedSemanticFinBase
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) : Vec ℝ :=
  shiftedSemanticIndexedBase r z i.val
```

この形は良い。

また、`shiftedSemanticFinFourLevelPath` も新しく構成し直さず、既存の closed path object の alias にしている。

```lean id="xib91t"
def shiftedSemanticFinFourLevelPath
    ...
    := shiftedSemanticFourLevelPath hcore z
```

これは無駄がない。
閉路本体は一つ、finite wrapper は読みやすさのための API。
設計としてきれいじゃ。

## 5. 数学的意味

ここまでで、DkMath 側には次の構造ができている。

```text id="qpfxza"
fixed q2 boundary:
  保存核境界

shifted normalized edge:
  境界上の連続 edge

four indexed paths:
  四本で閉じる

Fin 4 wrapper:
  有限四状態 successor で読む
```

これはもう、pre-geometric cyclic skeleton じゃ。

まだ円ではない。
まだ角度でもない。
しかし、固定 `q2` 境界上に、有限四状態の閉路構造がある。

この「円と言わずに閉じている」が大事じゃ。

## 6. 次の本質

次は二つの道がある。

```text id="p0q5uv"
A:
  cyclic quotient parameter へ進む

B:
  closed path の観測 API を整える
```

わっちは、いきなり quotient へ行く前に、まず B を推す。

理由は、`shiftedSemanticFourLevelPath` は閉じた path object になったが、まだその path の中の「四つの seam / center / endpoint をどう読むか」の API が薄いからじゃ。

次に欲しいのは、closed path の観測点。

```text id="q7vahs"
edge 0 の開始点
edge 0 の中心
edge 1 の中心
edge 2 の中心
edge 3 の中心
閉路の終点
```

これらを theorem として整えると、後で quotient phase や Euclidean reading へ接続しやすくなる。

## 7. 次の勝利条件

次の checkpoint では、閉路そのものをいじるより、closed path の seam / center API を作るのがよい。

狙いはこう。

```text id="tfuxln"
Fin 4 successor:
  already done

next:
  Fin 4 center law
  Fin 4 q2 law
  Fin 4 edge endpoint law
  closed four path source/target aliases
  finite seam sequence documentation
```

もし可能なら、`finFourSucc` の小さい API も足すとよい。

```lean id="kipxwo"
finFourSucc_zero
finFourSucc_one
finFourSucc_two
finFourSucc_three
```

これがあると、後続の `fin_cases` 証明が読みやすくなる。

## 8. cyclic quotient は次の次でよい

continuous quotient parameter はまだ急がなくてよい。

なぜなら、今は `Fin 4` で有限骨格ができたばかりだからじゃ。
次は、その有限骨格の観測点 API を整える方が効果が高い。

```text id="ux322v"
now:
  finite cyclic skeleton

next:
  observation API on finite skeleton

later:
  continuous cyclic quotient parameter
```

この順番がよい。

## 9. 結論

今回の差分は採用でよい。

```text id="pixksg"
実装:
  良い。Fin 4 wrapper と finite successor seam law が入った。

数学:
  良い。有限四状態 cyclic index と fixed q2 closed path が接続された。

設計:
  良い。連続 quotient や Euclidean reading には進まず、有限 cyclic index で止めている。

次:
  Fin 4 観測 API と closed four path の読みやすい wrapper を整える。
```

ぬしよ、これはかなり安定してきた。
ここまで来ると、DkMath の pre-geometric 四状態閉路は、Lean API として十分に見える形になってきた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 4f862609..ef84e282 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -200,7 +200,10 @@ four-step return holds for bases, endpoints, and edge functions. Fixed-`q2`
 indexed level-set paths expose the same compatibility inside the boundary.
 The first four indexed shifted level paths now concatenate to a closed
 fixed-`q2` path object; the closing seam is supplied by the core-zero
-four-step return law.
+four-step return law. The same finite cyclic layer is also exposed through
+`Fin 4` wrappers for bases, edges, level edges, and paths, with a finite
+successor seam law for downstream code that wants a bounded index rather than
+raw natural-number indices.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 1ec39ac2..70c0db6f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1114,6 +1114,187 @@ def shiftedSemanticFourLevelPath
       (p2.cast h12 rfl)).trans
       (p3.cast h23 rfl)).cast rfl h30.symm
 
+/-!
+## Finite cyclic index wrappers
+
+The `Fin 4` wrappers give downstream code a finite cyclic index without
+choosing a continuous quotient phase parameter.
+-/
+
+/-- Cyclic successor on the four finite indices. -/
+def finFourSucc (i : Fin 4) : Fin 4 :=
+  ⟨(i.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩
+
+@[simp]
+theorem finFourSucc_val (i : Fin 4) :
+    (finFourSucc i).val = (i.val + 1) % 4 := rfl
+
+/-- The shifted base state indexed by `Fin 4`. -/
+def shiftedSemanticFinBase
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) : Vec ℝ :=
+  shiftedSemanticIndexedBase r z i.val
+
+@[simp]
+theorem shiftedSemanticFinBase_eq_indexed
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinBase r z i =
+      shiftedSemanticIndexedBase r z i.val := rfl
+
+/-- Every finite shifted base remains on the original square-mass level. -/
+theorem shiftedSemanticFinBase_q2
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
+    Vec.q2 (shiftedSemanticFinBase r z i) = Vec.q2 z :=
+  shiftedSemanticIndexedBase_q2 r z i.val
+
+/-- The shifted normalized edge indexed by `Fin 4`. -/
+def shiftedSemanticFinEdge
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) (t : ℝ) : Vec ℝ :=
+  shiftedSemanticIndexedEdge r z i.val t
+
+@[simp]
+theorem shiftedSemanticFinEdge_eq_indexed
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) (t : ℝ) :
+    shiftedSemanticFinEdge r z i t =
+      shiftedSemanticIndexedEdge r z i.val t := rfl
+
+/-- The finite shifted edge stays on the original square-mass boundary. -/
+theorem shiftedSemanticFinEdge_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) (t : ℝ) :
+    Vec.q2 (shiftedSemanticFinEdge r z i t) = Vec.q2 z := by
+  rw [shiftedSemanticFinEdge, shiftedSemanticIndexedEdge,
+    shiftedSemanticNormalizedEdge_q2_of_core_eq_zero hcore,
+    shiftedSemanticIndexedBase_q2]
+
+/-- The finite shifted edge center reaches the next indexed base state. -/
+theorem shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinEdge r z i phaseCenter =
+      shiftedSemanticIndexedBase r z (i.val + 1) :=
+  shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero hcore z i.val
+
+/-- The finite shifted normalized edge as a path. -/
+def shiftedSemanticFinPath
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
+    Path
+      (shiftedSemanticLeftEndpoint r (shiftedSemanticFinBase r z i))
+      (shiftedSemanticRightEndpoint r (shiftedSemanticFinBase r z i)) :=
+  shiftedSemanticIndexedPath r z i.val
+
+@[simp]
+theorem shiftedSemanticFinPath_apply
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
+    shiftedSemanticFinPath r z i t =
+      shiftedSemanticFinEdge r z i t := rfl
+
+/-- The finite shifted left endpoint inside the original square-mass level set. -/
+def shiftedSemanticFinLeftLevelEndpoint
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) : LevelSet ℝ (Vec.q2 z) :=
+  shiftedSemanticIndexedLeftLevelEndpoint hcore z i.val
+
+/-- The finite shifted right endpoint inside the original square-mass level set. -/
+def shiftedSemanticFinRightLevelEndpoint
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) : LevelSet ℝ (Vec.q2 z) :=
+  shiftedSemanticIndexedRightLevelEndpoint hcore z i.val
+
+@[simp]
+theorem shiftedSemanticFinLeftLevelEndpoint_eq_indexed
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinLeftLevelEndpoint hcore z i =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z i.val := rfl
+
+@[simp]
+theorem shiftedSemanticFinRightLevelEndpoint_eq_indexed
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinRightLevelEndpoint hcore z i =
+      shiftedSemanticIndexedRightLevelEndpoint hcore z i.val := rfl
+
+/-- The finite shifted level edge inside the original square-mass boundary. -/
+def shiftedSemanticFinLevelEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) (t : ℝ) : LevelSet ℝ (Vec.q2 z) :=
+  shiftedSemanticIndexedLevelEdge hcore z i.val t
+
+@[simp]
+theorem shiftedSemanticFinLevelEdge_eq_indexed
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) (t : ℝ) :
+    shiftedSemanticFinLevelEdge hcore z i t =
+      shiftedSemanticIndexedLevelEdge hcore z i.val t := rfl
+
+@[simp]
+theorem shiftedSemanticFinLevelEdge_val
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) (t : ℝ) :
+    (shiftedSemanticFinLevelEdge hcore z i t).1 =
+      shiftedSemanticFinEdge r z i t := rfl
+
+/-- The finite level edge center reaches the next indexed base level point. -/
+theorem shiftedSemanticFinLevelEdge_center_eq_next_base_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinLevelEdge hcore z i phaseCenter =
+      shiftedSemanticIndexedBaseLevelPoint r z (i.val + 1) :=
+  shiftedSemanticIndexedLevelEdge_center_eq_next_base_of_core_eq_zero hcore z i.val
+
+/-- The finite shifted normalized edge as a fixed-boundary path. -/
+def shiftedSemanticFinLevelPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    Path (shiftedSemanticFinLeftLevelEndpoint hcore z i)
+      (shiftedSemanticFinRightLevelEndpoint hcore z i) :=
+  shiftedSemanticIndexedLevelPath hcore z i.val
+
+@[simp]
+theorem shiftedSemanticFinLevelPath_apply
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
+    (shiftedSemanticFinLevelPath hcore z i t).1 =
+      shiftedSemanticFinEdge r z i t := rfl
+
+/--
+Finite cyclic seam compatibility: the right endpoint of finite edge `i` is
+the left endpoint of its cyclic successor.
+-/
+theorem shiftedSemanticFinRightLevelEndpoint_eq_succ_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (i : Fin 4) :
+    shiftedSemanticFinRightLevelEndpoint hcore z i =
+      shiftedSemanticFinLeftLevelEndpoint hcore z (finFourSucc i) := by
+  fin_cases i
+  · exact shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 0
+  · exact shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 1
+  · exact shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 2
+  · exact shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left hcore z
+
+/-- Finite-index alias for the closed four shifted level path. -/
+def shiftedSemanticFinFourLevelPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path
+      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0)
+      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0) :=
+  shiftedSemanticFourLevelPath hcore z
+
 /-!
 [IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
 The shifted semantic edge uses the normalized center states of neighboring
@@ -1138,6 +1319,11 @@ The first four indexed shifted normalized level paths are seam-compatible and
 concatenate to a closed fixed-`q2` path object. The closing seam uses the
 core-zero four-step return law, not any geometric angle reading.
 
+[IMPLEMENTED: semantic-cf2d/shifted-fin-four]
+The shifted indexed layer now has `Fin 4` wrappers for bases, edges, paths,
+fixed-`q2` level edges, and level paths. A finite cyclic successor records the
+four-state seam law without introducing a continuous quotient parameter.
+
 [TODO: semantic-cf2d/shifted-cyclic-quotient]
 Introduce a quotient phase parameter only after the four-edge closed path is
 stable enough for downstream consumers.
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 813e4e07..93d60b8b 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -440,6 +440,16 @@ shiftedSemanticIndexedLevelEndpoint_2_3
 shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left
 shiftedSemanticIndexedLevelEdge_add_four_of_core_eq_zero
 shiftedSemanticFourLevelPath
+finFourSucc
+shiftedSemanticFinBase
+shiftedSemanticFinEdge
+shiftedSemanticFinEdge_q2_of_core_eq_zero
+shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero
+shiftedSemanticFinPath
+shiftedSemanticFinLevelEdge
+shiftedSemanticFinLevelPath
+shiftedSemanticFinRightLevelEndpoint_eq_succ_left
+shiftedSemanticFinFourLevelPath
 ```
 
 The shifted normalized edge starts at the left normalized center candidate,
@@ -488,6 +498,25 @@ the fixed `q2` boundary. The first three seams are adjacent endpoint
 compatibility facts, and the final seam from edge `3` back to edge `0` uses
 the core-zero four-step return law.
 
+The finite cyclic wrapper is now available through `Fin 4`. It keeps the
+Nat-indexed API as the source of truth while giving downstream code a bounded
+four-state index:
+
+```text
+shiftedSemanticFinBase r z i = shiftedSemanticIndexedBase r z i.val
+shiftedSemanticFinEdge r z i t = shiftedSemanticIndexedEdge r z i.val t
+```
+
+The finite successor `finFourSucc` is defined by `(i.val + 1) % 4`, and Lean
+proves the finite seam law:
+
+```text
+right endpoint of finite edge i = left endpoint of finite edge (finFourSucc i)
+```
+
+This is still a finite cyclic index, not a continuous quotient phase
+parameter.
+
 Candidate theorem directions:
 
 ```text
@@ -559,7 +588,9 @@ depend on that reading.
 18. Implemented: package indexed shifted paths inside the fixed `q2` level set.
 19. Implemented: prove the four endpoint compatibility facts for indexed shifted level paths.
 20. Implemented: concatenate the four indexed shifted level paths into a closed fixed-`q2` path.
-21. Later: add a Euclidean bridge that reads `1/8` full-cycle
+21. Implemented: add `Fin 4` wrappers for shifted bases, edges, paths, level edges, and level paths.
+22. Implemented: prove the finite successor seam law on `Fin 4`.
+23. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -603,6 +634,11 @@ wrappers.
 [IMPLEMENTED: semantic-cf2d/shifted-four-level-path]
 Prove the four seam compatibility facts and concatenate the first four indexed
 shifted normalized level paths into one closed fixed-`q2` path object.
+
+[IMPLEMENTED: semantic-cf2d/shifted-fin-four]
+Expose the shifted cyclic index through `Fin 4` wrappers for bases, edges,
+paths, fixed-`q2` level edges, and fixed-`q2` level paths. Add a finite
+successor and prove the corresponding cyclic seam law.
 ```
 
 ## Remaining TODO Tags
````
`````
