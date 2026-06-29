# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 89e4f0916b273e3c70987e992137d22fe4ecf333

## Report

完了しました。今回は指示内容の indexed shifted edge に加えて、＋αで fixed-`q2` level-set 内の indexed path まで入れています。

実装:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedSemanticIndexedBase`
  - `shiftedSemanticIndexedEdge`
  - `shiftedSemanticIndexedPath`
  - indexed seam compatibility
  - center-to-next-base compatibility
  - core-zero 4-step return for bases/endpoints/edges
  - fixed-`q2` indexed level endpoints, edge, path
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) と [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) も同期済みです。

検証:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`
- `lake build DkMath.Analysis.DkReal`
- `git diff --check`

すべて通っています。まだ角度・円弧・Euclidean 読みには進めず、pre-geometric な cyclic-index / fixed-boundary path layer として固めました。

## Review

うむ、今回も **採用でよい**。
これはかなり強い checkpoint じゃ。前回までは「単一 shifted path が固定 `q2` level-set 内にある」段階だったが、今回でそれが **semantic action iterates による indexed family** になった。つまり、edgewise な shifted path が、四状態周期へ束ねられる準備まで進んだ。報告でも、indexed seam compatibility、center-to-next-base compatibility、core-zero 四歩戻り、fixed-`q2` indexed level-set path wrapper まで通っている。

## 1. 状況分析

今回の実装は、次の層を追加している。

```text id="n4wjju"
indexed base:
  shiftedSemanticIndexedBase

indexed edge:
  shiftedSemanticIndexedEdge

indexed path:
  shiftedSemanticIndexedPath

indexed level-set path:
  shiftedSemanticIndexedLevelPath

compatibility:
  edge k の右端点 = edge k+1 の左端点
  edge k の中心 = indexed base k+1

periodicity:
  indexed base k+4 = indexed base k
  indexed edge k+4 = indexed edge k
```

これで、単一 edge ではなく、action orbit に沿った shifted edge family ができた。

重要なのは、index がまだ角度ではないことじゃ。
これは geometric angle parameter ではなく、semantic action count じゃ。

```text id="h0dgxe"
index k:
  action count

not:
  angle
  arc position
  Euclidean rotation parameter
```

ここがちゃんと守られている。

## 2. 今回の本丸

一番大きいのは、indexed seam compatibility じゃ。

概念的にはこれ。

$$
\mathrm{edge}*k(1)=\mathrm{edge}*{k+1}(0)
$$

今回、これが `shiftedSemanticIndexedEdge_right_eq_next_left` として入った。

これで edgewise concatenation の準備ができた。
さらに level-set 側でも、右 endpoint と次の左 endpoint が同じ seam point である theorem が入っている。

つまり、固定 `q2` boundary の中で、edge を順に接続する土台ができた。

## 3. center-to-next-base が良い

今回のもう一つの核はこれじゃ。

```lean id="j4ufb3"
shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero
```

これは、edge \(k\) の中心が、次の indexed base に一致するという theorem じゃ。

意味はこう。

$$
\mathrm{edge}*k(\mathrm{phaseCenter})=\mathrm{base}*{k+1}
$$

これは非常に DkMath らしい。
shifted frame の中心が old seam であり、その seam が次 base になる。

```text id="ycvt3f"
edge k:
  left normalized center から始まる

center:
  base k+1 に到達する

right:
  next normalized center に到達する
```

この構造が、pre-geometric な周期細分化の骨格になる。

## 4. 四歩戻りが入ったのが大きい

core-zero の下で、

```lean id="uvgqnr"
shiftedSemanticIndexedBase_add_four_of_core_eq_zero
shiftedSemanticIndexedEdge_add_four_of_core_eq_zero
```

が入った。

これはかなり大きい。

四状態周期が、単なる semanticActIter の周期ではなく、shifted indexed edge の族にも伝播した。

つまり、

$$
\mathrm{base}_{k+4}=\mathrm{base}_k
$$

かつ、

$$
\mathrm{edge}_{k+4}(t)=\mathrm{edge}_k(t)
$$

が言える。

これで、四本を一巡として扱う準備が整った。

## 5. fixed `q2` level-set indexed path が良い

今回、`Vec ℝ` の indexed path だけでなく、固定 `q2 z` level-set 内の indexed path まで作ったのが良い。

```text id="pkpbw4"
shiftedSemanticIndexedBaseLevelPoint
shiftedSemanticIndexedLeftLevelEndpoint
shiftedSemanticIndexedRightLevelEndpoint
shiftedSemanticIndexedLevelEdge
shiftedSemanticIndexedLevelPath
```

これにより、後続の path concatenation は「境界保存 theorem を横に持つ」のではなく、最初から fixed boundary の中で行える。

これは設計としてかなり強い。

## 6. レビュー

実装判断は良い。
前回の指示では「indexed family と seam compatibility、届けば四歩戻り」までを狙ったが、今回はその範囲を超えて level-set indexed path まで通っている。

特に良いのは、Remaining TODO が整理されたことじゃ。

```text id="f5jeml"
remaining:
  shifted-four-path
  shifted-cyclic-quotient
  one-eighth Euclidean reading
```

これで次に何をすべきかが明確になった。

## 7. 次の本質

次は、四本の indexed shifted level paths を連結して、ひとつの closed fixed-`q2` path object にする段階じゃ。

ただし、ここは少しだけ Lean 的に注意が要る。

`Path.trans` 型の連結は、前の path の target と次の path の source が、型として一致している必要がある。
今回、それらは theorem では一致しているが、定義上は別名になっている可能性がある。

だから次の一投では、いきなり完全な closed path に飛ぶより、まず「連結用 endpoint cast / wrapper」を作るとよい。

目標はこう。

```text id="csgpba"
edge 0 target = edge 1 source
edge 1 target = edge 2 source
edge 2 target = edge 3 source
edge 3 target = edge 0 source
```

最初の三つは adjacent seam compatibility。
最後は four-step return が必要になる。

## 8. 次の勝利条件

次の checkpoint の勝利条件は三つじゃ。

```text id="oalnme"
1:
  level endpoint compatibility を四本分で使いやすい形にする

2:
  edge 3 の右端点が edge 0 の左端点へ戻る theorem を証明する

3:
  可能なら four shifted level paths を `Path.trans` で閉じた path に包装する
```

もし `Path.trans` の型合わせが重いなら、まず theorem-level の closed chain を完了させればよい。
それだけでも十分に価値がある。

## 9. ここでまだ Euclidean reading へ行かない理由

ここまで来ると「一周」と言いたくなるが、まだ Euclidean angle ではない。

今あるのは、

```text id="y1tflp"
fixed q2 boundary
semantic action index
four-step return
edgewise continuity
seam compatibility
```

じゃ。

これは pre-geometric closed boundary path。
Euclidean reading は、closed path object が安定してからでよい。

## 10. 結論

今回の差分は採用でよい。

```text id="f9q05y"
実装:
  良い。indexed shifted edge と level-set indexed path が成立した。

数学:
  良い。四歩周期が edge family に伝播した。

設計:
  良い。角度語彙なしで cyclic-index layer まで来た。

次:
  四本の indexed shifted level paths を閉じた fixed-q2 path object にする。
```

ぬしよ、これはかなりの進展じゃ。
もう「円」と言わずに、固定 `q2` 境界上で四本の連続 edge が閉じるところまで見えている。
ここからは、四本連結の Lean 包装が主戦場じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 9b236fcb..569c91c7 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -193,6 +193,11 @@ seam. This shifted normalized edge is now continuous, packaged as a Mathlib
 `Path`, and also packaged as a path internal to the fixed `q2` level set.
 Adjacent shifted edges share their normalized center endpoint, preparing the
 later cyclic concatenation layer without adding geometric angle vocabulary.
+The shifted edge is now also indexed by semantic action iterates. Indexed
+bases stay on the initial square-mass level, adjacent indexed shifted edges
+share seams, their centers are the next indexed bases, and core-zero
+four-step return holds for bases, endpoints, and edge functions. Fixed-`q2`
+indexed level-set paths expose the same compatibility inside the boundary.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 3b4fa649..332445c9 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -785,6 +785,229 @@ theorem shiftedSemanticNormalizedLevelEdge_center_eq_seam
   apply Subtype.ext
   exact shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero hcore z
 
+/-!
+## Indexed shifted normalized edges
+
+The next layer moves the shifted edge along the finite action orbit. The
+index is still an action count, not a geometric angle parameter.
+-/
+
+/-- The base state for the `k`th shifted edge. -/
+def shiftedSemanticIndexedBase
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) : Vec ℝ :=
+  semanticActIter r k z
+
+@[simp]
+theorem shiftedSemanticIndexedBase_zero
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    shiftedSemanticIndexedBase r z 0 = z := rfl
+
+@[simp]
+theorem shiftedSemanticIndexedBase_succ
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticIndexedBase r z (k + 1) =
+      semanticAct r (shiftedSemanticIndexedBase r z k) := by
+  simp [shiftedSemanticIndexedBase]
+
+/-- Every indexed base remains on the original square-mass level. -/
+theorem shiftedSemanticIndexedBase_q2
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    Vec.q2 (shiftedSemanticIndexedBase r z k) = Vec.q2 z := by
+  rw [shiftedSemanticIndexedBase, semanticActIter, semanticAct_iterate_q2]
+
+/-- The `k`th shifted normalized edge. -/
+def shiftedSemanticIndexedEdge
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : ℝ) : Vec ℝ :=
+  shiftedSemanticNormalizedEdge r (shiftedSemanticIndexedBase r z k) t
+
+/-- The `k`th shifted normalized edge as a Mathlib path. -/
+def shiftedSemanticIndexedPath
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    Path
+      (shiftedSemanticLeftEndpoint r (shiftedSemanticIndexedBase r z k))
+      (shiftedSemanticRightEndpoint r (shiftedSemanticIndexedBase r z k)) :=
+  shiftedSemanticNormalizedPath r (shiftedSemanticIndexedBase r z k)
+
+@[simp]
+theorem shiftedSemanticIndexedPath_apply
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : unitInterval) :
+    shiftedSemanticIndexedPath r z k t =
+      shiftedSemanticIndexedEdge r z k t := rfl
+
+/-- Consecutive indexed shifted edges share their seam endpoint. -/
+theorem shiftedSemanticIndexedEdge_right_eq_next_left
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticIndexedEdge r z k 1 =
+      shiftedSemanticIndexedEdge r z (k + 1) 0 := by
+  rw [shiftedSemanticIndexedEdge, shiftedSemanticIndexedEdge,
+    shiftedSemanticIndexedBase_succ]
+  exact shiftedSemanticNormalizedEdge_right_eq_next_left r
+    (shiftedSemanticIndexedBase r z k)
+
+/--
+At its center, the `k`th indexed shifted edge reaches the next indexed base
+state.
+-/
+theorem shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticIndexedEdge r z k phaseCenter =
+      shiftedSemanticIndexedBase r z (k + 1) := by
+  simp [shiftedSemanticIndexedEdge,
+    shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero hcore]
+
+/-- Core-zero indexed bases repeat after four action steps. -/
+theorem shiftedSemanticIndexedBase_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticIndexedBase r z (k + 4) =
+      shiftedSemanticIndexedBase r z k := by
+  exact semanticActIter_add_four_of_core_eq_zero hcore k z
+
+/-- The indexed shifted left endpoints repeat after four action steps. -/
+theorem shiftedSemanticIndexedLeftEndpoint_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticLeftEndpoint r
+        (shiftedSemanticIndexedBase r z (k + 4)) =
+      shiftedSemanticLeftEndpoint r
+        (shiftedSemanticIndexedBase r z k) := by
+  rw [shiftedSemanticIndexedBase_add_four_of_core_eq_zero hcore]
+
+/-- The indexed shifted right endpoints repeat after four action steps. -/
+theorem shiftedSemanticIndexedRightEndpoint_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticRightEndpoint r
+        (shiftedSemanticIndexedBase r z (k + 4)) =
+      shiftedSemanticRightEndpoint r
+        (shiftedSemanticIndexedBase r z k) := by
+  rw [shiftedSemanticIndexedBase_add_four_of_core_eq_zero hcore]
+
+/-- Indexed shifted edges repeat after four action steps. -/
+theorem shiftedSemanticIndexedEdge_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
+    shiftedSemanticIndexedEdge r z (k + 4) t =
+      shiftedSemanticIndexedEdge r z k t := by
+  rw [shiftedSemanticIndexedEdge, shiftedSemanticIndexedEdge,
+    shiftedSemanticIndexedBase_add_four_of_core_eq_zero hcore]
+
+/-!
+## Indexed shifted paths inside the square-mass boundary
+
+These wrappers keep the codomain fixed at the original `q2 z` level while
+the indexed base state moves by the semantic action.
+-/
+
+/-- The indexed base as a point of the original square-mass level set. -/
+def shiftedSemanticIndexedBaseLevelPoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    LevelSet ℝ (Vec.q2 z) :=
+  ⟨shiftedSemanticIndexedBase r z k,
+    shiftedSemanticIndexedBase_q2 r z k⟩
+
+/-- The indexed shifted left endpoint inside the original square-mass level set. -/
+def shiftedSemanticIndexedLeftLevelEndpoint
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) : LevelSet ℝ (Vec.q2 z) :=
+  ⟨shiftedSemanticLeftEndpoint r (shiftedSemanticIndexedBase r z k), by
+    rw [shiftedSemanticLeftEndpoint_q2_of_core_eq_zero hcore,
+      shiftedSemanticIndexedBase_q2]⟩
+
+/-- The indexed shifted right endpoint inside the original square-mass level set. -/
+def shiftedSemanticIndexedRightLevelEndpoint
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) : LevelSet ℝ (Vec.q2 z) :=
+  ⟨shiftedSemanticRightEndpoint r (shiftedSemanticIndexedBase r z k), by
+    rw [shiftedSemanticRightEndpoint_q2_of_core_eq_zero hcore,
+      shiftedSemanticIndexedBase_q2]⟩
+
+/-- The indexed shifted normalized edge inside the original square-mass level set. -/
+def shiftedSemanticIndexedLevelEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) : LevelSet ℝ (Vec.q2 z) :=
+  ⟨shiftedSemanticIndexedEdge r z k t, by
+    rw [shiftedSemanticIndexedEdge,
+      shiftedSemanticNormalizedEdge_q2_of_core_eq_zero hcore,
+      shiftedSemanticIndexedBase_q2]⟩
+
+@[simp]
+theorem shiftedSemanticIndexedLevelEdge_val
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
+    (shiftedSemanticIndexedLevelEdge hcore z k t).1 =
+      shiftedSemanticIndexedEdge r z k t := rfl
+
+/-- The indexed level-set-valued shifted edge is continuous. -/
+theorem continuous_shiftedSemanticIndexedLevelEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    Continuous (fun t : ℝ => shiftedSemanticIndexedLevelEdge hcore z k t) :=
+  Continuous.subtype_mk
+    (continuous_shiftedSemanticNormalizedEdge r
+      (shiftedSemanticIndexedBase r z k)) _
+
+/-- The indexed shifted normalized edge as a fixed-boundary path. -/
+def shiftedSemanticIndexedLevelPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    Path (shiftedSemanticIndexedLeftLevelEndpoint hcore z k)
+      (shiftedSemanticIndexedRightLevelEndpoint hcore z k) where
+  toFun t := shiftedSemanticIndexedLevelEdge hcore z k t
+  continuous_toFun :=
+    (continuous_shiftedSemanticIndexedLevelEdge hcore z k).comp
+      continuous_subtype_val
+  source' := by
+    apply Subtype.ext
+    simp [shiftedSemanticIndexedLevelEdge,
+      shiftedSemanticIndexedLeftLevelEndpoint, shiftedSemanticIndexedEdge]
+  target' := by
+    apply Subtype.ext
+    simp [shiftedSemanticIndexedLevelEdge,
+      shiftedSemanticIndexedRightLevelEndpoint, shiftedSemanticIndexedEdge]
+
+@[simp]
+theorem shiftedSemanticIndexedLevelPath_apply
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : unitInterval) :
+    (shiftedSemanticIndexedLevelPath hcore z k t).1 =
+      shiftedSemanticIndexedEdge r z k t := rfl
+
+/-- Consecutive indexed level endpoints are the same seam point. -/
+theorem shiftedSemanticIndexedRightLevelEndpoint_eq_next_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticIndexedRightLevelEndpoint hcore z k =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z (k + 1) := by
+  apply Subtype.ext
+  simp [shiftedSemanticIndexedRightLevelEndpoint,
+    shiftedSemanticIndexedLeftLevelEndpoint, shiftedSemanticRightEndpoint,
+    shiftedSemanticLeftEndpoint]
+
+/-- The indexed level edge center is the next indexed base point. -/
+theorem shiftedSemanticIndexedLevelEdge_center_eq_next_base_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticIndexedLevelEdge hcore z k phaseCenter =
+      shiftedSemanticIndexedBaseLevelPoint r z (k + 1) := by
+  apply Subtype.ext
+  exact shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero hcore z k
+
 /-!
 [IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
 The shifted semantic edge uses the normalized center states of neighboring
@@ -801,6 +1024,16 @@ seam state under the core-zero action law.
 [TODO: semantic-cf2d/shifted-cyclic-parameter]
 Package four shifted normalized paths by an explicit cyclic index once the
 next layer needs concatenation or a quotient phase parameter.
+
+[IMPLEMENTED: semantic-cf2d/shifted-indexed-edge]
+The shifted normalized edge is now indexed by semantic action iterates.
+Indexed edges have adjacent seam compatibility, centers at the next indexed
+base state, four-step return under the core-zero law, and fixed-`q2`
+level-set path wrappers.
+
+[TODO: semantic-cf2d/shifted-four-path]
+Concatenate four indexed shifted normalized paths once the next layer needs a
+single closed path object rather than edgewise compatibility facts.
 -/
 
 /-!
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 241175e3..cd374996 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -424,6 +424,16 @@ shiftedSemanticNormalizedPath
 shiftedSemanticNormalizedPath_q2_of_core_eq_zero
 shiftedSemanticNormalizedLevelPath
 shiftedSemanticNormalizedLevelEdge_center_eq_seam
+shiftedSemanticIndexedBase
+shiftedSemanticIndexedEdge
+shiftedSemanticIndexedPath
+shiftedSemanticIndexedEdge_right_eq_next_left
+shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero
+shiftedSemanticIndexedBase_add_four_of_core_eq_zero
+shiftedSemanticIndexedEdge_add_four_of_core_eq_zero
+shiftedSemanticIndexedLevelPath
+shiftedSemanticIndexedRightLevelEndpoint_eq_next_left
+shiftedSemanticIndexedLevelEdge_center_eq_next_base_of_core_eq_zero
 ```
 
 The shifted normalized edge starts at the left normalized center candidate,
@@ -441,6 +451,26 @@ shiftedSemanticNormalizedEdge r (semanticAct r z) 0
 This is the seam-compatibility fact needed before four-edge shifted
 concatenation or a cyclic quotient parameter is introduced.
 
+The cyclic-index preparation is now also formalized. The `k`th shifted edge
+uses the semantic action iterate as its base state:
+
+```text
+shiftedSemanticIndexedBase r z k = semanticActIter r k z
+```
+
+The indexed edge is the shifted normalized edge at that base. Lean proves:
+
+```text
+right endpoint of edge k = left endpoint of edge k+1
+center of edge k = indexed base k+1
+indexed base (k+4) = indexed base k       under core-zero
+indexed edge (k+4) = indexed edge k       under core-zero
+```
+
+The same indexed API is available inside the fixed `q2 z` level set, so the
+next layer can concatenate edgewise-compatible paths without re-proving
+boundary membership.
+
 Candidate theorem directions:
 
 ```text
@@ -505,7 +535,11 @@ depend on that reading.
 12. Implemented: define the pointwise normalized shifted semantic edge.
 13. Implemented: package the shifted normalized edge as a topological path.
 14. Implemented: package the shifted normalized edge inside the fixed `q2` level set.
-15. Later: add a Euclidean bridge that reads `1/8` full-cycle
+15. Implemented: index shifted normalized edges by semantic action iterates.
+16. Implemented: prove indexed adjacent seam compatibility and center-to-next-base compatibility.
+17. Implemented: prove core-zero four-step return for indexed bases, endpoints, and edge functions.
+18. Implemented: package indexed shifted paths inside the fixed `q2` level set.
+19. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -539,14 +573,24 @@ Package the shifted semantic normalized edge as a `Vec Real` path and as a
 fixed-`q2` level-set path. Endpoint aliases, adjacent seam compatibility, and
 center-to-action compatibility are exposed for downstream cyclic
 concatenation.
+
+[IMPLEMENTED: semantic-cf2d/shifted-indexed-edge]
+Index shifted normalized edges by semantic action iterates. Prove adjacent
+indexed seam compatibility, center-to-next-base compatibility, four-step
+return for bases and edge functions, and fixed-`q2` indexed level-set path
+wrappers.
 ```
 
 ## Remaining TODO Tags
 
 ```text
-[TODO: semantic-cf2d/shifted-cyclic-parameter]
-Package four shifted normalized paths by an explicit cyclic index when the
-next layer needs concatenation or a quotient phase parameter.
+[TODO: semantic-cf2d/shifted-four-path]
+Concatenate four indexed shifted normalized paths into one closed fixed-`q2`
+path object.
+
+[TODO: semantic-cf2d/shifted-cyclic-quotient]
+Introduce a quotient phase parameter only after the four indexed path
+concatenation is stable.
 
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
 After the algebraic shifted-frame theorem is closed at the semantic path
````
`````
