# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 47a7b64b5ecd57dde95e3797d5ea902398f6282e

## Report

完了しました。今回は指示内容に加えて、＋αで fixed-`q2` level-set 内の shifted path まで包装しました。

実装内容:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - endpoint alias: `shiftedSemanticNormalizedEdge_leftEndpoint/rightEndpoint`
  - 隣接 shifted edge の seam compatibility: `shiftedSemanticNormalizedEdge_right_eq_next_left`
  - center-to-action wrapper: `shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero`
  - continuity: `continuous_shiftedSemanticRawAffine`, `continuous_shiftedSemanticNormalizedEdge`
  - `Path`: `shiftedSemanticNormalizedPath`
  - fixed `q2` level-set wrappers and `shiftedSemanticNormalizedLevelPath`
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) と [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) も同期済みです。

検証:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`
- `lake build DkMath.Analysis.DkReal`
- `git diff --check`

すべて通っています。まだ Euclidean な角度語彙には進めず、pre-geometric な boundary-valued shifted path として確立しました。

## Review

うむ、今回も **採用でよい**。
そして、指示の粒度もかなり良く効いている。今回は `shiftedSemanticNormalizedEdge` がただの関数で止まらず、連続性、Mathlib `Path`、固定 `q2` level-set 内の path まで包装された。つまり checkpoint 104 の shifted-frame route は、pre-geometric な path layer まで到達したと言える。報告でも、`shiftedSemanticNormalizedPath` と `shiftedSemanticNormalizedLevelPath` が追加され、隣接 shifted edge の seam compatibility まで通っている。

## 1. 状況分析

今回の追加は大きく三層じゃ。

```text id="lfwcsq"
endpoint / seam compatibility:
  shiftedSemanticNormalizedEdge_leftEndpoint
  shiftedSemanticNormalizedEdge_rightEndpoint
  shiftedSemanticNormalizedEdge_right_eq_next_left
  shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero

continuity and Path:
  continuous_shiftedSemanticRawAffine
  continuous_shiftedSemanticNormalizedEdge
  shiftedSemanticNormalizedPath

fixed q2 level-set path:
  shiftedSemanticLeftLevelEndpoint
  shiftedSemanticRightLevelEndpoint
  shiftedSemanticSeamLevelPoint
  shiftedSemanticNormalizedLevelEdge
  shiftedSemanticNormalizedLevelPath
  shiftedSemanticNormalizedLevelEdge_center_eq_seam
```

これで、shifted normalized edge は単なる boundary-valued function ではなくなった。
連続 path として扱えるようになり、しかも固定 `q2` level-set の内部 path としても包装された。

これは非常に良い。

## 2. 今回の本丸

一番大きいのは、隣接 shifted edge の seam compatibility が入ったことじゃ。

$$
\mathrm{shiftedEdge}(r,z,1)=\mathrm{shiftedEdge}(r,\mathrm{semanticAct}(r,z),0)
$$

この等式があることで、shifted edges を連結する準備ができた。

つまり、今までの構造はこう進んだ。

```text id="kvyeyf"
scalar shifted frame:
  endpoint が center に読み替わる

semantic shifted edge:
  q2 boundary 上の normalized edge になる

topological path:
  continuous path として包装される

level-set path:
  fixed q2 boundary 内の path になる

seam compatibility:
  次の shifted edge と接続できる
```

ここまで通ったのは大きい。

## 3. fixed `q2` level-set path が良い

今回、単に `Path` にしただけではなく、固定 `q2` level-set の内部 path まで作ったのが良い。

これは DkMath 的にはかなり重要じゃ。

普通の `Vec ℝ` path だと、「たまたま `q2` が保存される」という theorem を横に持つ必要がある。
しかし level-set path にすると、codomain 自体が固定境界になる。

つまり、

```text id="73klai"
Vec Real path:
  path value に q2 theorem が付いている

LevelSet path:
  path value が最初から q2 boundary 内にいる
```

この違いは後で効く。
循環構造や concatenation を作るとき、保存核が型側に入るからじゃ。

## 4. 中心一致も良い

center-to-action wrapper も良い。

```lean id="iea6zz"
shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero
```

これは、shifted edge の中心が old seam、つまり次 action state であることを直接言う theorem じゃ。

これにより、文章上の読みが Lean API に入った。

```text id="5qe473"
shifted frame の中心:
  old seam state

old seam state:
  semanticAct r z
```

この定理があることで、後続の cyclic concatenation で seam を `semanticAct r z` として扱いやすくなる。

## 5. レビュー

実装判断はかなり良い。

まず、`continuous_shiftedSemanticRawAffine` と `continuous_shiftedSemanticNormalizedEdge` を入れたことで、path 化の下地が安定した。
次に `shiftedSemanticNormalizedPath` で Mathlib `Path` に包装し、そのうえで `shiftedSemanticNormalizedLevelPath` まで作った。

これは「薄い定理だけで止めない」という今回の進行方針に合っている。

さらに docs も良い。`shifted-semantic-path` が IMPLEMENTED になり、残り TODO が `shifted-cyclic-parameter` と `one-eighth-euclidean-reading` に整理されている。

今の TODO はかなり見通しがよい。

## 6. 次の本質

次は四本の shifted normalized path をどう束ねるかじゃ。

ただし、まだ角度ではない。
まだ円周でもない。
やるべきことは、有限 cyclic index と seam compatibility の整理じゃ。

現在は、単一 shifted edge と隣接 edge の接続がある。

次に欲しいのは、`k` 回 action された点を starting point とする shifted edge の族じゃ。

概念的にはこう。

```text id="pge3vw"
edge 0:
  z から始まる shifted edge

edge 1:
  semanticAct r z から始まる shifted edge

edge 2:
  semanticAct r (semanticAct r z) から始まる shifted edge

edge 3:
  semanticAct r ((semanticAct r)^[2] z) から始まる shifted edge
```

ただし、Lean では既に `semanticActIter` があるなら、それを使う方がよい。

## 7. 次に狙う theorem

まず欲しいのは、iterate 版の endpoint compatibility じゃ。

```lean id="pqhuq9"
shiftedSemanticNormalizedEdge_right_eq_iter_next_left
```

意味はこれ。

$$
\mathrm{edge}*k(1)=\mathrm{edge}*{k+1}(0)
$$

ここで `edge k` は、`semanticActIter r k z` を起点にする shifted edge じゃ。

これが通ると、四本連結の準備が整う。

## 8. まだ concatenation を急ぎすぎない

Mathlib `Path.trans` や path concatenation を使って四本 path を一気に結合するのは、次の一投で狙ってもよい。
ただし、proof が重ければ無理しない方がよい。

まずは、

```text id="l2v8i6"
indexed shifted edge
indexed seam compatibility
four-step return endpoint
```

ここまでで十分価値がある。

もし `semanticActIter_four_of_core_eq_zero` や `semanticAct_four_of_core_eq_zero` が使えるなら、四本目の終端が最初の始点へ戻ることも狙える。

ただし注意点がある。
shifted path の endpoint は raw action state ではなく normalized center state じゃ。
だから「四本で戻る」は、起点そのものではなく、shifted left endpoint の戻りとして言う必要がある。

## 9. 結論

今回の差分は採用でよい。

```text id="y4gqcn"
実装:
  良い。shifted normalized edge が Path と LevelSet Path になった。

数学:
  良い。q2 boundary-valued shifted path が成立した。

設計:
  良い。角度語彙へ進まず、pre-geometric path layer で閉じている。

次:
  shifted paths を cyclic index で束ね、四本連結の準備をする。
```

ぬしよ、ここまで来るとかなり強い。
「円」と言わずに、固定 `q2` 境界上の shifted path が連結可能になっている。
次は有限 cyclic parameter の包装じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 92898ed4..9b236fcb 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -189,7 +189,10 @@ center correction rescales that raw midpoint exactly back to the old seam and
 to the original `q2` boundary. The raw shifted affine edge has the same
 `phaseDepth` profile as the original affine edge, so the same pointwise
 normalization defines a shifted boundary-valued edge whose center is the old
-seam.
+seam. This shifted normalized edge is now continuous, packaged as a Mathlib
+`Path`, and also packaged as a path internal to the fixed `q2` level set.
+Adjacent shifted edges share their normalized center endpoint, preparing the
+later cyclic concatenation layer without adding geometric angle vocabulary.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 295313bc..3b4fa649 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -545,6 +545,13 @@ theorem shiftedSemanticNormalizedEdge_zero
     shiftedSemanticNormalizedEdge r z 0 = shiftedSemanticLeftEndpoint r z := by
   simp [shiftedSemanticNormalizedEdge]
 
+/-- Endpoint spelling for downstream shifted-path code. -/
+theorem shiftedSemanticNormalizedEdge_leftEndpoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    shiftedSemanticNormalizedEdge r z 0 =
+      shiftedSemanticLeftEndpoint r z :=
+  shiftedSemanticNormalizedEdge_zero r z
+
 /-- The normalized shifted edge ends at the right endpoint candidate. -/
 @[simp]
 theorem shiftedSemanticNormalizedEdge_one
@@ -552,6 +559,25 @@ theorem shiftedSemanticNormalizedEdge_one
     shiftedSemanticNormalizedEdge r z 1 = shiftedSemanticRightEndpoint r z := by
   simp [shiftedSemanticNormalizedEdge]
 
+/-- Endpoint spelling for downstream shifted-path code. -/
+theorem shiftedSemanticNormalizedEdge_rightEndpoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    shiftedSemanticNormalizedEdge r z 1 =
+      shiftedSemanticRightEndpoint r z :=
+  shiftedSemanticNormalizedEdge_one r z
+
+/--
+Adjacent shifted normalized edges meet at the same normalized center state.
+
+This is the seam-compatibility fact needed before any cyclic concatenation
+layer is introduced.
+-/
+theorem shiftedSemanticNormalizedEdge_right_eq_next_left
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    shiftedSemanticNormalizedEdge r z 1 =
+      shiftedSemanticNormalizedEdge r (semanticAct r z) 0 := by
+  simp [shiftedSemanticRightEndpoint, shiftedSemanticLeftEndpoint]
+
 /-- The normalized shifted edge stays on the original `q2` boundary. -/
 theorem shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
     {r : UnitKernel DkNNRealQ}
@@ -593,6 +619,172 @@ theorem shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
         (phaseNormalization phaseCenter ^ 2 / 2) * y := by ring
       _ = y := by rw [phaseNormalization_center_sq]; ring
 
+/--
+Center-to-seam spelling using the underlying semantic action.
+
+This form is convenient for later cyclic concatenation, where the seam is
+usually expressed as the next action state.
+-/
+theorem shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticNormalizedEdge r z phaseCenter =
+      semanticAct r z := by
+  rw [shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero hcore]
+  rfl
+
+/-!
+## Shifted normalized paths
+
+The shifted edge has the same analytic shape as the normalized phase edge:
+a continuous raw affine interpolation followed by the same positive scalar
+normalization. The path API below is still pre-geometric. It records only
+endpoint compatibility, seam compatibility, and fixed-`q2` boundary
+membership.
+-/
+
+/-- The raw shifted affine edge is continuous. -/
+theorem continuous_shiftedSemanticRawAffine
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    Continuous (fun t : ℝ => shiftedSemanticRawAffine r z t) := by
+  apply Continuous.vec_mk
+  · fun_prop
+  · fun_prop
+
+/-- The shifted normalized edge is continuous. -/
+theorem continuous_shiftedSemanticNormalizedEdge
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    Continuous (fun t : ℝ => shiftedSemanticNormalizedEdge r z t) := by
+  rcases continuous_vec_iff.mp
+      (continuous_shiftedSemanticRawAffine r z) with
+    ⟨hcore, hbeam⟩
+  apply Continuous.vec_mk
+  · exact continuous_phaseNormalization.mul hcore
+  · exact continuous_phaseNormalization.mul hbeam
+
+/--
+The shifted normalized edge packaged as a Mathlib path between neighboring
+normalized center states.
+-/
+def shiftedSemanticNormalizedPath
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    Path (shiftedSemanticLeftEndpoint r z)
+      (shiftedSemanticRightEndpoint r z) where
+  toFun t := shiftedSemanticNormalizedEdge r z t
+  continuous_toFun :=
+    (continuous_shiftedSemanticNormalizedEdge r z).comp continuous_subtype_val
+  source' := by simp
+  target' := by simp
+
+@[simp]
+theorem shiftedSemanticNormalizedPath_apply
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : unitInterval) :
+    shiftedSemanticNormalizedPath r z t =
+      shiftedSemanticNormalizedEdge r z t := rfl
+
+/-- The shifted normalized path remains on the original `q2` boundary. -/
+theorem shiftedSemanticNormalizedPath_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : unitInterval) :
+    Vec.q2 (shiftedSemanticNormalizedPath r z t) = Vec.q2 z :=
+  shiftedSemanticNormalizedEdge_q2_of_core_eq_zero hcore z t
+
+/-!
+## Shifted paths internal to the square-mass boundary
+
+As in the original normalized path layer, the next wrappers strengthen the
+codomain from `Vec Real` to the fixed `q2` level set.
+-/
+
+/-- The shifted left endpoint as a point of the fixed square-mass level set. -/
+def shiftedSemanticLeftLevelEndpoint
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) : LevelSet ℝ (Vec.q2 z) :=
+  ⟨shiftedSemanticLeftEndpoint r z,
+    shiftedSemanticLeftEndpoint_q2_of_core_eq_zero hcore z⟩
+
+/-- The shifted right endpoint as a point of the fixed square-mass level set. -/
+def shiftedSemanticRightLevelEndpoint
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) : LevelSet ℝ (Vec.q2 z) :=
+  ⟨shiftedSemanticRightEndpoint r z,
+    shiftedSemanticRightEndpoint_q2_of_core_eq_zero hcore z⟩
+
+/-- The shifted seam as a point of the fixed square-mass level set. -/
+def shiftedSemanticSeamLevelPoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    LevelSet ℝ (Vec.q2 z) :=
+  ⟨shiftedSemanticSeam r z, shiftedSemanticSeam_q2 r z⟩
+
+/--
+The shifted normalized edge as a point of the fixed square-mass level set.
+-/
+def shiftedSemanticNormalizedLevelEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : ℝ) : LevelSet ℝ (Vec.q2 z) :=
+  ⟨shiftedSemanticNormalizedEdge r z t,
+    shiftedSemanticNormalizedEdge_q2_of_core_eq_zero hcore z t⟩
+
+@[simp]
+theorem shiftedSemanticNormalizedLevelEdge_val
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : ℝ) :
+    (shiftedSemanticNormalizedLevelEdge hcore z t).1 =
+      shiftedSemanticNormalizedEdge r z t := rfl
+
+/-- The level-set-valued shifted normalized edge is continuous. -/
+theorem continuous_shiftedSemanticNormalizedLevelEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Continuous (fun t : ℝ => shiftedSemanticNormalizedLevelEdge hcore z t) :=
+  Continuous.subtype_mk (continuous_shiftedSemanticNormalizedEdge r z) _
+
+/--
+The shifted normalized edge as a path internal to the fixed square-mass level
+set.
+-/
+def shiftedSemanticNormalizedLevelPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path (shiftedSemanticLeftLevelEndpoint hcore z)
+      (shiftedSemanticRightLevelEndpoint hcore z) where
+  toFun t := shiftedSemanticNormalizedLevelEdge hcore z t
+  continuous_toFun :=
+    (continuous_shiftedSemanticNormalizedLevelEdge hcore z).comp
+      continuous_subtype_val
+  source' := by
+    apply Subtype.ext
+    simp [shiftedSemanticNormalizedLevelEdge, shiftedSemanticLeftLevelEndpoint]
+  target' := by
+    apply Subtype.ext
+    simp [shiftedSemanticNormalizedLevelEdge, shiftedSemanticRightLevelEndpoint]
+
+@[simp]
+theorem shiftedSemanticNormalizedLevelPath_apply
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : unitInterval) :
+    (shiftedSemanticNormalizedLevelPath hcore z t).1 =
+      shiftedSemanticNormalizedEdge r z t := rfl
+
+/-- At the center, the level-set-valued shifted path reaches the seam point. -/
+theorem shiftedSemanticNormalizedLevelEdge_center_eq_seam
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticNormalizedLevelEdge hcore z phaseCenter =
+      shiftedSemanticSeamLevelPoint r z := by
+  apply Subtype.ext
+  exact shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero hcore z
+
 /-!
 [IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
 The shifted semantic edge uses the normalized center states of neighboring
@@ -600,9 +792,15 @@ quarter edges as endpoints. Its raw affine form has the same `phaseDepth`
 profile as the original affine edge, so the same pointwise normalization
 keeps it on the original `q2` boundary and sends its center to the old seam.
 
-[TODO: semantic-cf2d/shifted-semantic-path]
-Package `shiftedSemanticNormalizedEdge` as a topological path once downstream
-code needs path concatenation or a cyclic quotient parameter.
+[IMPLEMENTED: semantic-cf2d/shifted-semantic-path]
+The shifted normalized edge is continuous and is packaged both as a `Vec Real`
+path and as a path internal to the fixed `q2` level set. Adjacent shifted
+edges share endpoint states, and the center of the shifted edge is the old
+seam state under the core-zero action law.
+
+[TODO: semantic-cf2d/shifted-cyclic-parameter]
+Package four shifted normalized paths by an explicit cyclic index once the
+next layer needs concatenation or a quotient phase parameter.
 -/
 
 /-!
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index fb118c0c..241175e3 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -414,13 +414,32 @@ the original affine edge. Therefore the same pointwise normalization is valid:
 
 ```text
 shiftedSemanticNormalizedEdge
+shiftedSemanticNormalizedEdge_leftEndpoint
+shiftedSemanticNormalizedEdge_rightEndpoint
+shiftedSemanticNormalizedEdge_right_eq_next_left
 shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
 shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
+shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero
+shiftedSemanticNormalizedPath
+shiftedSemanticNormalizedPath_q2_of_core_eq_zero
+shiftedSemanticNormalizedLevelPath
+shiftedSemanticNormalizedLevelEdge_center_eq_seam
 ```
 
 The shifted normalized edge starts at the left normalized center candidate,
 ends at the right normalized center candidate, stays on the original `q2`
-boundary, and reaches the old seam at `phaseCenter`.
+boundary, and reaches the old seam at `phaseCenter`. It is also packaged as a
+Mathlib `Path` and as a path internal to the fixed `q2` level set. Adjacent
+shifted normalized edges share endpoint states:
+
+```text
+shiftedSemanticNormalizedEdge r z 1
+  =
+shiftedSemanticNormalizedEdge r (semanticAct r z) 0
+```
+
+This is the seam-compatibility fact needed before four-edge shifted
+concatenation or a cyclic quotient parameter is introduced.
 
 Candidate theorem directions:
 
@@ -439,8 +458,9 @@ shifted-frame conservation
   boundary law after re-centering
 ```
 
-The last item should be delayed until the exact shifted path definition is
-chosen. The scalar theorem should come first.
+The shifted path definition has now been chosen in the same style as
+`normalizedPhasePath`: first a `Vec Real` path, then a fixed-`q2` level-set
+path. Four-edge shifted concatenation remains a later packaging layer.
 
 ## Guardrails
 
@@ -483,7 +503,9 @@ depend on that reading.
 10. Implemented: define the corrected shifted midpoint and prove it returns to the seam.
 11. Implemented: prove the raw shifted affine has the `phaseDepth` profile.
 12. Implemented: define the pointwise normalized shifted semantic edge.
-13. Later: add a Euclidean bridge that reads `1/8` full-cycle
+13. Implemented: package the shifted normalized edge as a topological path.
+14. Implemented: package the shifted normalized edge inside the fixed `q2` level set.
+15. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -511,14 +533,20 @@ parameter before assigning any Euclidean shape.
 Define the shifted semantic normalized edge from neighboring normalized center
 states, prove its raw `phaseDepth` profile, prove boundary preservation, and
 prove its center is the old seam.
+
+[IMPLEMENTED: semantic-cf2d/shifted-semantic-path]
+Package the shifted semantic normalized edge as a `Vec Real` path and as a
+fixed-`q2` level-set path. Endpoint aliases, adjacent seam compatibility, and
+center-to-action compatibility are exposed for downstream cyclic
+concatenation.
 ```
 
 ## Remaining TODO Tags
 
 ```text
-[TODO: semantic-cf2d/shifted-semantic-path]
-Package `shiftedSemanticNormalizedEdge` as a topological path when the next
-layer needs path concatenation or a cyclic quotient parameter.
+[TODO: semantic-cf2d/shifted-cyclic-parameter]
+Package four shifted normalized paths by an explicit cyclic index when the
+next layer needs concatenation or a quotient phase parameter.
 
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
 After the algebraic shifted-frame theorem is closed at the semantic path
````
`````
