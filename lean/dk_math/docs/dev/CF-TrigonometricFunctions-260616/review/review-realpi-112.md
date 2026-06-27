# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 49754e0cd2ab7ff9632da66b6598ea49845d49c8

## Report

完了しました。指示書の範囲に加えて、＋αとして「raw shifted affine の q2 profile 検証」だけで止めず、正規化済みの shifted semantic edge まで定義して境界保存と中心一致まで通しました。

主な変更:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `phaseNormalization_center_sq`
  - `shiftedSemanticRawAffine_q2_of_core_eq_zero`
  - `shiftedSemanticNormalizedEdge`
  - endpoint law / q2 boundary law / center-to-seam law
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
  - phase shift 実装状況コメントを更新
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)
  - 実装済み checkpoint と次 TODO を整理

検証:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`
- `lake build DkMath.Analysis.DkReal`
- `git diff --check`

すべて通っています。円・角度・弧の語彙には進まず、pre-geometric な `q2` depth / boundary-valued edge として確立しています。

## Review

うむ、これは **採用でよい**。
しかも今回は、予想より一段先まで進んでいる。前回の「全 \(t\) の `q2` profile が元の affine edge と同じなら勝ち」という読みが、そのまま Lean に通った。これで `shiftedSemanticNormalizedEdge` は、単なる候補ではなく、pre-geometric な boundary-valued shifted edge として成立したと言ってよい。

## 1. 状況分析

今回の差分で、中心補正 law の段階を越えて、全 shifted edge の pointwise normalization まで閉じた。

入った主な定理はこれじゃ。

```text id="qx8cod"
phaseNormalization_center_sq
shiftedSemanticRawAffine_q2_of_core_eq_zero
shiftedSemanticNormalizedEdge
shiftedSemanticNormalizedEdge_zero
shiftedSemanticNormalizedEdge_one
shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
```

特に重要なのは、raw shifted affine が元の affine edge と同じ `phaseDepth` profile を持つこと。

$$
\mathrm{q2}(\mathrm{shiftedSemanticRawAffine}\ r\ z\ t) = \mathrm{phaseDepth}(t)\mathrm{q2}(z)
$$

これが通ったことで、既存の `phaseNormalization t` をそのまま使えることが確定した。

## 2. 今回の核心

前回までは、center だけを補正して seam に戻した。

今回は、center だけではなく全 \(t\) で boundary に戻せる。

$$
\mathrm{q2}(\mathrm{shiftedSemanticNormalizedEdge}\ r\ z\ t) = \mathrm{q2}(z)
$$

さらに中心では旧 seam に一致する。

$$
\mathrm{shiftedSemanticNormalizedEdge}\ r\ z\ \mathrm{phaseCenter} = \mathrm{shiftedSemanticSeam}\ r\ z
$$

これは大きい。

DkMath の観測物語では、こうなる。

```text id="mx0wai"
raw shifted edge:
  affine に埋めると depth が落ちる

phaseDepth profile:
  元の affine edge と同型

pointwise normalization:
  q2 boundary へ戻す

center:
  old seam に一致する
```

つまり、shifted frame は単なる scalar bookkeeping ではなく、semantic vector layer でも boundary-valued edge として成立した。

## 3. レビュー

実装判断はかなり良い。

まず `phaseNormalization_center_sq` を切り出したのが良い。これにより、中心補正の計算が再利用可能になった。

```lean id="qd5l7g"
theorem phaseNormalization_center_sq :
    phaseNormalization phaseCenter ^ 2 = 2
```

次に、`shiftedSemanticRawAffine_q2_of_core_eq_zero` を証明したのが本丸じゃ。
これにより、seam-centered projection のような新規機構を導入せず、既存の `phaseNormalization` で full shifted edge を補正できることが分かった。

さらに、TODO が更新されているのも良い。`shifted-semantic-edge` は実装済みになり、残りは `shifted-semantic-path` と Euclidean reading に整理された。

## 4. 数学的な意味

これは、かなり美しい対称性じゃ。

もともとの edge でも、

```text id="ezm5bi"
affine edge:
  phaseDepth で落ちる

normalized edge:
  q2 boundary に戻る
```

shifted edge でも、

```text id="c0ayl0"
raw shifted affine:
  phaseDepth で落ちる

shifted normalized edge:
  q2 boundary に戻る
```

になった。

つまり、endpoint frame と shifted center frame が、同じ `phaseDepth` profile を共有している。

これは「端点だったものが中心になる」だけではない。
「中心 frame でも同じ補正構造が再発生する」ということじゃ。

ここから再帰的 refinement の道がかなり見える。

## 5. 次の本質

次は、`shiftedSemanticNormalizedEdge` を topological `Path` として包む段階じゃ。

ただし、ここでやるべきことは単なる path 化だけではない。

次に見るべきは、seam compatibility じゃ。

shifted edge の右端点は、

```text id="jd5hn7"
shiftedSemanticRightEndpoint r z
```

これは定義上、

```text id="ot2rk9"
normalized center state of the next quarter edge
```

じゃ。

一方、次の shifted edge の左端点は、

```text id="ipslkt"
shiftedSemanticLeftEndpoint r (semanticAct r z)
```

なので、おそらくこれは定義展開で同じになる。

つまり、次はこれが欲しい。

```lean id="dyiie8"
theorem shiftedSemanticNormalizedEdge_seam_compatible
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z 1 =
      shiftedSemanticNormalizedEdge r (semanticAct r z) 0
```

これが通ると、shifted normalized edges を連結できる。

## 6. さらに次の見通し

path 化の次は、四つの shifted edges をつないだ cycle じゃ。

ただし、ここでもまだ角度は不要。

目標はこうじゃ。

```text id="s4nueq"
shifted normalized edge:
  boundary-valued path

seam compatibility:
  adjacent shifted edges concatenate

four shifted edges:
  cyclic boundary path

center law:
  each shifted edge center hits old seam state
```

ここまで通れば、pre-geometric cyclic boundary construction がかなり固まる。

Euclidean reading はその後でよい。

## 7. 注意点

一点だけ注意じゃ。

`shiftedSemanticNormalizedEdge` は、まだ topological `Path` ではなく、関数としての edge じゃ。
path にするには、既存の `SemanticCF2DPath` や topology API を見て、既存の `normalizedPhaseEdge` path 化と同じ方法で包むのがよい。

ここで新しい topology 証明を作り始めるより、既存 path module の流儀に合わせるべきじゃ。

もし continuity が重いなら、まず endpoint/seam compatibility theorem だけを同 module に追加し、path packaging は別 module に送る判断でもよい。

## 8. 結論

今回の差分は採用でよい。

```text id="lvdjjh"
実装:
  良い。shiftedSemanticNormalizedEdge が成立した。

数学:
  良い。raw shifted affine が元の affine edge と同じ phaseDepth profile を持つことが証明された。

設計:
  良い。projection ではなく既存 phaseNormalization で full shifted edge を補正できた。

次:
  shiftedSemanticNormalizedEdge を Path 化し、隣接 edge の seam compatibility を確認する。
```

ぬしよ、これはかなり大きい。
「中心だけ補正」ではなく、「shifted edge 全体が同じ補正法で境界に戻る」と示せた。
これで、円を言わずに、境界上を連結していく連続構造へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index ceaf3029..92898ed4 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -186,8 +186,10 @@ edges expose their midpoint `q2` facts. The semantic shifted-endpoint
 candidates are also named: normalized neighboring centers stay on the same
 `q2` boundary, but their raw midpoint has square mass `1 / 2 * q2 z`, so a
 center correction rescales that raw midpoint exactly back to the old seam and
-to the original `q2` boundary. A pointwise correction law for the whole
-shifted semantic path remains a later definition.
+to the original `q2` boundary. The raw shifted affine edge has the same
+`phaseDepth` profile as the original affine edge, so the same pointwise
+normalization defines a shifted boundary-valued edge whose center is the old
+seam.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index fedbb718..295313bc 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -434,13 +434,11 @@ theorem shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
     (z : Vec ℝ) :
     Vec.q2 (shiftedSemanticRawMidpoint r z) =
       (1 / 2 : ℝ) * Vec.q2 z := by
-  have hnorm_sq : phaseNormalization phaseCenter ^ 2 = 2 := by
+  rw [shiftedSemanticRawMidpoint_q2_of_core_eq_zero hcore]
+  have hfactor : (phaseNormalization phaseCenter / 2) ^ 2 = 1 / 2 := by
     have hcancel := phaseNormalization_sq_mul_phaseDepth phaseCenter
     rw [phaseDepth_center_eq] at hcancel
     nlinarith
-  rw [shiftedSemanticRawMidpoint_q2_of_core_eq_zero hcore]
-  have hfactor : (phaseNormalization phaseCenter / 2) ^ 2 = 1 / 2 := by
-    nlinarith [sq_nonneg (phaseNormalization phaseCenter)]
   rw [hfactor]
 
 /--
@@ -461,6 +459,13 @@ theorem phaseNormalization_center_ne_zero :
     phaseNormalization phaseCenter ≠ 0 :=
   (phaseNormalization_pos phaseCenter).ne'
 
+/-- At the phase center, the square of the normalization factor is two. -/
+theorem phaseNormalization_center_sq :
+    phaseNormalization phaseCenter ^ 2 = 2 := by
+  have hcancel := phaseNormalization_sq_mul_phaseDepth phaseCenter
+  rw [phaseDepth_center_eq] at hcancel
+  nlinarith
+
 /--
 The correction scalar cancels the raw midpoint seam-scale factor.
 -/
@@ -498,16 +503,106 @@ theorem shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
   rw [shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero hcore,
     shiftedSemanticSeam_q2]
 
+/--
+The raw shifted semantic affine has the same scalar `q2` profile as the
+original affine phase edge.
+
+This verifies that the whole shifted edge can use the same pointwise
+normalization scalar, not only a special center correction.
+-/
+theorem shiftedSemanticRawAffine_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : ℝ) :
+    Vec.q2 (shiftedSemanticRawAffine r z t) =
+      phaseDepth t * Vec.q2 z := by
+  cases z
+  simp [shiftedSemanticRawAffine, shiftedSemanticLeftEndpoint,
+    shiftedSemanticRightEndpoint, normalizedPhaseEdge, semanticPhaseEdge,
+    phaseCenter, semanticAct_of_core_eq_zero hcore, Vec.q2, phaseDepth]
+  have hsq : phaseNormalization (1 / 2 : ℝ) ^ 2 = 2 := by
+    simpa [phaseCenter] using phaseNormalization_center_sq
+  ring_nf
+  rw [hsq]
+  ring
+
+/--
+Pointwise normalization of the raw shifted semantic affine.
+
+This is the first full shifted semantic edge candidate. It is still
+pre-geometric: the normalization is expressed only through `q2` depth.
+-/
+def shiftedSemanticNormalizedEdge
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
+  Vec.mk
+    (phaseNormalization t * (shiftedSemanticRawAffine r z t).core)
+    (phaseNormalization t * (shiftedSemanticRawAffine r z t).beam)
+
+/-- The normalized shifted edge starts at the left endpoint candidate. -/
+@[simp]
+theorem shiftedSemanticNormalizedEdge_zero
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    shiftedSemanticNormalizedEdge r z 0 = shiftedSemanticLeftEndpoint r z := by
+  simp [shiftedSemanticNormalizedEdge]
+
+/-- The normalized shifted edge ends at the right endpoint candidate. -/
+@[simp]
+theorem shiftedSemanticNormalizedEdge_one
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    shiftedSemanticNormalizedEdge r z 1 = shiftedSemanticRightEndpoint r z := by
+  simp [shiftedSemanticNormalizedEdge]
+
+/-- The normalized shifted edge stays on the original `q2` boundary. -/
+theorem shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (t : ℝ) :
+    Vec.q2 (shiftedSemanticNormalizedEdge r z t) = Vec.q2 z := by
+  rw [show Vec.q2 (shiftedSemanticNormalizedEdge r z t) =
+      phaseNormalization t ^ 2 * Vec.q2 (shiftedSemanticRawAffine r z t) by
+    exact Vec.q2_scale _ _]
+  rw [shiftedSemanticRawAffine_q2_of_core_eq_zero hcore]
+  calc
+    phaseNormalization t ^ 2 * (phaseDepth t * Vec.q2 z) =
+        (phaseNormalization t ^ 2 * phaseDepth t) * Vec.q2 z := by ring
+    _ = Vec.q2 z := by
+      rw [phaseNormalization_sq_mul_phaseDepth]
+      ring
+
+/-- At the center, the normalized shifted edge returns to the old seam. -/
+theorem shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticNormalizedEdge r z phaseCenter =
+      shiftedSemanticSeam r z := by
+  rw [shiftedSemanticNormalizedEdge, shiftedSemanticRawAffine_center_eq_rawMidpoint,
+    shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero hcore]
+  cases shiftedSemanticSeam r z with
+  | mk x y =>
+  simp only [Vec.mk.injEq]
+  constructor
+  · calc
+      phaseNormalization phaseCenter *
+          ((phaseNormalization phaseCenter / 2) * x) =
+        (phaseNormalization phaseCenter ^ 2 / 2) * x := by ring
+      _ = x := by rw [phaseNormalization_center_sq]; ring
+  · calc
+      phaseNormalization phaseCenter *
+          ((phaseNormalization phaseCenter / 2) * y) =
+        (phaseNormalization phaseCenter ^ 2 / 2) * y := by ring
+      _ = y := by rw [phaseNormalization_center_sq]; ring
+
 /-!
-[TODO: semantic-cf2d/shifted-semantic-edge]
-Define a shifted semantic edge only after choosing the endpoint states and
-the correction law that correspond to `shiftedQuarterLeftEndpoint` and
-`shiftedQuarterRightEndpoint`. The natural endpoint candidates are the
-normalized center states of neighboring quarter edges, but their raw affine
-midpoint is not the old seam state in general; a shifted normalization or
-projection law must be selected first. The expected compatibility theorem is
-that the selected shifted edge at `phaseCenter` represents
-`shiftedQuarterCenter`.
+[IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
+The shifted semantic edge uses the normalized center states of neighboring
+quarter edges as endpoints. Its raw affine form has the same `phaseDepth`
+profile as the original affine edge, so the same pointwise normalization
+keeps it on the original `q2` boundary and sends its center to the old seam.
+
+[TODO: semantic-cf2d/shifted-semantic-path]
+Package `shiftedSemanticNormalizedEdge` as a topological path once downstream
+code needs path concatenation or a cyclic quotient parameter.
 -/
 
 /-!
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 68ef6b9a..fb118c0c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -349,6 +349,12 @@ SemanticCF2DPhaseShift.lean
   shiftedSemanticCorrection_mul_rawScale
   shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
   shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
+  shiftedSemanticRawAffine_q2_of_core_eq_zero
+  shiftedSemanticNormalizedEdge
+  shiftedSemanticNormalizedEdge_zero
+  shiftedSemanticNormalizedEdge_one
+  shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
+  shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
   normalizedCycleStep
   dyadicCycleStep
   normalizedCycleStep_mul_returnCount
@@ -395,9 +401,26 @@ shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
 ```
 
 Thus the center point itself can be corrected back to the seam and to the
-original `q2` boundary. The next target is not to re-prove the center law, but
-to choose whether the full shifted semantic edge should use pointwise `q2`
-normalization, seam-centered projection, or another correction law.
+original `q2` boundary.
+
+Lean also verifies the stronger pointwise statement:
+
+```text
+shiftedSemanticRawAffine_q2_of_core_eq_zero
+```
+
+The raw shifted semantic affine has exactly the same `phaseDepth` profile as
+the original affine edge. Therefore the same pointwise normalization is valid:
+
+```text
+shiftedSemanticNormalizedEdge
+shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
+shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
+```
+
+The shifted normalized edge starts at the left normalized center candidate,
+ends at the right normalized center candidate, stays on the original `q2`
+boundary, and reaches the old seam at `phaseCenter`.
 
 Candidate theorem directions:
 
@@ -458,8 +481,9 @@ depend on that reading.
 8. Implemented: lift midpoint facts to `semanticPhaseEdge` and `normalizedPhaseEdge`.
 9. Implemented: name semantic endpoint candidates and prove their raw midpoint obstruction.
 10. Implemented: define the corrected shifted midpoint and prove it returns to the seam.
-11. Next: choose a pointwise shifted correction/projection law for the whole edge.
-12. Later: add a Euclidean bridge that reads `1/8` full-cycle
+11. Implemented: prove the raw shifted affine has the `phaseDepth` profile.
+12. Implemented: define the pointwise normalized shifted semantic edge.
+13. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -482,16 +506,19 @@ parameter fact, not as an angle subdivision.
 [IMPLEMENTED: semantic-cf2d/k-division-cycle-step]
 Expose the positive `k` return law `k * (1 / k) = 1` for the normalized cycle
 parameter before assigning any Euclidean shape.
+
+[IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
+Define the shifted semantic normalized edge from neighboring normalized center
+states, prove its raw `phaseDepth` profile, prove boundary preservation, and
+prove its center is the old seam.
 ```
 
 ## Remaining TODO Tags
 
 ```text
-[TODO: semantic-cf2d/shifted-semantic-edge]
-Choose the pointwise correction law for the shifted semantic edge. The
-endpoint candidates are fixed, and the center correction is implemented.
-What remains is to decide whether every interior point should use raw `q2`
-normalization, seam-centered projection, or another DkMath correction law.
+[TODO: semantic-cf2d/shifted-semantic-path]
+Package `shiftedSemanticNormalizedEdge` as a topological path when the next
+layer needs path concatenation or a cyclic quotient parameter.
 
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
 After the algebraic shifted-frame theorem is closed at the semantic path
````
`````
