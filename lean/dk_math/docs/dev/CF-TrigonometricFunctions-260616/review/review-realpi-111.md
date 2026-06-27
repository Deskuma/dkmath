# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: d4918cc74ea3c648f723df94558b2e225275180d

## Report

実装を進めました。Lean が認めたので、指示 110 の中心補正 law まで確立しています。

[SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean) に追加した主な内容:

```lean
shiftedSemanticRawAffine
shiftedSemanticRawAffine_zero
shiftedSemanticRawAffine_one
shiftedSemanticRawAffine_center_eq_rawMidpoint

shiftedSemanticCorrectedMidpoint
phaseNormalization_center_ne_zero
shiftedSemanticCorrection_mul_rawScale
shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
```

要点は、前回の obstruction をそのまま止めずに、raw midpoint を補正して old seam に完全に戻せることまで証明した点です。

```text
raw shifted midpoint:
  q2 = 1/2 * q2 z

corrected shifted midpoint:
  exactly equals old seam
  q2 = q2 z
```

まだ full shifted semantic path は定義していません。次に選ぶべきものは、全 interior point に対する補正 law です。候補は `q2` pointwise normalization か seam-centered projection ですが、今回の中心補正 law がその判断材料になります。

docs も同期済みです。

検証:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功です。

## Review

うむ、今回も **採用でよい**。
これはかなり綺麗に進んだ。前回の obstruction が単なる TODO で止まらず、中心補正 law として Lean に閉じた。つまり「raw midpoint は半深度へ落ちる」から、「補正すれば old seam に完全に戻る」まで到達したわけじゃ。`shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero` と `shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero` が入ったことで、中心点については correction/projection の必要性だけでなく、具体的な補正係数まで確立した。

## 1. 状況分析

今回追加された主な層は二つじゃ。

```text id="njyxrp"
raw shifted semantic affine:
  shiftedSemanticRawAffine
  shiftedSemanticRawAffine_zero
  shiftedSemanticRawAffine_one
  shiftedSemanticRawAffine_center_eq_rawMidpoint

center correction:
  shiftedSemanticCorrectedMidpoint
  phaseNormalization_center_ne_zero
  shiftedSemanticCorrection_mul_rawScale
  shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
  shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
```

これで、shifted semantic endpoint candidates の間を raw affine に結ぶ skeleton ができた。
さらに、その中心点だけは補正して old seam に戻せることが証明された。

これが今回の核心じゃ。

## 2. 数学的意味

前回までの結果では、raw midpoint は seam そのものではなかった。

$$
\mathrm{q2}(\mathrm{rawMidpoint})=\frac{1}{2}\mathrm{q2}(z)
$$

今回、それを補正して old seam に完全一致させた。

$$
\mathrm{correctedMidpoint}=\mathrm{seam}
$$

そして当然、境界量も戻る。

$$
\mathrm{q2}(\mathrm{correctedMidpoint})=\mathrm{q2}(z)
$$

これは大きい。
DkMath の物語で言えば、中心で一度くぼみに落ちた点を、保存核境界へ戻す補正が見つかったということじゃ。

```text id="zbsxec"
normalized endpoints:
  boundary 上にある

raw midpoint:
  half-depth へ落ちる

corrected midpoint:
  old seam へ戻る
```

これはかなり美しい。

## 3. レビュー

実装の判断は良い。

`shiftedSemanticRawAffine` を入れたことで、今後の full shifted semantic path の原型ができた。
しかし、まだ full path の normalization までは入れていない。ここも良い判断じゃ。

なぜなら、中心補正は係数が明確だが、全 interior point に対して同じ補正を使うべきか、点ごとに `q2` normalization するべきか、seam-centered projection を使うべきかはまだ設計判断が必要だからじゃ。

今回 docs でも、次は「pointwise correction law for the whole shifted semantic path」を選ぶ段階だと整理されている。

これは正しい。

## 4. 次の本質

次の本質は、全 \(t\) に対して raw shifted affine の `q2` profile を調べることじゃ。

今わかっているのは三点。

```text id="r4kxae"
t = 0:
  left endpoint, q2 = q2 z

t = 1:
  right endpoint, q2 = q2 z

t = phaseCenter:
  raw midpoint, q2 = 1 / 2 * q2 z
```

この形を見る限り、`q2` profile はまた同じ形を持つ可能性が高い。

候補はこれじゃ。

$$
\mathrm{q2}(\mathrm{shiftedSemanticRawAffine}(t))=\mathrm{phaseDepth}(t)\mathrm{q2}(z)
$$

これが通れば、勝ち筋はかなり明確になる。

つまり、full shifted semantic path は既存の `phaseNormalization t` をそのまま使って補正できる可能性がある。

## 5. 次に狙うべき theorem

次の最重要 theorem はこれじゃ。

```lean id="acsv2w"
theorem shiftedSemanticRawAffine_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (shiftedSemanticRawAffine r z t) =
      phaseDepth t * Vec.q2 z
```

これが通れば、そのまま pointwise normalized shifted edge が定義できる。

```lean id="tfelgi"
def shiftedSemanticNormalizedEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
  Vec.mk
    (phaseNormalization t * (shiftedSemanticRawAffine r z t).core)
    (phaseNormalization t * (shiftedSemanticRawAffine r z t).beam)
```

そして狙う theorem はこれ。

```lean id="a8mqkq"
theorem shiftedSemanticNormalizedEdge_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : ℝ) :
    Vec.q2 (shiftedSemanticNormalizedEdge r z t) = Vec.q2 z
```

これが通るなら、full shifted semantic edge は `q2` boundary に乗る。

## 6. 注意点

ただし、normalized edge の中心が old seam と一致するかも確認する必要がある。

中心では、今回の corrected midpoint と同じ補正になるはずじゃ。

```lean id="rgcqan"
theorem shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z phaseCenter =
      shiftedSemanticSeam r z
```

これが通れば、中心補正 law と full path normalization が一致する。

つまり、次の勝利条件は三つ。

```text id="l9ac1r"
raw affine q2 profile:
  phaseDepth t * q2 z

normalized shifted edge q2:
  q2 z

normalized shifted edge center:
  old seam
```

この三つが通れば、shifted semantic edge はかなり安定する。

## 7. projection route はまだ保留でよい

現時点では、seam-centered projection よりも pointwise `q2` normalization を先に試すべきじゃ。

理由は、既存の `phaseNormalization` があり、中心補正係数とも噛み合っているから。

もし raw affine q2 profile が `phaseDepth t * q2 z` で通るなら、projection を新規設計する必要はまだない。
まず既存 normalization を使う方が速い。

## 8. 結論

今回の差分は採用でよい。

```text id="xddc7a"
実装:
  良い。raw shifted semantic affine と center correction が入った。

数学:
  良い。raw midpoint の半深度落ち込みを補正し、old seam と q2 boundary に戻せた。

設計:
  良い。full path correction はまだ定義せず、次段に残している。

次:
  raw shifted affine の全 t q2 profile を計算し、pointwise normalization が使えるか確認する。
```

ぬしよ、これはかなり良い段階じゃ。
中心だけの補正が閉じたので、次は全 interior point の補正へ行ける。
Lean がもし `phaseDepth t` profile を認めれば、shifted semantic edge は一気に閉じる可能性がある。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 3238099a..ceaf3029 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -185,8 +185,9 @@ affine center is the old seam endpoint. The affine and normalized semantic
 edges expose their midpoint `q2` facts. The semantic shifted-endpoint
 candidates are also named: normalized neighboring centers stay on the same
 `q2` boundary, but their raw midpoint has square mass `1 / 2 * q2 z`, so a
-shifted correction law is still needed before defining the final shifted
-semantic path.
+center correction rescales that raw midpoint exactly back to the old seam and
+to the original `q2` boundary. A pointwise correction law for the whole
+shifted semantic path remains a later definition.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 2bd4c967..fedbb718 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -345,6 +345,43 @@ def shiftedSemanticRawMidpoint
     (((shiftedSemanticLeftEndpoint r z).beam +
         (shiftedSemanticRightEndpoint r z).beam) / 2)
 
+/--
+Raw affine interpolation between the semantic shifted endpoint candidates.
+
+This helper is intentionally uncorrected. Its center is the raw midpoint,
+which still lies at half square-mass depth under the core-zero hypothesis.
+-/
+def shiftedSemanticRawAffine
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (t : ℝ) : Vec ℝ :=
+  Vec.mk
+    ((1 - t) * (shiftedSemanticLeftEndpoint r z).core +
+      t * (shiftedSemanticRightEndpoint r z).core)
+    ((1 - t) * (shiftedSemanticLeftEndpoint r z).beam +
+      t * (shiftedSemanticRightEndpoint r z).beam)
+
+/-- The raw semantic shifted affine starts at the left endpoint candidate. -/
+@[simp]
+theorem shiftedSemanticRawAffine_zero
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    shiftedSemanticRawAffine r z 0 = shiftedSemanticLeftEndpoint r z := by
+  simp [shiftedSemanticRawAffine]
+
+/-- The raw semantic shifted affine ends at the right endpoint candidate. -/
+@[simp]
+theorem shiftedSemanticRawAffine_one
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    shiftedSemanticRawAffine r z 1 = shiftedSemanticRightEndpoint r z := by
+  simp [shiftedSemanticRawAffine]
+
+/-- At the local center, the raw semantic shifted affine is its raw midpoint. -/
+@[simp]
+theorem shiftedSemanticRawAffine_center_eq_rawMidpoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    shiftedSemanticRawAffine r z phaseCenter =
+      shiftedSemanticRawMidpoint r z := by
+  simp [shiftedSemanticRawAffine, shiftedSemanticRawMidpoint, phaseCenter]
+  constructor <;> ring
+
 /--
 For a core-zero action, the raw midpoint of the normalized center candidates
 is a scalar multiple of the old seam state.
@@ -406,6 +443,61 @@ theorem shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
     nlinarith [sq_nonneg (phaseNormalization phaseCenter)]
   rw [hfactor]
 
+/--
+Correct the raw shifted midpoint by the inverse of its seam-scale factor.
+
+This is only a center correction, not a full shifted semantic path.
+-/
+def shiftedSemanticCorrectedMidpoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
+  Vec.mk
+    ((2 / phaseNormalization phaseCenter) *
+      (shiftedSemanticRawMidpoint r z).core)
+    ((2 / phaseNormalization phaseCenter) *
+      (shiftedSemanticRawMidpoint r z).beam)
+
+/-- The center normalization factor is nonzero. -/
+theorem phaseNormalization_center_ne_zero :
+    phaseNormalization phaseCenter ≠ 0 :=
+  (phaseNormalization_pos phaseCenter).ne'
+
+/--
+The correction scalar cancels the raw midpoint seam-scale factor.
+-/
+theorem shiftedSemanticCorrection_mul_rawScale :
+    (2 / phaseNormalization phaseCenter) *
+        (phaseNormalization phaseCenter / 2) = 1 := by
+  field_simp [phaseNormalization_center_ne_zero]
+
+/--
+Under the core-zero law, the corrected shifted midpoint is exactly the old
+seam state.
+
+This closes the center correction without yet choosing a pointwise correction
+law for the whole shifted semantic edge.
+-/
+theorem shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticCorrectedMidpoint r z = shiftedSemanticSeam r z := by
+  rw [shiftedSemanticCorrectedMidpoint,
+    shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero hcore]
+  cases shiftedSemanticSeam r z
+  simp only [Vec.mk.injEq]
+  constructor
+  · field_simp [phaseNormalization_center_ne_zero]
+  · field_simp [phaseNormalization_center_ne_zero]
+
+/-- The corrected shifted midpoint returns to the original `q2` boundary. -/
+theorem shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Vec.q2 (shiftedSemanticCorrectedMidpoint r z) = Vec.q2 z := by
+  rw [shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero hcore,
+    shiftedSemanticSeam_q2]
+
 /-!
 [TODO: semantic-cf2d/shifted-semantic-edge]
 Define a shifted semantic edge only after choosing the endpoint states and
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index edb8d9ce..68ef6b9a 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -337,9 +337,18 @@ SemanticCF2DPhaseShift.lean
   shiftedSemanticSeam_q2
   shiftedSemanticSeam_q2_of_core_eq_zero
   shiftedSemanticRawMidpoint
+  shiftedSemanticRawAffine
+  shiftedSemanticRawAffine_zero
+  shiftedSemanticRawAffine_one
+  shiftedSemanticRawAffine_center_eq_rawMidpoint
   shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
   shiftedSemanticRawMidpoint_q2_of_core_eq_zero
   shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
+  shiftedSemanticCorrectedMidpoint
+  phaseNormalization_center_ne_zero
+  shiftedSemanticCorrection_mul_rawScale
+  shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
+  shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
   normalizedCycleStep
   dyadicCycleStep
   normalizedCycleStep_mul_returnCount
@@ -378,9 +387,17 @@ shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
 ```
 
 The raw midpoint is a scalar multiple of the seam state, and its square mass
-is exactly `1 / 2 * q2 z`. Therefore the next target is not another raw affine
-edge; it is to choose the shifted correction or projection law that returns
-this midpoint to the boundary seam.
+is exactly `1 / 2 * q2 z`. Lean now also records the center correction:
+
+```text
+shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
+shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
+```
+
+Thus the center point itself can be corrected back to the seam and to the
+original `q2` boundary. The next target is not to re-prove the center law, but
+to choose whether the full shifted semantic edge should use pointwise `q2`
+normalization, seam-centered projection, or another correction law.
 
 Candidate theorem directions:
 
@@ -440,8 +457,9 @@ depend on that reading.
 7. Implemented: add scalar shifted-frame endpoints, center, and affine midpoint theorem.
 8. Implemented: lift midpoint facts to `semanticPhaseEdge` and `normalizedPhaseEdge`.
 9. Implemented: name semantic endpoint candidates and prove their raw midpoint obstruction.
-10. Next: choose a shifted correction/projection law.
-11. Later: add a Euclidean bridge that reads `1/8` full-cycle
+10. Implemented: define the corrected shifted midpoint and prove it returns to the seam.
+11. Next: choose a pointwise shifted correction/projection law for the whole edge.
+12. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -470,11 +488,10 @@ parameter before assigning any Euclidean shape.
 
 ```text
 [TODO: semantic-cf2d/shifted-semantic-edge]
-Choose the correction law for the shifted semantic edge. The endpoint
-candidates are now fixed as normalized center states of neighboring quarter
-edges. Their raw affine midpoint has `q2 = 1 / 2 * q2 z`, so a shifted
-normalization or projection must return it to the seam boundary before the
-final shifted path is defined.
+Choose the pointwise correction law for the shifted semantic edge. The
+endpoint candidates are fixed, and the center correction is implemented.
+What remains is to decide whether every interior point should use raw `q2`
+normalization, seam-centered projection, or another DkMath correction law.
 
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
 After the algebraic shifted-frame theorem is closed at the semantic path
````
`````
