# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 0757bbf43d8acb635a78460bc4222702d8d72887

## Report

指示 109 の Goal まで進めました。

[SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean) に semantic shifted-edge の候補層を追加しました。

追加した主な定義・定理:

```lean
shiftedSemanticLeftEndpoint
shiftedSemanticRightEndpoint
shiftedSemanticSeam

shiftedSemanticLeftEndpoint_q2_of_core_eq_zero
shiftedSemanticRightEndpoint_q2_of_core_eq_zero
shiftedSemanticSeam_q2
shiftedSemanticSeam_q2_of_core_eq_zero

shiftedSemanticRawMidpoint
shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
shiftedSemanticRawMidpoint_q2_of_core_eq_zero
shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
```

現場判断で、指示書の候補より一段強く、raw midpoint の `q2` が core-zero でちょうど

```lean
(1 / 2 : ℝ) * Vec.q2 z
```

になることまで証明しました。これで obstruction がかなり明確です。normalized center endpoints はそれぞれ boundary 上にありますが、その raw midpoint は seam ではなく、半深度へ落ちます。次は shifted correction/projection law を選ぶ段階です。

docs も同期しました。

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)

検証:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功です。

## Review

うむ、これはかなり大きな前進じゃ。
今回の差分は **採用でよい**。しかも、単なる endpoint candidate の命名に留まらず、raw midpoint obstruction が `q2` レベルで完全に数値化された。これは次の correction / projection law を選ぶための、非常に良い観測結果じゃ。

## 1. 状況分析

今回で、semantic shifted-edge の候補層が入った。

```text id="tgzgp2"
shiftedSemanticLeftEndpoint
shiftedSemanticRightEndpoint
shiftedSemanticSeam
shiftedSemanticRawMidpoint
```

意味はこうじゃ。

```text id="x9vdtw"
left endpoint candidate:
  current quarter edge の normalized center state

right endpoint candidate:
  next quarter edge の normalized center state

seam:
  その二つの edge の間にある旧 seam state

raw midpoint:
  left candidate と right candidate の座標平均
```

ここで重要なのは、左右 endpoint candidate はどちらも `q2` boundary 上にあることが証明された点じゃ。さらに seam も同じ `q2` boundary 上にある。

つまり、候補点は boundary 上に乗っている。

しかし、それらの raw midpoint は seam そのものではない。
ここが今回の obstruction じゃ。

## 2. 今回の最大成果

最大の成果は、raw midpoint の落ち込みが正確に出たことじゃ。

$$
\mathrm{q2}(\mathrm{shiftedSemanticRawMidpoint}\ r\ z)=\frac{1}{2},\mathrm{q2}(z)
$$

これは非常に良い。

scalar shifted frame では、左右 center の midpoint は旧 seam endpoint だった。
ところが semantic vector layer では、normalized center states の raw midpoint は旧 seam state ではなく、半深度へ落ちる。

つまり、ここで次の構造がはっきりした。

```text id="e3m8c7"
scalar shifted frame:
  midpoint is seam

semantic raw affine frame:
  midpoint falls to half q2 depth

therefore:
  correction / projection law is necessary
```

この「半深度へ落ちる」は、以前の affine midpoint と同じ現象じゃ。
つまり DkMath の観測物語としてかなり美しい。

```text id="kzqdx1"
boundary candidates:
  normalized and on q2 level

raw midpoint:
  falls inward

correction:
  returns it to boundary
```

これは「くぼみを見つけ、補正で境界へ戻す」構造そのものじゃ。

## 3. scaled seam theorem が強い

今回入った theorem は、単に q2 が半分というだけではない。

```lean id="cu25ol"
shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
```

これが重要じゃ。

raw midpoint は seam と無関係に落ちているのではなく、seam state の scalar multiple として落ちている。

係数は、報告によれば

```text id="q5u641"
phaseNormalization phaseCenter / 2
```

じゃ。

つまり、抽象的にはこう読める。

$$
\mathrm{rawMidpoint}=\frac{\mathrm{phaseNormalization}(\mathrm{phaseCenter})}{2},\mathrm{seam}
$$

この形なら、次の correction はほぼ見えている。

raw midpoint を seam に戻すには、逆係数をかければよい。

$$
\mathrm{correctedMidpoint}=\frac{2}{\mathrm{phaseNormalization}(\mathrm{phaseCenter})},\mathrm{rawMidpoint}
$$

これはまだ円ではない。
角度でもない。
ただの boundary correction law じゃ。

## 4. レビュー

今回の判断はかなり良い。

まず、semantic endpoint candidates を normalized center states として固定した。これは自然じゃ。
なぜなら、それぞれがすでに boundary 上に戻された点だから。

次に、その raw affine midpoint を seam と仮定せず、実際に計算した。
ここが正しい。

結果として、raw midpoint は seam ではなく scaled seam だった。
さらに `q2` は半分へ落ちた。

これは obstruction であると同時に、補正法の手がかりでもある。

```text id="jtyiua"
bad news:
  raw midpoint is not seam

good news:
  raw midpoint is exactly a scalar multiple of seam

next:
  invert the scalar
```

これはかなり良い展開じゃ。

## 5. ここで避けるべきこと

ここで Euclidean reading に進むのはまだ早い。

まだやるべきことは、角度ではなく補正法の選択じゃ。

```text id="p8d0k5"
do next:
  correction law
  projection law
  normalized shifted midpoint

do not yet:
  pi / 4
  45 degree
  circle arc
  Euclidean angle
```

特に今回、raw midpoint obstruction が綺麗に出たので、次は「補正して seam に戻る」を Lean で閉じるべきじゃ。

## 6. 次の最短ルート

次はおそらく、この correction def を置くのが最短じゃ。

```lean id="hym5bv"
def shiftedSemanticCorrectedMidpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  Vec.scale (2 / phaseNormalization phaseCenter)
    (shiftedSemanticRawMidpoint r z)
```

もし `Vec.scale` が既存名でなければ、`Vec.mk` で core / beam に係数をかける形でもよい。

狙う theorem はこれ。

```lean id="muc1ow"
theorem shiftedSemanticCorrectedMidpoint_eq_seam_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticCorrectedMidpoint r z = shiftedSemanticSeam r z
```

これが通れば、今回の obstruction は完全に correction law へ変わる。

次に、

```lean id="y68t4z"
theorem shiftedSemanticCorrectedMidpoint_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Vec.q2 (shiftedSemanticCorrectedMidpoint r z) = Vec.q2 z
```

も通るはずじゃ。
これは seam equality からも出せるし、q2 scale からも出せる。

## 7. correction と projection の違い

ここで用語を整理しておくとよい。

```text id="ppjbmf"
correction:
  known scalar factor を逆にかけて seam に戻す

projection:
  q2 boundary へ戻す一般操作として定義する
```

今回の状況では、raw midpoint が scaled seam であることが分かっている。
だからまずは correction law でよい。

projection はより一般的だが重い。
今の段階では、`phaseCenter` 専用の correction theorem を閉じる方が速い。

## 8. 次の重め theorem

その次に狙うなら、shifted semantic affine edge の中心だけを補正するのではなく、path 全体に補正を入れる方向がある。

ただし、これは少し危険じゃ。

なぜなら、全 \(t\) に対してどの normalization factor を使うかを決める必要があるから。

今すぐ path 全体を定義するなら、候補はこうなる。

```text id="wjagtz"
raw shifted semantic affine edge:
  leftEndpoint と rightEndpoint の affine interpolation

shifted correction:
  q2 boundary に戻す scalar normalization

corrected shifted edge:
  corrected raw shifted edge
```

しかし、全 \(t\) の normalization は `q2` が正であることや sqrt が絡む可能性がある。

だから次の一投では、まず **center 専用 correction** を閉じる。
届けば raw shifted affine edge def まで置く。
path 全体の normalization は TODO でよい。

## 9. 結論

今回の差分は採用でよい。

```text id="uycuxf"
実装:
  良い。semantic endpoint candidates が入り、q2 boundary facts が閉じた。

数学:
  良い。raw midpoint が scaled seam であり、q2 が半分に落ちることが証明された。

設計:
  良い。shifted semantic path を急がず、correction law が必要と明記した。

次:
  raw midpoint obstruction を correction law に変換する。
```

ぬしよ、これは大きい。
「raw では落ちる」が Lean で数値化された。
ならば次は「補正で戻る」を示す番じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 528b0463..3238099a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -182,8 +182,11 @@ phase displacement without using circle or arc language. Scalar return laws
 for dyadic and positive `k` cycle divisions are also recorded. The shifted
 scalar frame now names neighboring centers as endpoints and proves that its
 affine center is the old seam endpoint. The affine and normalized semantic
-edges expose their midpoint `q2` facts, while shifted semantic paths remain a
-later definition.
+edges expose their midpoint `q2` facts. The semantic shifted-endpoint
+candidates are also named: normalized neighboring centers stay on the same
+`q2` boundary, but their raw midpoint has square mass `1 / 2 * q2 z`, so a
+shifted correction law is still needed before defining the final shifted
+semantic path.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index ee07dff1..2bd4c967 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -276,6 +276,136 @@ theorem shiftedQuarterAffine_center_eq_shiftedQuarterCenter (k : ℕ) :
   simp [phaseCenter]
   ring
 
+/-!
+## Semantic shifted endpoint candidates
+
+The natural semantic endpoint candidates are the normalized center states of
+two neighboring quarter edges. Their raw midpoint is deliberately computed
+below instead of being assumed to be the old seam state.
+-/
+
+/-- Left semantic endpoint candidate for the shifted frame. -/
+def shiftedSemanticLeftEndpoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
+  normalizedPhaseEdge r z phaseCenter
+
+/-- Right semantic endpoint candidate for the shifted frame. -/
+def shiftedSemanticRightEndpoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
+  normalizedPhaseEdge r (semanticAct r z) phaseCenter
+
+/-- The old seam state between the neighboring quarter edges. -/
+def shiftedSemanticSeam
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
+  semanticAct r z
+
+/-- The left semantic endpoint candidate remains on the original `q2` boundary. -/
+theorem shiftedSemanticLeftEndpoint_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Vec.q2 (shiftedSemanticLeftEndpoint r z) = Vec.q2 z := by
+  exact normalizedPhaseEdge_q2_of_core_eq_zero hcore z phaseCenter
+
+/-- The right semantic endpoint candidate remains on the original `q2` boundary. -/
+theorem shiftedSemanticRightEndpoint_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Vec.q2 (shiftedSemanticRightEndpoint r z) = Vec.q2 z := by
+  rw [shiftedSemanticRightEndpoint,
+    normalizedPhaseEdge_q2_of_core_eq_zero hcore,
+    semanticAct_q2]
+
+/-- The old seam state is on the same `q2` boundary. -/
+theorem shiftedSemanticSeam_q2
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    Vec.q2 (shiftedSemanticSeam r z) = Vec.q2 z :=
+  semanticAct_q2 r z
+
+/-- Core-zero spelling of `shiftedSemanticSeam_q2`, for uniform downstream APIs. -/
+theorem shiftedSemanticSeam_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (_hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Vec.q2 (shiftedSemanticSeam r z) = Vec.q2 z :=
+  shiftedSemanticSeam_q2 r z
+
+/--
+Raw coordinate midpoint between the shifted semantic endpoint candidates.
+
+This is only the uncorrected midpoint. It is useful precisely because it lets
+the next theorem state the correction obstruction explicitly.
+-/
+def shiftedSemanticRawMidpoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
+  Vec.mk
+    (((shiftedSemanticLeftEndpoint r z).core +
+        (shiftedSemanticRightEndpoint r z).core) / 2)
+    (((shiftedSemanticLeftEndpoint r z).beam +
+        (shiftedSemanticRightEndpoint r z).beam) / 2)
+
+/--
+For a core-zero action, the raw midpoint of the normalized center candidates
+is a scalar multiple of the old seam state.
+
+The scalar is `phaseNormalization phaseCenter / 2`, not definitionally `1`.
+This is the concrete obstruction: a final shifted semantic edge needs an
+additional correction or projection law before its center can be identified
+with the seam state.
+-/
+theorem shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticRawMidpoint r z =
+      Vec.mk
+        ((phaseNormalization phaseCenter / 2) * (shiftedSemanticSeam r z).core)
+        ((phaseNormalization phaseCenter / 2) * (shiftedSemanticSeam r z).beam) := by
+  cases z
+  simp [shiftedSemanticRawMidpoint, shiftedSemanticLeftEndpoint,
+    shiftedSemanticRightEndpoint, shiftedSemanticSeam, normalizedPhaseEdge,
+    semanticPhaseEdge, phaseCenter, semanticAct_of_core_eq_zero hcore]
+  constructor <;> ring
+
+/--
+The raw shifted midpoint has the square-mass of the seam scaled by
+`(phaseNormalization phaseCenter / 2)^2`.
+
+This packages the same obstruction at the boundary-observation level.
+-/
+theorem shiftedSemanticRawMidpoint_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Vec.q2 (shiftedSemanticRawMidpoint r z) =
+      (phaseNormalization phaseCenter / 2) ^ 2 * Vec.q2 z := by
+  rw [shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero hcore]
+  rw [Vec.q2_scale, shiftedSemanticSeam_q2]
+
+/--
+At the boundary-observation level, the raw midpoint has only half the original
+square mass.
+
+This stronger form makes the obstruction explicit: the candidate endpoints
+are individually normalized, but their raw midpoint has fallen back to the
+same half-depth value as an unnormalized affine center.
+-/
+theorem shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Vec.q2 (shiftedSemanticRawMidpoint r z) =
+      (1 / 2 : ℝ) * Vec.q2 z := by
+  have hnorm_sq : phaseNormalization phaseCenter ^ 2 = 2 := by
+    have hcancel := phaseNormalization_sq_mul_phaseDepth phaseCenter
+    rw [phaseDepth_center_eq] at hcancel
+    nlinarith
+  rw [shiftedSemanticRawMidpoint_q2_of_core_eq_zero hcore]
+  have hfactor : (phaseNormalization phaseCenter / 2) ^ 2 = 1 / 2 := by
+    nlinarith [sq_nonneg (phaseNormalization phaseCenter)]
+  rw [hfactor]
+
 /-!
 [TODO: semantic-cf2d/shifted-semantic-edge]
 Define a shifted semantic edge only after choosing the endpoint states and
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index d40c504c..edb8d9ce 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -329,6 +329,17 @@ SemanticCF2DPhaseShift.lean
   shiftedQuarterAffine_zero_eq_leftEndpoint
   shiftedQuarterAffine_one_eq_rightEndpoint
   shiftedQuarterAffine_center_eq_shiftedQuarterCenter
+  shiftedSemanticLeftEndpoint
+  shiftedSemanticRightEndpoint
+  shiftedSemanticSeam
+  shiftedSemanticLeftEndpoint_q2_of_core_eq_zero
+  shiftedSemanticRightEndpoint_q2_of_core_eq_zero
+  shiftedSemanticSeam_q2
+  shiftedSemanticSeam_q2_of_core_eq_zero
+  shiftedSemanticRawMidpoint
+  shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
+  shiftedSemanticRawMidpoint_q2_of_core_eq_zero
+  shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
   normalizedCycleStep
   dyadicCycleStep
   normalizedCycleStep_mul_returnCount
@@ -342,9 +353,34 @@ SemanticCF2DPhaseShift.lean
 
 The scalar shifted-frame API is now implemented, including endpoint
 separation, center half-quarter formulas, and the affine interpolation helper
-`shiftedQuarterAffine`. The next target is to choose the semantic endpoint
-states and correction law for a shifted semantic edge, then lift the
-shifted-frame scalar center theorem to that path.
+`shiftedQuarterAffine`.
+
+The first semantic endpoint candidates are also implemented:
+
+```text
+left candidate:
+  normalized center state of the current quarter edge
+
+right candidate:
+  normalized center state of the next quarter edge
+
+seam:
+  the old endpoint state between those two edges
+```
+
+The candidates all lie on the same `q2` boundary under the core-zero
+hypothesis. However, their raw affine midpoint is not the seam state in
+general. Lean records the obstruction in two forms:
+
+```text
+shiftedSemanticRawMidpoint_eq_scaled_seam_of_core_eq_zero
+shiftedSemanticRawMidpoint_q2_half_of_core_eq_zero
+```
+
+The raw midpoint is a scalar multiple of the seam state, and its square mass
+is exactly `1 / 2 * q2 z`. Therefore the next target is not another raw affine
+edge; it is to choose the shifted correction or projection law that returns
+this midpoint to the boundary seam.
 
 Candidate theorem directions:
 
@@ -403,8 +439,9 @@ depend on that reading.
 6. Implemented: add scalar cycle-step facts for dyadic and positive `k` divisions.
 7. Implemented: add scalar shifted-frame endpoints, center, and affine midpoint theorem.
 8. Implemented: lift midpoint facts to `semanticPhaseEdge` and `normalizedPhaseEdge`.
-9. Next: choose a shifted semantic edge definition.
-10. Later: add a Euclidean bridge that reads `1/8` full-cycle
+9. Implemented: name semantic endpoint candidates and prove their raw midpoint obstruction.
+10. Next: choose a shifted correction/projection law.
+11. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -433,11 +470,11 @@ parameter before assigning any Euclidean shape.
 
 ```text
 [TODO: semantic-cf2d/shifted-semantic-edge]
-Choose the endpoint states and correction law for the shifted semantic edge.
-The natural candidates are normalized center states of neighboring quarter
-edges, but their raw affine midpoint is not generally the old seam state.
-After selecting the shifted normalization/projection law, prove scalar
-compatibility with `shiftedQuarterCenter`.
+Choose the correction law for the shifted semantic edge. The endpoint
+candidates are now fixed as normalized center states of neighboring quarter
+edges. Their raw affine midpoint has `q2 = 1 / 2 * q2 z`, so a shifted
+normalization or projection must return it to the seam boundary before the
+final shifted path is defined.
 
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
 After the algebraic shifted-frame theorem is closed at the semantic path
````
`````
