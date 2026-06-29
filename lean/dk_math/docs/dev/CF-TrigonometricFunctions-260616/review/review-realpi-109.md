# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 31ad2fa3d64fbb4db7772112782277b62bbff23a

## Report

作業指示書 108 の Goal まで進めました。

[SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean) に shifted-frame scalar API を補強しました。

追加した主なもの:

```lean
shiftedQuarterRightEndpoint_sub_leftEndpoint
shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter
shiftedQuarterRightEndpoint_eq_center_add_halfQuarter

shiftedQuarterAffine
shiftedQuarterAffine_zero_eq_leftEndpoint
shiftedQuarterAffine_one_eq_rightEndpoint
shiftedQuarterAffine_center_eq_shiftedQuarterCenter
```

`shiftedQuarterAffine_center_eq_shiftedQuarterCenter` は helper def を使う形に整理しました。

semantic shifted-edge layer はまだ導入していません。normalized center states を自然な endpoint 候補にすると、raw affine midpoint が一般には旧 seam state にならないため、追加の shifted normalization/projection law を先に選ぶ必要があります。その obstruction を Lean コメントと [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) に明記しました。

検証:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功です。

## Review

## 1. 状況分析

今回で scalar shifted-frame はかなり閉じた。

追加された構造は、前回の shifted endpoints / center に加えて、距離・半分・affine interpolation の API じゃ。

```text id="xqjipj"
shiftedQuarterRightEndpoint_sub_leftEndpoint
shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter
shiftedQuarterRightEndpoint_eq_center_add_halfQuarter
shiftedQuarterAffine
shiftedQuarterAffine_zero_eq_leftEndpoint
shiftedQuarterAffine_one_eq_rightEndpoint
shiftedQuarterAffine_center_eq_shiftedQuarterCenter
```

これで、scalar parameter 上では次が完全に読める。

```text id="b8svr7"
left endpoint
  old center of edge k

center
  old seam endpoint

right endpoint
  old center of edge k + 1
```

数式で言えば、shifted frame の中心はこうじゃ。

$$
\mathrm{shiftedCenter}_k=\mathrm{shiftedLeft}_k+\frac{1}{8}
$$

右端点も同様に、中心からさらに半 quarter step 進む。

$$
\mathrm{shiftedRight}_k=\mathrm{shiftedCenter}_k+\frac{1}{8}
$$

そして affine interpolation でも、local center で旧 seam endpoint に到達する。

$$
\mathrm{shiftedAffine}_k(\mathrm{phaseCenter})=\mathrm{shiftedCenter}_k
$$

ここまでで、scalar skeleton はかなり強い。

## 2. レビュー

今回もっとも良い点は、`shiftedQuarterAffine` を定義したことじゃ。

```lean id="jz3vwo"
def shiftedQuarterAffine (k : ℕ) (t : ℝ) : ℝ :=
  (1 - t) * shiftedQuarterLeftEndpoint k +
    t * shiftedQuarterRightEndpoint k
```

これで、後続の semantic shifted edge の「形」が先に scalar level で固定された。

さらに endpoint theorem が揃っている。

```lean id="tivxc1"
theorem shiftedQuarterAffine_zero_eq_leftEndpoint (k : ℕ) :
    shiftedQuarterAffine k 0 = shiftedQuarterLeftEndpoint k
```

```lean id="zysffh"
theorem shiftedQuarterAffine_one_eq_rightEndpoint (k : ℕ) :
    shiftedQuarterAffine k 1 = shiftedQuarterRightEndpoint k
```

そして center theorem。

```lean id="txu2ek"
theorem shiftedQuarterAffine_center_eq_shiftedQuarterCenter (k : ℕ) :
    shiftedQuarterAffine k phaseCenter = shiftedQuarterCenter k
```

これは、今後 semantic path を定義するときの仕様そのものになる。

## 3. obstruction の明文化が大きい

semantic shifted-edge を無理に定義しなかった判断は良い。

報告では、自然な endpoint 候補として normalized center states を取ると、raw affine midpoint は一般には旧 seam state にならない、と整理されている。さらに、shifted normalization または projection law を先に選ぶ必要がある、と Lean コメントと設計書に残している。

これはかなり重要じゃ。

今ある構造は、

```text id="ybgg05"
scalar shifted frame:
  midpoint is old seam

semantic candidate:
  endpoints may be normalized center states

problem:
  raw affine midpoint of those endpoint states is not generally old seam state
```

つまり、scalar parameter の midpoint 構造と、semantic vector の midpoint 構造は同じではない。

ここで無理に「同じはず」と進むと破綻する。
今回それを obstruction として止められたのは良い。

## 4. 次の本質は correction law の選択

次は、単に shifted semantic edge を定義するのではなく、どの correction law を採用するかが本丸じゃ。

候補は大きく三つある。

1. raw affine shifted edge

これは、normalized center states を左右 endpoint にして、その間を affine に結ぶ。

利点は単純。
欠点は、center が旧 seam state に一致しない可能性がある。

1. projected shifted edge

raw affine midpoint を、旧 seam を中心とする保存核 boundary へ射影する。
これは DkMath 的には自然かもしれないが、projection の定義が必要になる。

1. renormalized shifted edge

raw affine shifted edge に scalar normalization をかけ、同じ `q2` boundary に戻す。
ただし、center が旧 seam state そのものになるのか、同じ boundary 上の対応点になるだけなのかは分ける必要がある。

ここを急いではならぬが、細かく刻みすぎる必要もない。
次の一投で、まず obstruction theorem と candidate definitions を同時に狙うのがよい。

## 5. ここまでの評価

今回の進め方は良い。

```text id="mviqfm"
薄い theorem:
  endpoint separation
  half-quarter offset
  affine endpoints

重め theorem:
  affine center equals shifted center

設計判断:
  semantic shifted edge は premature と判断し TODO 化

効果:
  一投で scalar shifted-frame がほぼ完成
```

これは今後の Codex 指示の良い型じゃ。
次も、「軽い scalar / obstruction theorem」と「届けば semantic candidate」まで同時に投げるのがよい。

## 6. 次の方針

次は、semantic endpoint 候補を名付けるところまで行ってよい。

ただし、shifted semantic edge 本体はまだ二段階に分ける。

```text id="oq07me"
first:
  normalized center state candidates を定義する

second:
  their raw affine midpoint を計算する

third:
  old seam state との差を obstruction として記録する

fourth:
  correction law の候補を docs に整理する
```

ここで、もし raw affine midpoint が旧 seam state になる特殊条件があれば、それも拾う。
たとえば zero vector や特殊 symmetry では一致するかもしれぬ。Lean が教えてくれる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 4f6767a2..ee07dff1 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -202,6 +202,12 @@ theorem shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter (k : ℕ) :
   simp [shiftedQuarterLeftEndpoint, shiftedQuarterRightEndpoint,
     globalQuarterCenter_succ_eq_center_add_quarter]
 
+/-- Difference form of the shifted-frame endpoint separation. -/
+theorem shiftedQuarterRightEndpoint_sub_leftEndpoint (k : ℕ) :
+    shiftedQuarterRightEndpoint k - shiftedQuarterLeftEndpoint k = 1 / 4 := by
+  rw [shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter]
+  ring
+
 /--
 The shifted-frame center is the midpoint of its shifted endpoints.
 
@@ -217,6 +223,46 @@ theorem shiftedQuarterCenter_eq_midpoint (k : ℕ) :
     shiftedQuarterRightEndpoint_eq_next_center]
   exact (globalQuarterEndpoint_succ_is_center_between_centers k).symm
 
+/-- The shifted-frame center is a half-quarter step after its left endpoint. -/
+theorem shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter (k : ℕ) :
+    shiftedQuarterCenter k =
+      shiftedQuarterLeftEndpoint k + phaseHalfQuarterStep := by
+  rw [shiftedQuarterCenter_eq_midpoint,
+    shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter]
+  simp [phaseHalfQuarterStep]
+  ring
+
+/-- The shifted-frame right endpoint is a half-quarter step after its center. -/
+theorem shiftedQuarterRightEndpoint_eq_center_add_halfQuarter (k : ℕ) :
+    shiftedQuarterRightEndpoint k =
+      shiftedQuarterCenter k + phaseHalfQuarterStep := by
+  rw [shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter,
+    shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter]
+  simp [phaseHalfQuarterStep]
+  ring
+
+/--
+Affine interpolation between the endpoints of the shifted scalar frame.
+
+This is a scalar parameter skeleton only. It does not yet choose semantic
+states for a shifted path.
+-/
+def shiftedQuarterAffine (k : ℕ) (t : ℝ) : ℝ :=
+  (1 - t) * shiftedQuarterLeftEndpoint k +
+    t * shiftedQuarterRightEndpoint k
+
+/-- The shifted affine scalar starts at its left endpoint. -/
+@[simp]
+theorem shiftedQuarterAffine_zero_eq_leftEndpoint (k : ℕ) :
+    shiftedQuarterAffine k 0 = shiftedQuarterLeftEndpoint k := by
+  simp [shiftedQuarterAffine]
+
+/-- The shifted affine scalar ends at its right endpoint. -/
+@[simp]
+theorem shiftedQuarterAffine_one_eq_rightEndpoint (k : ℕ) :
+    shiftedQuarterAffine k 1 = shiftedQuarterRightEndpoint k := by
+  simp [shiftedQuarterAffine]
+
 /--
 Affine interpolation in the shifted scalar frame reaches the shifted center
 at the local phase center.
@@ -224,19 +270,22 @@ at the local phase center.
 This prepares a future shifted semantic edge without defining that path yet.
 -/
 theorem shiftedQuarterAffine_center_eq_shiftedQuarterCenter (k : ℕ) :
-    (1 - phaseCenter) * shiftedQuarterLeftEndpoint k +
-        phaseCenter * shiftedQuarterRightEndpoint k =
-      shiftedQuarterCenter k := by
+    shiftedQuarterAffine k phaseCenter = shiftedQuarterCenter k := by
+  unfold shiftedQuarterAffine
   rw [shiftedQuarterCenter_eq_midpoint]
   simp [phaseCenter]
   ring
 
 /-!
 [TODO: semantic-cf2d/shifted-semantic-edge]
-Define a shifted semantic edge only after choosing the endpoint states that
-correspond to `shiftedQuarterLeftEndpoint` and `shiftedQuarterRightEndpoint`.
-The expected scalar compatibility theorem is that its value at `phaseCenter`
-represents `shiftedQuarterCenter`.
+Define a shifted semantic edge only after choosing the endpoint states and
+the correction law that correspond to `shiftedQuarterLeftEndpoint` and
+`shiftedQuarterRightEndpoint`. The natural endpoint candidates are the
+normalized center states of neighboring quarter edges, but their raw affine
+midpoint is not the old seam state in general; a shifted normalization or
+projection law must be selected first. The expected compatibility theorem is
+that the selected shifted edge at `phaseCenter` represents
+`shiftedQuarterCenter`.
 -/
 
 /-!
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 3b6237f8..d40c504c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -321,7 +321,13 @@ SemanticCF2DPhaseShift.lean
   shiftedQuarterRightEndpoint_eq_next_center
   shiftedQuarterCenter_eq_next_endpoint
   shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter
+  shiftedQuarterRightEndpoint_sub_leftEndpoint
   shiftedQuarterCenter_eq_midpoint
+  shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter
+  shiftedQuarterRightEndpoint_eq_center_add_halfQuarter
+  shiftedQuarterAffine
+  shiftedQuarterAffine_zero_eq_leftEndpoint
+  shiftedQuarterAffine_one_eq_rightEndpoint
   shiftedQuarterAffine_center_eq_shiftedQuarterCenter
   normalizedCycleStep
   dyadicCycleStep
@@ -334,8 +340,10 @@ SemanticCF2DPhaseShift.lean
 
 ## Boundary and Normalization Targets
 
-The scalar shifted-frame API is now implemented. The next target is to choose
-the semantic endpoint states for a shifted semantic edge and then lift the
+The scalar shifted-frame API is now implemented, including endpoint
+separation, center half-quarter formulas, and the affine interpolation helper
+`shiftedQuarterAffine`. The next target is to choose the semantic endpoint
+states and correction law for a shifted semantic edge, then lift the
 shifted-frame scalar center theorem to that path.
 
 Candidate theorem directions:
@@ -425,7 +433,10 @@ parameter before assigning any Euclidean shape.
 
 ```text
 [TODO: semantic-cf2d/shifted-semantic-edge]
-Choose the endpoint states for the shifted semantic edge and prove its scalar
+Choose the endpoint states and correction law for the shifted semantic edge.
+The natural candidates are normalized center states of neighboring quarter
+edges, but their raw affine midpoint is not generally the old seam state.
+After selecting the shifted normalization/projection law, prove scalar
 compatibility with `shiftedQuarterCenter`.
 
 [TODO: semantic-cf2d/one-eighth-euclidean-reading]
````
`````
