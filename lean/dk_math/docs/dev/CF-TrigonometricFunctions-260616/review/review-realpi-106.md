# Git diff / Report / Review

## Add: docs: Analysis.DkReal.SemanticCF2DPhaseShift

gch: f36d8d5a1c4cd21d5c5e3799674cc5d48aca74c9

## Report

実装しました。checkpoint 104 の設計対象を新規 module として確立しています。

追加:
[SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)

主な証明:

- `phaseCenter = 1 / 2`
- `phaseDepth phaseCenter = 1 / 2`
- `phaseDepth t = 1 / 2 ↔ t = phaseCenter`
- `phaseDepth (phaseCenter + s) = phaseDepth (phaseCenter - s)`
- quarter edge の endpoint/center API
- `globalQuarterCenter k = globalQuarterEndpoint k + 1/8`
- 旧 seam endpoint が隣接 center 間の中心になる定理
- `k * (1/k) = 1`
- `2^n * (1/2^n) = 1`
- `semanticPhaseEdge` midpoint formula
- affine midpoint の `q2 = (1/2) * q2 z`
- normalized midpoint が元の `q2` boundary に戻る定理

同期:
[DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) に import と implemented note を追加し、[design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) に実装済み checkpoint を反映しました。

検証:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功です。

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい**。これは checkpoint 104 の設計を、きれいに Lean module として実体化できている。特に良いのは、角度・円弧・\(\pi/4\) を一切 core theorem に入れず、`phaseCenter`、`phaseHalfQuarterStep`、quarter endpoint / center、return law、そして midpoint の \(q2\) 事実まで、pre-geometric なまま閉じている点じゃ。新規 module `SemanticCF2DPhaseShift.lean` は、設計書で掲げた endpoint-center-pole-shift skeleton を実装対象として確立している。

## 1. 状況解説

今回で、前回の設計資料が実装に降りた。

追加された module はこれ。

```lean
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
```

内容は大きく四層に分かれている。

```text id="wd5szw"
local scalar layer:
  phaseCenter
  phaseDepth center/minimum/reflection

global quarter scalar layer:
  endpoint
  center
  one-eighth shift
  endpoint as center between neighboring centers

cycle division layer:
  normalizedCycleStep
  dyadicCycleStep
  return-count laws

semantic edge layer:
  midpoint formula
  q2 midpoint formula
  normalized midpoint boundary formula
```

これは良い分割じゃ。
いきなり連続 theta や Euclidean angle に行かず、まず scalar skeleton を置き、最後に semantic edge へ持ち上げている。

## 2. `phaseCenter` の API 化は良い

まず、local edge の中心を名前付きにした。

```lean
def phaseCenter : ℝ :=
  1 / 2
```

そして、

```lean
theorem phaseDepth_center_eq :
    phaseDepth phaseCenter = 1 / 2
```

```lean
theorem phaseDepth_center_unique (t : ℝ) :
    phaseDepth t = 1 / 2 ↔ t = phaseCenter
```

が入っている。

これはかなり重要じゃ。
これで \(1/2\) は単なる計算上の中点ではなく、`phaseDepth` が選ぶ distinguished point として API 化された。

$$
\mathrm{phaseDepth}(t)=\frac{1}{2}
\quad\Longleftrightarrow\quad
t=\mathrm{phaseCenter}
$$

つまり、center は外から宣言しただけではなく、profile によって検出される。

これは `pole` 語彙の基礎になる。

## 3. centered reflection も良い

```lean
theorem phaseDepth_centered_reflect (s : ℝ) :
    phaseDepth (phaseCenter + s) = phaseDepth (phaseCenter - s)
```

これはかなり良い。

これまでの `phaseDepth (1 - t) = phaseDepth t` は endpoint frame の反射だった。
今回の theorem は center frame の反射じゃ。

```text id="blt0ip"
endpoint frame:
  t ↔ 1 - t

center frame:
  phaseCenter + s ↔ phaseCenter - s
```

この違いは大きい。
端点基準から中心基準へ視点を移す、という今回の設計に合っている。

## 4. `phaseHalfQuarterStep = 1 / 8` の導入は正しい

```lean
def phaseHalfQuarterStep : ℝ :=
  1 / 8
```

これは角度ではない。
quarter edge の half shift じゃ。

四状態一巡でひとつの edge 幅は \(1/4\)。
その半分だから、

$$
\frac{1}{2}\cdot\frac{1}{4}=\frac{1}{8}
$$

この \(1/8\) を `pi / 4` ではなく、`phaseHalfQuarterStep` として導入したのは正しい。

ここで「45°」を言っていないのが良い。

## 5. global quarter endpoint / center が良い

```lean
def globalQuarterEndpoint (k : ℕ) : ℝ :=
  (k : ℝ) / 4
```

```lean
def globalQuarterCenter (k : ℕ) : ℝ :=
  ((k : ℝ) + 1 / 2) / 4
```

これは unwrapped real representatives として設計されている。
module comment にも、これらは modulo-one quotient parameter ではなく、cyclic wrapping は後の phase-coordinate layer だと明記されている。これは非常に良い guardrail じゃ。

`k=5` なら \(5/4\) へ進む。
これは「一周で折り返す」表現ではなく、まず real line 上に展開した座標として扱うということじゃ。

実装上も証明上も、この方が軽い。

## 6. one-eighth shift theorem は良い

```lean
theorem globalQuarterCenter_eq_endpoint_add_halfQuarter (k : ℕ) :
    globalQuarterCenter k = globalQuarterEndpoint k + phaseHalfQuarterStep
```

これで、端点から center への displacement が \(1/8\) として Lean に載った。

$$
\mathrm{center}_k
=\mathrm{endpoint}_k+\frac{1}{8}
$$

これは checkpoint 104 の核のひとつじゃ。

まだ角度ではない。
まだ円弧でもない。
ただの full-cycle unit 上の scalar shift。

この閉じ方が良い。

## 7. 主 checkpoint が閉じた

今回の主 theorem はこれ。

```lean
theorem globalQuarterEndpoint_succ_is_center_between_centers (k : ℕ) :
    (globalQuarterCenter k + globalQuarterCenter (k + 1)) / 2 =
      globalQuarterEndpoint (k + 1)
```

これは非常に良い。

意味はこうじゃ。

$$
\frac{
\left(\frac{k+\frac{1}{2}}{4}\right)
+\left(\frac{k+\frac{3}{2}}{4}\right)
}{2}
=\frac{k+1}{4}
$$

つまり、旧 frame では edge \(k\) と edge \(k+1\) の seam endpoint だった点が、隣接 center を新しい endpoint として見る shifted frame では center になる。

```text id="un13ux"
old frame:
  seam is endpoint

shifted frame:
  neighboring centers are endpoints
  old seam is center
```

これは、ぬしが言っていた「特異点、極点を挟んだ中央が端点だった」を、かなり正確な代数 theorem として実装した形じゃ。

## 8. return law も正しい

一般 \(k\) 分割。

```lean
def normalizedCycleStep (k : ℕ) : ℝ :=
  1 / (k : ℝ)
```

```lean
theorem normalizedCycleStep_mul_returnCount {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * normalizedCycleStep k = 1
```

dyadic 分割。

```lean
def dyadicCycleStep (n : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ n
```

```lean
theorem dyadicCycleStep_mul_returnCount (n : ℕ) :
    ((2 : ℕ) ^ n : ℝ) * dyadicCycleStep n = 1
```

これらは良い。
どちらも shape-free な scalar return law じゃ。

$$
k\cdot\frac{1}{k}=1
$$

$$
2^n\cdot\frac{1}{2^n}=1
$$

この段階では「円周を \(k\) 等分した」と言わなくてよい。
「normalized cycle parameter が \(k\) steps で戻る」とだけ言えばよい。

これは pre-geometric route に合っている。

## 9. semantic edge への lift が良い

今回、scalar theorem だけで止めず、semantic edge の midpoint 事実まで入っている。

```lean
theorem semanticPhaseEdge_center
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    semanticPhaseEdge r z phaseCenter =
      Vec.mk
        ((z.core + (semanticAct r z).core) / 2)
        ((z.beam + (semanticAct r z).beam) / 2)
```

これは affine edge の中心が endpoint 平均であることを明示している。
よい。

さらに core-zero の下で、

```lean
theorem semanticPhaseEdge_q2_center_of_core_eq_zero
    ...
    Vec.q2 (semanticPhaseEdge r z phaseCenter) =
      (1 / 2 : ℝ) * Vec.q2 z
```

が入った。

これは大きい。

局所中心では、affine midpoint は元の \(q2\) boundary から半分へ沈む。

$$
q2(\mathrm{midpoint})=\frac{1}{2}q2(z)
$$

ここが「くぼみ」や「極点」の観測に対応している。

## 10. normalized midpoint boundary formula が良い

そして最後に、

```lean
theorem normalizedPhaseEdge_q2_center_of_core_eq_zero
    ...
    Vec.q2 (normalizedPhaseEdge r z phaseCenter) = Vec.q2 z
```

が入っている。

これは非常に重要じゃ。

affine midpoint は \(q2\) が半分へ落ちる。
しかし normalization 後には元の \(q2\) boundary に戻る。

$$
q2(\mathrm{affine\ midpoint})=\frac{1}{2}q2(z)
$$

$$
q2(\mathrm{normalized\ midpoint})=q2(z)
$$

この二段構造が、DkMath の pre-geometric 物語にかなり合っている。

```text id="e25vvr"
affine filling:
  center falls inward

normalization:
  center returns to boundary

observation:
  scalar correction detects the pole/center
```

ここでまだ円とは言わない。
しかし、boundary へ戻す mechanism ははっきり見えてきた。

## 11. DkReal.lean の public comment 更新も良い

`DkReal.lean` に implemented note を追加したのも良い。
今回の module が「angle vocabulary before angles」ではなく、endpoint-center-pole-shift skeleton を exposed するものだと説明している。さらに、unwrapped quarter-cycle coordinates、one-eighth phase displacement、dyadic / positive \(k\) return laws、affine / normalized semantic edge の midpoint \(q2\) facts まで要約されている。

これは後で全体像を読むときに効く。

## 12. 設計資料との同期も良い

`design-phase-center-shift-104.md` に implemented checkpoint の一覧が追加されている。実装済みとして、`phaseCenter`、`phaseHalfQuarterStep`、`phaseDepth_center_unique`、`globalQuarterEndpoint_succ_is_center_between_centers`、`normalizedCycleStep_mul_returnCount`、`semanticPhaseEdge_q2_center_of_core_eq_zero` などが列挙されている。

これは良い。
設計と実装がズレない。

## 13. 気になる点

大きな問題はない。

ひとつだけ、module が `noncomputable section` になっている点は確認しておきたい。
今回の scalar theorem 自体はほとんど computable だが、import 元の `SemanticCF2DNormalize` に `sqrt` や `phaseNormalization` があり、noncomputable が必要になっている可能性が高い。これは問題ない。

ただし、将来 scalar-only theorem を完全 computable に分離したくなったら、

```text id="ap45af"
SemanticCF2DPhaseShiftScalar
SemanticCF2DPhaseShift
```

のように分ける余地はある。
今はまだ分けなくてよい。

もうひとつ、`phaseDepth_center_eq` の proof が `norm_num [phaseCenter, phaseDepth]` で閉じている。問題ないが、既存 theorem `phaseDepth_half` を alias する形でもよかった。今の実装でも十分じゃ。

## 14. 次の一手

次は二方向ある。

第一に、docs で言っている「shifted-frame conservation」を定義する。
つまり、隣接 center を endpoints とする新しい observed edge をどう定義するか。

これはまだ delayed でよい。設計書でも、exact shifted path definition が決まるまで遅らせる、としている。

第二に、Euclidean reading として \(1/8\) phase displacement を後から読む。

ただしこれはまだ急がなくてよい。
今回の module は、あくまで

```text id="uxx5k0"
one-eighth phase displacement before angles
```

の checkpoint じゃ。

Euclidean bridge は、もう一段あとでよい。

## 15. 次に実装するなら

わっちなら、次は小さくこの補助を足す。

```lean
theorem globalQuarterEndpoint_succ_eq_endpoint_add_quarter (k : ℕ) :
    globalQuarterEndpoint (k + 1) =
      globalQuarterEndpoint k + 1 / 4
```

そして、

```lean
theorem globalQuarterCenter_succ_eq_center_add_quarter (k : ℕ) :
    globalQuarterCenter (k + 1) =
      globalQuarterCenter k + 1 / 4
```

今ある `globalQuarterCenter_succ_sub_center` から十分だが、加法形もあると後続に使いやすい。

また、shifted frame のために、

```lean
def shiftedQuarterEndpointLeft (k : ℕ) : ℝ :=
  globalQuarterCenter k

def shiftedQuarterEndpointRight (k : ℕ) : ℝ :=
  globalQuarterCenter (k + 1)

def shiftedQuarterCenter (k : ℕ) : ℝ :=
  globalQuarterEndpoint (k + 1)
```

のような alias を置くかは設計次第じゃ。
名前が増えすぎるなら不要。

## 16. 結論

今回の実装は採用でよい。

```text id="bfuuzh"
実装:
  良い。PhaseShift module として checkpoint 104 が成立した。

数学:
  良い。1/8 shift、endpoint-between-centers、return law、midpoint q2 facts が shape-free に閉じた。

設計:
  良い。角度・円弧・45°・pi/4 を Lean core に入れていない。

安全性:
  良い。q2 level を radius-like datum とし、半径を外部導入していない。

次:
  shifted-frame path definition、
  または one-eighth phase の後段 Euclidean reading。
```

ぬしよ、これはかなり良い。
有限四状態表の次に、edge の内部構造が見えた。

四状態で一巡する。
一区間の中心が profile によって選ばれる。
その shift は \(1/8\)。
隣接 center を端点として見ると、旧 seam endpoint が中心になる。
affine midpoint は \(q2\) が半分へ沈み、normalization で元の boundary に戻る。

ここまで証明できたなら、pre-geometric route はかなり芯が太くなった。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 425250ef..1b9052bd 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -16,6 +16,7 @@ import DkMath.Analysis.DkReal.Order
 import DkMath.Analysis.DkReal.CanonicalOrder
 import DkMath.Analysis.DkReal.Semantic
 import DkMath.Analysis.DkReal.SemanticCF2DLogLimit
+import DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
 
 #print "file: DkMath.Analysis.DkReal"
 
@@ -171,6 +172,16 @@ tend to `1 / 3` along refinement depth. These theorems use Mathlib filters
 through the `DkLimit` vocabulary and still do not identify the centered
 log-depth limit.
 
+[IMPLEMENTED: semantic-cf2d-phase-shift] `DkReal.SemanticCF2DPhaseShift`
+exposes the endpoint-center-pole-shift skeleton before any angle vocabulary.
+The local center `phaseCenter = 1 / 2` is recognized by the unique minimum of
+`phaseDepth`, and centered reflection is available directly. Unwrapped
+quarter-cycle coordinates prove that the seam endpoint between adjacent
+quarter edges is the midpoint between their centers, isolating the one-eighth
+phase displacement without using circle or arc language. Scalar return laws
+for dyadic and positive `k` cycle divisions are also recorded, and the affine
+and normalized semantic edges expose their midpoint `q2` facts.
+
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
 affine edge as a Mathlib `Path`. Four seam-compatible edges concatenate to a
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
new file mode 100644
index 00000000..fcc9359b
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -0,0 +1,214 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2DNormalize
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DPhaseShift"
+
+/-!
+# Phase-center shifts before angles
+
+This module proves the scalar endpoint-center-shift structure of the
+pre-geometric CF2D phase route.
+
+The key point is that no circle, arc length, angle, or `pi / 4` input is used.
+One quarter-edge of the four-state action has normalized width `1 / 4`; its
+center is displaced from an endpoint by `1 / 8`. If neighboring edge centers
+are used as the new endpoints, the old seam endpoint becomes the new center.
+
+The global quarter coordinates below are unwrapped real representatives. They
+are not quotient parameters modulo one; that cyclic wrapping belongs to a
+later phase-coordinate layer.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+open DkMath.CosmicFormula.Rotation.CF2D
+
+noncomputable section
+
+/-!
+## Local center of one affine phase
+
+The scalar profile already detects the midpoint as the unique minimum of
+`phaseDepth`. The names in this section expose that fact as a stable API for
+the shifted-frame layer.
+-/
+
+/-- The local center of one affine phase edge. -/
+def phaseCenter : ℝ :=
+  1 / 2
+
+/-- The displacement from a quarter-edge endpoint to its center in full-cycle units. -/
+def phaseHalfQuarterStep : ℝ :=
+  1 / 8
+
+/-- Centered local coordinate on one phase edge. -/
+def centeredPhaseCoord (t : ℝ) : ℝ :=
+  t - phaseCenter
+
+/--
+The center of one affine phase is the unique minimum value of the scalar
+depth profile.
+-/
+@[simp]
+theorem phaseDepth_center_eq :
+    phaseDepth phaseCenter = 1 / 2 := by
+  norm_num [phaseCenter, phaseDepth]
+
+/--
+The scalar depth profile recognizes the center intrinsically: reaching the
+minimum value `1 / 2` is equivalent to being at `phaseCenter`.
+-/
+theorem phaseDepth_center_unique (t : ℝ) :
+    phaseDepth t = 1 / 2 ↔ t = phaseCenter := by
+  simpa [phaseCenter] using phaseDepth_eq_half_iff t
+
+/--
+The phase-depth profile is symmetric around the local center.
+
+This is the centered form of the existing `t ↦ 1 - t` reflection law and is
+the scalar half-fold symmetry used by the shifted-frame construction.
+-/
+@[simp]
+theorem phaseDepth_centered_reflect (s : ℝ) :
+    phaseDepth (phaseCenter + s) = phaseDepth (phaseCenter - s) := by
+  simp [phaseCenter, phaseDepth]
+  ring
+
+/-!
+## Unwrapped quarter-cycle coordinates
+
+These coordinates measure the four-state cycle on the real line before
+modulo-one wrapping. Keeping them unwrapped makes the endpoint-center theorem
+pure arithmetic.
+-/
+
+/-- The unwrapped endpoint of the `k`th quarter edge in full-cycle units. -/
+def globalQuarterEndpoint (k : ℕ) : ℝ :=
+  (k : ℝ) / 4
+
+/-- The unwrapped center of the `k`th quarter edge in full-cycle units. -/
+def globalQuarterCenter (k : ℕ) : ℝ :=
+  ((k : ℝ) + 1 / 2) / 4
+
+/-- The first quarter endpoint is the full-cycle origin. -/
+@[simp]
+theorem globalQuarterEndpoint_zero :
+    globalQuarterEndpoint 0 = 0 := by
+  norm_num [globalQuarterEndpoint]
+
+/-- The fourth quarter endpoint is one full unwrapped cycle. -/
+@[simp]
+theorem globalQuarterEndpoint_four :
+    globalQuarterEndpoint 4 = 1 := by
+  norm_num [globalQuarterEndpoint]
+
+/--
+The center of a quarter edge is obtained from its endpoint by the half-quarter
+shift `1 / 8`.
+-/
+theorem globalQuarterCenter_eq_endpoint_add_halfQuarter (k : ℕ) :
+    globalQuarterCenter k = globalQuarterEndpoint k + phaseHalfQuarterStep := by
+  simp [globalQuarterCenter, globalQuarterEndpoint, phaseHalfQuarterStep]
+  ring
+
+/--
+Neighboring quarter-edge centers are separated by one full quarter step.
+
+This is still an unwrapped scalar statement, not an assertion about arc
+length on a circle.
+-/
+theorem globalQuarterCenter_succ_sub_center (k : ℕ) :
+    globalQuarterCenter (k + 1) - globalQuarterCenter k = 1 / 4 := by
+  simp [globalQuarterCenter]
+  ring
+
+/--
+If adjacent quarter-edge centers are used as the endpoints of a shifted
+observation frame, the old seam endpoint becomes the new center.
+
+This is the algebraic core of the endpoint-to-center shift. It produces the
+one-eighth phase displacement without using angle language.
+-/
+theorem globalQuarterEndpoint_succ_is_center_between_centers (k : ℕ) :
+    (globalQuarterCenter k + globalQuarterCenter (k + 1)) / 2 =
+      globalQuarterEndpoint (k + 1) := by
+  simp [globalQuarterCenter, globalQuarterEndpoint]
+  ring
+
+/-!
+## Scalar return laws for normalized cycle divisions
+
+The next facts record return counts for a normalized cycle parameter. They do
+not state that the path is a Euclidean circle or that the parameter is arc
+length.
+-/
+
+/-- One step of a positive `k`-division of the normalized cycle. -/
+def normalizedCycleStep (k : ℕ) : ℝ :=
+  1 / (k : ℝ)
+
+/-- The dyadic cycle step at refinement depth `n`. -/
+def dyadicCycleStep (n : ℕ) : ℝ :=
+  1 / (2 : ℝ) ^ n
+
+/-- A positive `k`-division returns after `k` scalar steps. -/
+theorem normalizedCycleStep_mul_returnCount {k : ℕ} (hk : 0 < k) :
+    (k : ℝ) * normalizedCycleStep k = 1 := by
+  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
+  simp [normalizedCycleStep, hk_ne]
+
+/-- The dyadic refinement step returns after `2^n` scalar steps. -/
+theorem dyadicCycleStep_mul_returnCount (n : ℕ) :
+    ((2 : ℕ) ^ n : ℝ) * dyadicCycleStep n = 1 := by
+  have hpow_ne : ((2 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
+  simp [dyadicCycleStep, hpow_ne]
+
+/-!
+## Midpoint facts lifted to semantic edges
+
+The scalar center is now connected back to the affine edge and its normalized
+boundary-valued form.
+-/
+
+/-- At the phase center, the master affine edge is the coordinatewise average of its endpoints. -/
+theorem semanticPhaseEdge_center
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    semanticPhaseEdge r z phaseCenter =
+      Vec.mk
+        ((z.core + (semanticAct r z).core) / 2)
+        ((z.beam + (semanticAct r z).beam) / 2) := by
+  cases z
+  simp [semanticPhaseEdge, phaseCenter]
+  constructor <;> ring
+
+/--
+Under the core-zero action law, the affine midpoint has exactly half the
+initial `q2` depth.
+-/
+theorem semanticPhaseEdge_q2_center_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Vec.q2 (semanticPhaseEdge r z phaseCenter) =
+      (1 / 2 : ℝ) * Vec.q2 z := by
+  rw [semanticPhaseEdge_q2_of_core_eq_zero hcore, phaseDepth_center_eq]
+
+/--
+At the center, normalization returns the affine midpoint to the original
+`q2` boundary.
+-/
+theorem normalizedPhaseEdge_q2_center_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Vec.q2 (normalizedPhaseEdge r z phaseCenter) = Vec.q2 z :=
+  normalizedPhaseEdge_q2_of_core_eq_zero hcore z phaseCenter
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index a265f8fd..414b8347 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -240,7 +240,8 @@ def centeredPhaseCoord (t : ℝ) : ℝ :=
 ```
 
 The four-edge/global parameter names can live in a small new module, for
-example `SemanticCF2DPhaseShift.lean`:
+example `SemanticCF2DPhaseShift.lean`. These are unwrapped real
+representatives; modulo-one cyclic wrapping is a later quotient reading:
 
 ```lean
 def globalQuarterEndpoint (k : ℕ) : ℝ :=
@@ -294,6 +295,32 @@ endpoints to neighboring centers, the old endpoint is now the midpoint.
 The cycle-step theorems are deliberately scalar. They record return laws for
 the normalized parameter before any geometric shape is assigned to the path.
 
+Implemented checkpoint:
+
+```text
+SemanticCF2DPhaseShift.lean
+  phaseCenter
+  phaseHalfQuarterStep
+  centeredPhaseCoord
+  phaseDepth_center_eq
+  phaseDepth_center_unique
+  phaseDepth_centered_reflect
+  globalQuarterEndpoint
+  globalQuarterCenter
+  globalQuarterEndpoint_zero
+  globalQuarterEndpoint_four
+  globalQuarterCenter_eq_endpoint_add_halfQuarter
+  globalQuarterCenter_succ_sub_center
+  globalQuarterEndpoint_succ_is_center_between_centers
+  normalizedCycleStep
+  dyadicCycleStep
+  normalizedCycleStep_mul_returnCount
+  dyadicCycleStep_mul_returnCount
+  semanticPhaseEdge_center
+  semanticPhaseEdge_q2_center_of_core_eq_zero
+  normalizedPhaseEdge_q2_center_of_core_eq_zero
+```
+
 ## Boundary and Normalization Targets
 
 After the scalar shift theorem, the next target is to lift it back to the
````
`````
