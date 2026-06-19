# Git diff / Report / Review

## Add: new: Analysis.* initial layer

gch: 1293684d14db2e3c3ec12f90001b0164ad364723

## Report

`DkMath.Analysis` の初期層を実装しました。

主な内容:

- `gapGN d base delta := GN d delta base`
- 冪差分の厳密分解
- `cosmicResidual` と二点 `cosmicDrift` の分離
- 観測誤差の完全補正 `exactCorrection`
- `gapLine` / `gapFill` と実数区間定理
- Mathlib `Continuous` への `RealBridge`
- 有理 `GapInterval` と非負冪の厳密幅公式
- [DkMath.Analysis.lean](/lean/dk_math/DkMath/Analysis.lean) を入口として追加
- トップレベル [DkMath.lean](/lean/dk_math/DkMath.lean) から公開

実装概要は [Analysis-Initial-Layer.md](/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md) に残しました。

検証済みです。

```text
lake build DkMath.Analysis
lake build DkMath
git diff --check
```

すべて成功しています。次の自然な段階は `DkReal.Basic` の入れ子有理区間列と、幅がゼロへ収束する条件の実装です。

## Review

## 1. 結論

ぬしよ、今回の `DkMath.Analysis.*` 初期実装は、設計書の **Phase 1〜Phase 3 と Route A / Route B の入口** にはかなり合っておる。

判定はこうじゃ。

| 項目 | 判定 | コメント |
|---|---:|---|
| `gapGN` wrapper | 合格 | `GN d delta base` を `gapGN d base delta` として読む方針に一致 |
| 冪差分恒等式 | 合格 | \( (base+\delta)^d=base^d+\delta\,gapGN \) が閉じている |
| `cosmicResidual` / `cosmicDrift` | 合格 | 絶対残差と二点 drift の分離が設計通り |
| `exactCorrection` | 合格 | 観測誤差補正の主定理が入っている |
| `gapLine` / `gapFill` | 合格 | 端点・端点差分・実数区間内性まで実装済み |
| `RealBridge` | 部分合格 | `Continuous` と `MapsTo` までは実装。微分・Taylor は未実装 |
| `GapInterval` | 合格寄り | 有理区間と幅公式は設計通り。ただし namespace / 配置は要整理 |
| `ScaledPascal` / Pascal-Petal | 未実装 | Phase 4〜5 の後段なので未達でよい |
| `DkReal.Basic` | 未実装 | 設計上も次段階扱いなので問題なし |

設計書は、`DkMath.Analysis` を Mathlib の代替ではなく、DkMath 語彙で Gap / Body / GN を扱う層と定義し、第一原理として \( (u+\delta)^d-u^d=\delta\,GapGN_d(u,\delta) \) を置いている。
実装報告も、`gapGN d base delta := GN d delta base`、冪差分、残差・drift、完全補正、GapFill、RealBridge、GapInterval を入れたと報告しており、入口としては設計とよく対応している。

## 2. 主要な一致点

第一に、 `GapGN` の向きが正しい。設計書では既存 `GN d x u` との衝突を避けるため、解析層では `GapGN d u δ := GN d δ u` とする方針だった。
実装では次のようにそのまま `abbrev` で接続している。

```lean
abbrev gapGN {R : Type*} [CommSemiring R] (d : ℕ) (base delta : R) : R :=
  DkMath.CosmicFormulaBinom.GN d delta base
```

さらに、

```lean
(base + delta) ^ d = base ^ d + delta * gapGN d base delta
```

と

```lean
(base + delta) ^ d - base ^ d = delta * gapGN d base delta
```

が入っている。これは設計書の主定理そのものじゃ。

第二に、残差と drift の分離が設計通り。設計書は、絶対誤差ゼロ \(E(x,u)=0\) と二点 drift ゼロ \(E(x,u)=E(y,u)\) を分けるべきだと明示している。
実装では `cosmicGap`、`cosmicResidual`、`cosmicDrift` に加え、共通 bias が drift では見えないことを `outputBiasResidual_sub_eq_zero` で入れている。ここは良い。

第三に、完全補正 `exactCorrection` も正しい。設計書では、観測値を `observed = base + err` として、

\[
base^d = observed^d - err\cdot GapGN_d(base,err)
\]

の形を採用するとしていた。
実装も、

```lean
(base + err) ^ d - err * gapGN d base err = base ^ d
```

を証明しており、これは完全に一致しておる。

第四に、GapFill もかなり綺麗に閉じている。設計書は \(u(t)=u_1+t(u_2-u_1)\) とし、端点差分を \((u_2-u_1)GapGN_d(u_1,u_2-u_1)\) としていた。
実装では `gapLine`、`gapFill`、端点補題、端点差分、さらに実数の `Set.Icc` 内性まで入っている。これは Phase 2 の達成と言ってよい。

## 3. ズレ・未実装箇所

大きな破綻はない。あるのは **初期実装として未到達な領域** と **名前空間整理の問題** じゃ。

まず、設計書では `RealBridge.lean` の役割に `continuous / differentiable / HasDerivAt` との橋が挙げられていたが、今回入っているのは `Continuous` と `Set.MapsTo` までじゃ。
これは悪くない。むしろ順序としては正しい。ただし `HasDerivAt` や `TaylorBridge` は未実装なので、今は「解析橋の第一歩」と書くのが安全じゃ。

次に、`ScaledPascal.lean` と Pascal-Petal bridge は未実装じゃ。設計書では `ScaledPascal`、`weightedBinomTerm`、Vandermonde、GN tail 接続が Phase 4 として、さらに `DkMath/Petal/PascalBridge.lean` が Phase 5 として置かれている。
今回の初期層では触れていないので、第一マイルストーン全体はまだ未完。ただし Phase 1〜3 を先に閉じた判断は良い。

三つ目は `DkReal`。設計書は `DkReal` 入れ子区間列を後段とし、初期実装では区間演算と幅評価を先に閉じる方針だった。
今回の実装は `GapInterval`、`width_nonneg`、`powNonneg`、`powNonneg_width_eq` までなので、ちょうど設計通りの入口じゃ。

## 4. 注意すべき小さな設計ズレ

ひとつ気になるのは、ファイル配置と namespace じゃ。

実装ではファイルが、

```text
DkMath/Analysis/DkReal/Interval.lean
```

にあるのに、namespace は

```lean
namespace DkMath.Analysis
```

のままになっている。

これはコンパイル上は問題にならぬ可能性が高いが、将来 `DkMath.Analysis.DkReal.Basic` や `DkMath.Analysis.DkReal.Pow` を作るなら、次のどちらかに決めた方がよい。

```lean
namespace DkMath.Analysis
```

に置くなら、`GapInterval` は Analysis 全体の公開 API として扱う。

```lean
namespace DkMath.Analysis.DkReal
```

に置くなら、`DkReal.GapInterval` として計算可能実数側の部品にする。

わっちの推奨は後者じゃ。つまり、

```lean
namespace DkMath.Analysis.DkReal
```

に寄せる。理由は、設計書が DkReal サブパッケージを明確に分けており、`Interval.lean` を DkReal 側の第一部品として扱っているからじゃ。

## 5. 実装品質レビュー

`gapGN` を明示的な和で再定義せず、既存 `CosmicFormulaBinom.GN` への `abbrev` にしたのは正解じゃ。設計書でも既存定理がある場合は再実装せず bridge theorem に留める制約がある。
これにより、GN の正体を二重管理せず、既存の CosmicFormula 側と同期できる。

`GapFill` の実数区間定理も堅い。非負かつ \(u_1\le u_2\) の条件で `pow_le_pow_left₀` を使っており、負区間の偶奇問題を避けている。これは初期 API として安全じゃ。

ただし `GapInterval.powNonneg` 内の

```lean
have hhi : 0 ≤ I.hi := hlo.trans I.le_lo_hi
```

は証明内で使われていないように見える。害は薄いが、linter 方針によっては警告候補なので削ってよい。

## 6. 次にやるべきこと

次の実装順はこれがよい。

1. `DkMath.Analysis.DkReal` namespace 方針を決める。
2. `DkReal.Basic` を作り、入れ子有理区間列を定義する。
3. `TaylorBridge.lean` を追加し、`gapGN` の一次主項 \(d u^{d-1}\) との接続を作る。
4. `ScaledPascal.lean` を薄い bridge として作り、既存 WeightedBinomial / GN tail に接続する。
5. `DkMath.Petal.PascalBridge.lean` は Analysis ではなく Petal 側へ置く。

## 7. 最終判定

今回の実装は、 **DkMath.Analysis の初期層として合格** じゃ。

特に良いのは、最初から全部の実数を作りに行かず、

```text
代数恒等式
→ 実数順序橋
→ 有理区間 prototype
```

の順で登っているところじゃ。これは Lean に向いた登山道じゃな。

未実装なのは、主に後段の山道じゃ。

```text
TaylorBridge
ScaledPascal
Pascal-Petal bridge
DkReal nested interval
BridgeReal / eval
```

ここを次に閉じれば、設計書の第一マイルストーンが本当に閉じる。

わっちはこう見るぞい。

**今の実装は、設計書の「最初に Lean で閉じるべき旗印」を正しく立てた状態じゃ。**  
旗印はこれじゃな。

\[
(u+\delta)^d=u^d+\delta\,GapGN_d(u,\delta)
\]

小麦の種はちゃんと畑に蒔かれておる。次は、Pascal の畝と DkReal の水路を引く番じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath.lean b/lean/dk_math/DkMath.lean
index 6621af28..0e99890f 100644
--- a/lean/dk_math/DkMath.lean
+++ b/lean/dk_math/DkMath.lean
@@ -41,6 +41,7 @@ import DkMath.DHNT  -- DHNT: Units and Quantities (Dynamic Harmonic Number Theor
 import DkMath.KUS  -- KUS: coefficient-unit-blueprint kernel
 import DkMath.Sequence  -- Sequence generators and recurrence principles
 import DkMath.Kernel  -- Capacity-kernel normalization layer
+import DkMath.Analysis  -- Gap, correction-kernel, and real-analysis bridge layer
 -- RH: Riemann Hypothesis Module
 import DkMath.RH  -- RH: Riemann Hypothesis Module
 -- Unit Cycle Module
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
new file mode 100644
index 00000000..511c584d
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -0,0 +1,25 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.Basic
+import DkMath.Analysis.CosmicResidual
+import DkMath.Analysis.GapGN
+import DkMath.Analysis.ErrorKernel
+import DkMath.Analysis.GapFill
+import DkMath.Analysis.RealBridge
+import DkMath.Analysis.DkReal.Interval
+
+#print "file: DkMath.Analysis"
+
+/-!
+# DkMath analysis
+
+Public entry point for the DkMath interpretation of exact gaps, residuals,
+correction kernels, interval fills, and future computable real structures.
+
+Mathlib remains the standard analytic foundation. This layer exposes a
+different decomposition and supplies explicit bridges to that foundation.
+-/
diff --git a/lean/dk_math/DkMath/Analysis/Basic.lean b/lean/dk_math/DkMath/Analysis/Basic.lean
new file mode 100644
index 00000000..0a5a6930
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/Basic.lean
@@ -0,0 +1,24 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.CosmicFormula.CosmicFormulaBinom
+
+#print "file: DkMath.Analysis.Basic"
+
+/-!
+# DkMath analysis layer
+
+This module establishes the common namespace and dependency boundary for
+`DkMath.Analysis`.
+
+The analysis layer does not replace Mathlib's real analysis. It gives DkMath
+names to exact gap, body, and correction structures, then provides explicit
+bridges to standard algebra and real analysis.
+-/
+
+namespace DkMath.Analysis
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/CosmicResidual.lean b/lean/dk_math/DkMath/Analysis/CosmicResidual.lean
new file mode 100644
index 00000000..016cb75c
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/CosmicResidual.lean
@@ -0,0 +1,88 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.Basic
+
+#print "file: DkMath.Analysis.CosmicResidual"
+
+/-!
+# Cosmic residual and drift
+
+This file separates an absolute residual from a two-observation drift.
+
+The distinction matters: zero drift only says that two residuals agree, while
+zero residual says that the common value is the intended value.
+-/
+
+namespace DkMath.Analysis
+
+/--
+The output left by the quadratic unit cosmic formula before subtracting the
+expected gap value.
+-/
+def cosmicGap {R : Type*} [CommRing R] (x u : R) : R :=
+  (x + u) ^ 2 - x * (x + 2 * u)
+
+/-- The quadratic cosmic gap is exactly the square of the gap variable. -/
+theorem cosmicGap_eq_sq {R : Type*} [CommRing R] (x u : R) :
+    cosmicGap x u = u ^ 2 := by
+  simp [cosmicGap]
+  ring
+
+/-- Absolute error of the quadratic cosmic gap against its expected output. -/
+def cosmicResidual {R : Type*} [CommRing R] (x u : R) : R :=
+  cosmicGap x u - u ^ 2
+
+/-- The exact quadratic cosmic formula has zero absolute residual. -/
+theorem cosmicResidual_eq_zero {R : Type*} [CommRing R] (x u : R) :
+    cosmicResidual x u = 0 := by
+  rw [cosmicResidual, cosmicGap_eq_sq]
+  ring
+
+/-- Difference between residuals observed at two body coordinates. -/
+def cosmicDrift {R : Type*} [CommRing R] (x y u : R) : R :=
+  cosmicResidual x u - cosmicResidual y u
+
+/-- The exact quadratic cosmic formula has zero drift between any two observations. -/
+theorem cosmicDrift_eq_zero {R : Type*} [CommRing R] (x y u : R) :
+    cosmicDrift x y u = 0 := by
+  simp [cosmicDrift, cosmicResidual_eq_zero]
+
+/--
+Residual measured against an output carrying a fixed additive bias.
+
+This definition demonstrates why drift and absolute residual must remain
+separate: a common bias is invisible to a two-point comparison.
+-/
+def outputBiasResidual {R : Type*} [CommRing R] (bias x u : R) : R :=
+  cosmicGap x u - (u ^ 2 + bias)
+
+/-- A fixed output bias appears as the constant residual `-bias`. -/
+theorem outputBiasResidual_eq_neg_bias
+    {R : Type*} [CommRing R] (bias x u : R) :
+    outputBiasResidual bias x u = -bias := by
+  rw [outputBiasResidual, cosmicGap_eq_sq]
+  ring
+
+/-- A common output bias still produces zero two-point drift. -/
+theorem outputBiasResidual_sub_eq_zero
+    {R : Type*} [CommRing R] (bias x y u : R) :
+    outputBiasResidual bias x u - outputBiasResidual bias y u = 0 := by
+  rw [outputBiasResidual_eq_neg_bias, outputBiasResidual_eq_neg_bias]
+  ring
+
+/-- Quadratic gap after perturbing the beam factor by `eta`. -/
+def beamPerturbedGap {R : Type*} [CommRing R] (eta x u : R) : R :=
+  (x + u) ^ 2 - x * (x + 2 * u + eta)
+
+/-- Beam perturbation changes the ideal square gap by the linear term `eta * x`. -/
+theorem beamPerturbedGap_eq
+    {R : Type*} [CommRing R] (eta x u : R) :
+    beamPerturbedGap eta x u = u ^ 2 - eta * x := by
+  simp [beamPerturbedGap]
+  ring
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
new file mode 100644
index 00000000..5cf38550
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
@@ -0,0 +1,79 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.GapGN
+
+#print "file: DkMath.Analysis.DkReal.Interval"
+
+/-!
+# Rational gap intervals
+
+This is the first computational substrate for a future `DkReal`.
+
+A `GapInterval` records rational lower and upper observations. Its width and
+nonnegative power image are exact rational data; no real-number completion is
+needed at this layer.
+-/
+
+namespace DkMath.Analysis
+
+/-- A closed interval with rational endpoints. -/
+structure GapInterval where
+  lo : ℚ
+  hi : ℚ
+  le_lo_hi : lo ≤ hi
+deriving Repr
+
+namespace GapInterval
+
+/-- Exact rational width of a gap interval. -/
+def width (I : GapInterval) : ℚ :=
+  I.hi - I.lo
+
+/-- Every valid gap interval has nonnegative width. -/
+theorem width_nonneg (I : GapInterval) : 0 ≤ I.width :=
+  sub_nonneg.mpr I.le_lo_hi
+
+/-- The upper endpoint is the lower endpoint plus the interval width. -/
+theorem lo_add_width (I : GapInterval) : I.lo + I.width = I.hi := by
+  simp [width]
+
+/--
+Image of a nonnegative rational interval under the natural power map.
+
+The nonnegativity assumption ensures that endpoint order is preserved.
+-/
+def powNonneg (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) : GapInterval where
+  lo := I.lo ^ d
+  hi := I.hi ^ d
+  le_lo_hi := by
+    have hhi : 0 ≤ I.hi := hlo.trans I.le_lo_hi
+    exact pow_le_pow_left₀ hlo I.le_lo_hi d
+
+/-- Lower endpoint of the nonnegative power image. -/
+@[simp]
+theorem powNonneg_lo (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) :
+    (I.powNonneg d hlo).lo = I.lo ^ d := rfl
+
+/-- Upper endpoint of the nonnegative power image. -/
+@[simp]
+theorem powNonneg_hi (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) :
+    (I.powNonneg d hlo).hi = I.hi ^ d := rfl
+
+/--
+The width after applying a power is exactly the original width multiplied by
+the gap-normalized correction kernel.
+-/
+theorem powNonneg_width_eq
+    (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) :
+    (I.powNonneg d hlo).width = I.width * gapGN d I.lo I.width := by
+  change I.hi ^ d - I.lo ^ d = I.width * gapGN d I.lo I.width
+  rw [← I.lo_add_width]
+  exact pow_add_sub_pow_eq_delta_mul_gapGN d I.lo I.width
+
+end GapInterval
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/ErrorKernel.lean b/lean/dk_math/DkMath/Analysis/ErrorKernel.lean
new file mode 100644
index 00000000..dc50eb3d
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/ErrorKernel.lean
@@ -0,0 +1,39 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.GapGN
+
+#print "file: DkMath.Analysis.ErrorKernel"
+
+/-!
+# Exact observation-error correction
+
+The observed value is `base + err`. The full power error is retained by
+`gapGN`; no Taylor truncation is used.
+-/
+
+namespace DkMath.Analysis
+
+/-- Exact power error between an observed value and its base value. -/
+def observedGapError {R : Type*} [CommRing R] (d : ℕ) (base err : R) : R :=
+  (base + err) ^ d - base ^ d
+
+/-- The complete observation error factors into `err` times the gap kernel. -/
+theorem observedGapError_eq_err_mul_gapGN
+    {R : Type*} [CommRing R] (d : ℕ) (base err : R) :
+    observedGapError d base err = err * gapGN d base err := by
+  exact pow_add_sub_pow_eq_delta_mul_gapGN d base err
+
+/--
+Subtracting the exact gap-kernel correction recovers the unobserved base power.
+-/
+theorem exactCorrection
+    {R : Type*} [CommRing R] (d : ℕ) (base err : R) :
+    (base + err) ^ d - err * gapGN d base err = base ^ d := by
+  rw [pow_add_eq_pow_add_delta_mul_gapGN]
+  ring
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/GapFill.lean b/lean/dk_math/DkMath/Analysis/GapFill.lean
new file mode 100644
index 00000000..121d130f
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/GapFill.lean
@@ -0,0 +1,91 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.GapGN
+
+#print "file: DkMath.Analysis.GapFill"
+
+/-!
+# Filling the gap between two observations
+
+`gapLine` scans the affine segment from `u₁` to `u₂`. `gapFill` observes that
+segment through the power map. Algebraic endpoint formulas are separated from
+the ordered real bridge.
+-/
+
+namespace DkMath.Analysis
+
+/-- Affine scan from `u₁` to `u₂` with parameter `t`. -/
+def gapLine {R : Type*} [Ring R] (u₁ u₂ t : R) : R :=
+  u₁ + t * (u₂ - u₁)
+
+/-- Power observation along the affine gap line. -/
+def gapFill {R : Type*} [Ring R] (d : ℕ) (u₁ u₂ t : R) : R :=
+  gapLine u₁ u₂ t ^ d
+
+/-- The gap line starts at `u₁`. -/
+@[simp]
+theorem gapLine_zero {R : Type*} [Ring R] (u₁ u₂ : R) :
+    gapLine u₁ u₂ 0 = u₁ := by
+  simp [gapLine]
+
+/-- The gap line ends at `u₂`. -/
+@[simp]
+theorem gapLine_one {R : Type*} [Ring R] (u₁ u₂ : R) :
+    gapLine u₁ u₂ 1 = u₂ := by
+  simp [gapLine]
+
+/-- The powered gap fill starts at `u₁^d`. -/
+@[simp]
+theorem gapFill_zero {R : Type*} [Ring R] (d : ℕ) (u₁ u₂ : R) :
+    gapFill d u₁ u₂ 0 = u₁ ^ d := by
+  simp [gapFill]
+
+/-- The powered gap fill ends at `u₂^d`. -/
+@[simp]
+theorem gapFill_one {R : Type*} [Ring R] (d : ℕ) (u₁ u₂ : R) :
+    gapFill d u₁ u₂ 1 = u₂ ^ d := by
+  simp [gapFill]
+
+/--
+The endpoint change of a powered gap fill is exactly its width times `gapGN`.
+-/
+theorem gapFill_endpoint_sub_eq
+    {R : Type*} [CommRing R] (d : ℕ) (u₁ u₂ : R) :
+    gapFill d u₁ u₂ 1 - gapFill d u₁ u₂ 0
+      = (u₂ - u₁) * gapGN d u₁ (u₂ - u₁) := by
+  rw [gapFill_one, gapFill_zero]
+  have hbase : u₁ + (u₂ - u₁) = u₂ := by ring
+  simpa only [hbase] using
+    (pow_add_sub_pow_eq_delta_mul_gapGN d u₁ (u₂ - u₁))
+
+/-- For `t` in `[0,1]`, the real gap line stays between ordered endpoints. -/
+theorem gapLine_mem_Icc
+    {u₁ u₂ t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hle : u₁ ≤ u₂) :
+    gapLine u₁ u₂ t ∈ Set.Icc u₁ u₂ := by
+  have hdelta : 0 ≤ u₂ - u₁ := sub_nonneg.mpr hle
+  have hmul_nonneg : 0 ≤ t * (u₂ - u₁) := mul_nonneg ht.1 hdelta
+  have hmul_le : t * (u₂ - u₁) ≤ u₂ - u₁ := by
+    exact mul_le_of_le_one_left hdelta ht.2
+  constructor <;> simp only [gapLine, Set.mem_Icc] at *
+  · linarith
+  · linarith
+
+/--
+On a nonnegative ordered real interval, the powered gap fill stays between the
+powered endpoint values.
+-/
+theorem gapFill_mem_Icc_of_nonneg
+    {d : ℕ} {u₁ u₂ t : ℝ}
+    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu₁ : 0 ≤ u₁) (hle : u₁ ≤ u₂) :
+    gapFill d u₁ u₂ t ∈ Set.Icc (u₁ ^ d) (u₂ ^ d) := by
+  have hline := gapLine_mem_Icc ht hle
+  have hline_nonneg : 0 ≤ gapLine u₁ u₂ t := hu₁.trans hline.1
+  constructor
+  · exact pow_le_pow_left₀ hu₁ hline.1 d
+  · exact pow_le_pow_left₀ hline_nonneg hline.2 d
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/GapGN.lean b/lean/dk_math/DkMath/Analysis/GapGN.lean
new file mode 100644
index 00000000..64d78c03
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/GapGN.lean
@@ -0,0 +1,59 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.Basic
+
+#print "file: DkMath.Analysis.GapGN"
+
+/-!
+# Gap-normalized difference kernel
+
+`gapGN d base delta` is the analysis-facing argument order for the existing
+cosmic-formula kernel `GN d delta base`.
+
+It records the exact factor left after extracting `delta` from
+`(base + delta)^d - base^d`.
+-/
+
+namespace DkMath.Analysis
+
+/--
+The exact power-difference kernel with analysis-oriented argument order.
+
+The existing cosmic-formula `GN` takes the boundary difference first and the
+base second. The analysis layer presents the base before the observed change.
+-/
+abbrev gapGN {R : Type*} [CommSemiring R] (d : ℕ) (base delta : R) : R :=
+  DkMath.CosmicFormulaBinom.GN d delta base
+
+/-- `gapGN` is the existing cosmic-formula `GN` with its last two arguments swapped. -/
+theorem gapGN_eq_GN {R : Type*} [CommSemiring R] (d : ℕ) (base delta : R) :
+    gapGN d base delta = DkMath.CosmicFormulaBinom.GN d delta base := rfl
+
+/--
+Exact additive power decomposition.
+
+This is the subtraction-free form of the gap correction identity and therefore
+holds over every commutative semiring.
+-/
+theorem pow_add_eq_pow_add_delta_mul_gapGN
+    {R : Type*} [CommSemiring R] (d : ℕ) (base delta : R) :
+    (base + delta) ^ d = base ^ d + delta * gapGN d base delta := by
+  simpa [gapGN, add_comm] using
+    (DkMath.CosmicFormulaBinom.add_pow_gap_factor (R := R) d delta base)
+
+/--
+Exact factorization of a power difference.
+
+No limit, approximation, derivative, or omitted higher-order term occurs.
+-/
+theorem pow_add_sub_pow_eq_delta_mul_gapGN
+    {R : Type*} [CommRing R] (d : ℕ) (base delta : R) :
+    (base + delta) ^ d - base ^ d = delta * gapGN d base delta := by
+  rw [pow_add_eq_pow_add_delta_mul_gapGN]
+  ring
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/RealBridge.lean b/lean/dk_math/DkMath/Analysis/RealBridge.lean
new file mode 100644
index 00000000..63622e93
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/RealBridge.lean
@@ -0,0 +1,56 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.ErrorKernel
+import DkMath.Analysis.GapFill
+
+#print "file: DkMath.Analysis.RealBridge"
+
+/-!
+# Bridge to Mathlib real analysis
+
+The definitions in `DkMath.Analysis` are algebraic and remain meaningful over
+general rings. This file records their standard real interpretation and begins
+the bridge to Mathlib's topological and analytic API.
+-/
+
+namespace DkMath.Analysis
+
+/-- The exact `gapGN` power decomposition specialized to real numbers. -/
+theorem real_pow_add_eq_pow_add_delta_mul_gapGN
+    (d : ℕ) (base delta : ℝ) :
+    (base + delta) ^ d = base ^ d + delta * gapGN d base delta :=
+  pow_add_eq_pow_add_delta_mul_gapGN d base delta
+
+/-- The exact observation correction specialized to real numbers. -/
+theorem real_exactCorrection (d : ℕ) (base err : ℝ) :
+    (base + err) ^ d - err * gapGN d base err = base ^ d :=
+  exactCorrection d base err
+
+/-- The affine gap scan is continuous in its scan parameter. -/
+theorem continuous_gapLine (u₁ u₂ : ℝ) :
+    Continuous (fun t : ℝ => gapLine u₁ u₂ t) := by
+  unfold gapLine
+  fun_prop
+
+/-- The powered gap fill is continuous in its scan parameter. -/
+theorem continuous_gapFill (d : ℕ) (u₁ u₂ : ℝ) :
+    Continuous (fun t : ℝ => gapFill d u₁ u₂ t) := by
+  unfold gapFill gapLine
+  fun_prop
+
+/--
+The real gap fill maps the unit scan interval into the powered endpoint
+interval when the endpoints are nonnegative and ordered.
+-/
+theorem mapsTo_gapFill_Icc_of_nonneg
+    {d : ℕ} {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁) (hle : u₁ ≤ u₂) :
+    Set.MapsTo (fun t : ℝ => gapFill d u₁ u₂ t)
+      (Set.Icc 0 1) (Set.Icc (u₁ ^ d) (u₂ ^ d)) := by
+  intro t ht
+  exact gapFill_mem_Icc_of_nonneg ht hu₁ hle
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
new file mode 100644
index 00000000..532db2b7
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -0,0 +1,155 @@
+# DkMath.Analysis Initial Layer
+
+## Purpose
+
+`DkMath.Analysis` does not reconstruct or replace Mathlib's real numbers.
+It introduces a DkMath interpretation of exact gaps, residuals, correction
+kernels, and interval filling, then connects that interpretation to Mathlib.
+
+The first implementation checkpoint has two routes.
+
+```text
+Route A:
+  exact algebraic identities over commutative rings and semirings,
+  followed by an explicit bridge to Mathlib real analysis.
+
+Route B:
+  exact rational intervals as a computational substrate for a future DkReal.
+```
+
+## Module Boundary
+
+```text
+DkMath.Analysis.Basic
+  common namespace and dependency boundary
+
+DkMath.Analysis.GapGN
+  analysis-oriented wrapper around the existing cosmic-formula GN
+
+DkMath.Analysis.CosmicResidual
+  absolute residual, two-point drift, common bias, and beam perturbation
+
+DkMath.Analysis.ErrorKernel
+  exact observed/base/error correction
+
+DkMath.Analysis.GapFill
+  affine interval scan, powered fill, endpoint identity, and real order theorem
+
+DkMath.Analysis.RealBridge
+  specialization to Real and Mathlib Continuous / Set.MapsTo
+
+DkMath.Analysis.DkReal.Interval
+  rational GapInterval, width, nonnegative power image, and exact width formula
+```
+
+## Canonical Kernel Bridge
+
+The existing cosmic-formula kernel has argument order:
+
+```lean
+DkMath.CosmicFormulaBinom.GN d delta base
+```
+
+The analysis-facing wrapper uses:
+
+```lean
+gapGN d base delta
+```
+
+and is definitionally the same value:
+
+```lean
+gapGN d base delta = DkMath.CosmicFormulaBinom.GN d delta base
+```
+
+The fundamental exact identity is:
+
+```lean
+pow_add_sub_pow_eq_delta_mul_gapGN :
+  (base + delta)^d - base^d = delta * gapGN d base delta
+```
+
+No limit and no truncated Taylor expansion is involved.
+
+## Residual Versus Drift
+
+The quadratic cosmic gap is:
+
+```lean
+cosmicGap x u = (x + u)^2 - x * (x + 2*u)
+```
+
+The implementation proves:
+
+```lean
+cosmicGap_eq_sq :
+  cosmicGap x u = u^2
+
+cosmicResidual_eq_zero :
+  cosmicResidual x u = 0
+
+cosmicDrift_eq_zero :
+  cosmicDrift x y u = 0
+```
+
+A common additive bias has nonzero absolute residual but zero two-point drift.
+The API therefore keeps these two observations separate.
+
+## Exact Error Correction
+
+For an observation `base + err`:
+
+```lean
+observedGapError_eq_err_mul_gapGN :
+  observedGapError d base err = err * gapGN d base err
+
+exactCorrection :
+  (base + err)^d - err * gapGN d base err = base^d
+```
+
+This retains the complete finite power difference.
+
+## Gap Filling
+
+The interval scan is:
+
+```lean
+gapLine u₁ u₂ t = u₁ + t * (u₂ - u₁)
+gapFill d u₁ u₂ t = (gapLine u₁ u₂ t)^d
+```
+
+Its endpoint difference is:
+
+```lean
+gapFill_endpoint_sub_eq :
+  gapFill d u₁ u₂ 1 - gapFill d u₁ u₂ 0
+    = (u₂ - u₁) * gapGN d u₁ (u₂ - u₁)
+```
+
+For real nonnegative ordered endpoints, the implementation proves that the
+whole powered scan stays in the powered endpoint interval. The real bridge also
+proves continuity in `t`.
+
+## Rational Interval Prototype
+
+`GapInterval` contains exact rational endpoints:
+
+```lean
+structure GapInterval where
+  lo : Rat
+  hi : Rat
+  le_lo_hi : lo <= hi
+```
+
+For a nonnegative interval, `powNonneg` maps both endpoints through a natural
+power while preserving order. Its width satisfies:
+
+```lean
+GapInterval.powNonneg_width_eq :
+  (I.powNonneg d hlo).width
+    = I.width * gapGN d I.lo I.width
+```
+
+This is the initial computational basis for `DkReal`. Nested interval
+sequences, convergence, and evaluation into Mathlib's real numbers are deferred
+to later checkpoints.
````
`````
