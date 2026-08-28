# PPW-019 — centered Xi multiplicity transport / fixed local-charge bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-018 complete Green
Lean toolchain: v4.32.2
mathlib rev: 905b95818eb32af7874a58b427f50c1711a5e96c
```

PPW-018 までで、zero parameter を持たない fixed entire object

```text
pascalCenteredRiemannXiKernel : ℂ → ℂ
```

と fixed log-derivative candidate

```text
pascalCenteredXiNegLogDeriv : ℂ → ℂ
```

が Green になった。

また非自明 zeta zero `ρ` に対して centered coordinate

```text
zρ := ρ - criticalLineCenter
```

は

```text
pascalCenteredRiemannXiKernel zρ = 0
```

を満たす。

しかし現時点では、Xi 側の零点 multiplicity と既存

```text
riemannZetaZeroMultiplicity ρ
```

が一致することはまだ formalize されていない。従って Xi の `-logDeriv` residue を既存 zeta multiplicity と同一視してはならない。

PPW-019 の目的は、次の順序でこの gap を閉じることである。

```text
zeta zero multiplicity
  ↓ exact analytic-order transport
uncentered Xi multiplicity
  ↓ affine centering transport
centered Xi multiplicity
  ↓ local factorization
fixed -logDeriv Xi residue
  ↓ Mathlib circleIntegral
fixed local circle charge
  ↓ finite PPW window sum
existing total multiplicity / centered second moment
```

今回の最重要点は、PPW-017 の radial charge と違って **integrand も polynomial weight も zero-independent に固定できる**ところまで進めることである。

一方、local circles の有限和を一つの outer contour と同一視することはまだ行わない。それは PPW-020 の仕事とする。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalCenteredXiMultiplicityLocalChargeBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalCenteredXiMultiplicityLocalChargeBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalCanonicalXiFixedObservableBridge
import DkMath.RH.CFBRC.PascalZetaZeroMultiplicityBridge
import DkMath.RH.CFBRC.PascalZetaLocalCircleChargeBridge
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` の PPW-018 の直後へ公開 import を追加する。

---

## 3. exact API audit

今回の branch の `lake-manifest.json` は mathlib

```text
905b95818eb32af7874a58b427f50c1711a5e96c
```

を pin している。

この rev で以下の API が存在することを確認済みである。ただし実装開始時に local toolchain で `#check` して exact implicit arguments を確認すること。

### 3.1 analytic order

```lean
#check analyticOrderAt_congr
#check analyticOrderAt_mul
#check analyticOrderNatAt_mul
#check analyticOrderAt_comp_of_deriv_ne_zero
#check AnalyticAt.analyticOrderAt_ne_top
#check AnalyticAt.analyticOrderAt_eq_zero
```

特に multiplication について current API は、analytic な `f`, `g` に対して

```text
analyticOrderAt (f * g) z₀
  = analyticOrderAt f z₀ + analyticOrderAt g z₀
```

を与える。

また affine composition の derivative が非零なら

```text
analyticOrderAt (f ∘ g) z₀
  = analyticOrderAt f (g z₀)
```

を直接使える。

### 3.2 GammaR inverse

current Mathlib に

```lean
#check Complex.differentiable_Gammaℝ_inv
#check Complex.Gammaℝ_ne_zero_of_re_pos
```

が存在する。

重要なのは `Gammaℝ` 自体ではなく、

```text
s ↦ (Gammaℝ s)⁻¹
```

が **global Differentiable** として既に用意されていることである。

したがって zeta / completed-zeta multiplicity transport では、Gamma の pole を直接扱わず

```text
ζ = completedZeta * GammaR⁻¹
```

という local product を使う。

### 3.3 zeta / completed-zeta relation

既存 Mathlib:

```lean
#check riemannZeta_def_of_ne_zero
```

すなわち `s ≠ 0` なら

```text
riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s
```

である。

PPW-018 既存:

```lean
pascalRiemannXiKernel_eq_mul_completedRiemannZeta
```

すなわち `s ≠ 0,1` なら

```text
pascalRiemannXiKernel s
  = s * (1 - s) * completedRiemannZeta s
```

である。

---

## 4. Phase A — centered Xi zero set と intrinsic multiplicity

### 4.1 zero set

```lean
def pascalCenteredXiZeros : Set ℂ :=
  pascalCenteredRiemannXiKernel ⁻¹' {0}
```

```lean
@[simp] theorem mem_pascalCenteredXiZeros {z : ℂ} :
    z ∈ pascalCenteredXiZeros ↔
      pascalCenteredRiemannXiKernel z = 0 :=
  Iff.rfl
```

### 4.2 entire analytic API

PPW-018 の

```lean
differentiable_pascalCenteredRiemannXiKernel
```

から、必要なら次を薄く用意する。

```lean
theorem analyticOn_pascalCenteredRiemannXiKernel :
    AnalyticOnNhd ℂ pascalCenteredRiemannXiKernel Set.univ := by
  exact differentiable_pascalCenteredRiemannXiKernel.differentiableOn.analyticOnNhd
    isOpen_univ
```

```lean
theorem analyticAt_pascalCenteredRiemannXiKernel (z : ℂ) :
    AnalyticAt ℂ pascalCenteredRiemannXiKernel z := by
  exact analyticOn_pascalCenteredRiemannXiKernel z (Set.mem_univ z)
```

uncentered `pascalRiemannXiKernel` にも同様の helper を用意してよい。

### 4.3 fixed nonzero witness

centered coordinate `-criticalLineCenter` は uncentered `s = 0` に対応するため、definition から Xi kernel は `-1` になる。

候補:

```lean
@[simp] theorem pascalCenteredRiemannXiKernel_neg_center :
    pascalCenteredRiemannXiKernel (-criticalLineCenter) = -1 := by
  simp [pascalCenteredRiemannXiKernel, pascalRiemannXiKernel,
    criticalLineCenter]
```

これを entire function が identically zero でない固定 witness として使う。

### 4.4 zero set の closed / discrete

Mathlib の `ZetaZeros.lean` と同じ pattern を使ってよい。

`AnalyticOnNhd.preimage_zero_mem_codiscreteWithin` を `Set.univ` 上で使い、

```lean
theorem isClosed_pascalCenteredXiZeros :
    IsClosed pascalCenteredXiZeros
```

```lean
theorem isDiscrete_pascalCenteredXiZeros :
    IsDiscrete pascalCenteredXiZeros
```

を作る。

可能なら convenience:

```lean
theorem finite_pascalCenteredXiZeros_in_compact
    {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ pascalCenteredXiZeros).Finite
```

も追加する。

これは後続 outer-contour work で有用だが、build complexity が高ければ `isDiscrete` までを mandatory とする。

### 4.5 intrinsic multiplicity

```lean
noncomputable def pascalCenteredXiZeroMultiplicity (z : ℂ) : ℕ :=
  analyticOrderNatAt pascalCenteredRiemannXiKernel z
```

zero `z` について analytic order が finite である theorem:

```lean
theorem analyticOrderAt_pascalCenteredXi_ne_top_of_mem
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    analyticOrderAt pascalCenteredRiemannXiKernel z ≠ ⊤ := by
  ...
```

PPW-014 の `analyticOrderAt_riemannZeta_ne_top...` と同じ identity-principle route を使う。

さらに:

```lean
@[simp] theorem analyticOrderAt_pascalCenteredXi_eq_multiplicity
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    analyticOrderAt pascalCenteredRiemannXiKernel z =
      (pascalCenteredXiZeroMultiplicity z : ℕ∞)
```

```lean
theorem pascalCenteredXiZeroMultiplicity_pos
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    0 < pascalCenteredXiZeroMultiplicity z
```

まで作る。

---

## 5. Phase B — zeta → uncentered Xi analytic-order transport

ここが PPW-019 の第一 load-bearing 部分。

非自明 zero `ρ` を固定する。

```lean
variable {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ)
```

既存から

```text
0 < ρ.re
ρ.re < 1
ρ ≠ 0
ρ ≠ 1
GammaR ρ ≠ 0
```

を得る。

### 5.1 polynomial factor

必要なら名前を付ける。

```lean
noncomputable def pascalXiPolynomialFactor (s : ℂ) : ℂ :=
  s * (1 - s)
```

`ρ` では非零で analytic order `0`:

```lean
theorem pascalXiPolynomialFactor_ne_zero_of_nontrivial ...
```

```lean
theorem analyticOrderAt_pascalXiPolynomialFactor_eq_zero_of_nontrivial ...
```

### 5.2 completed zeta の local analyticity

`completedRiemannZeta` は `0,1` を避ける open set 上で complex differentiable なので、current `differentiableAt_completedZeta` から `AnalyticAt` を作る。

候補 helper:

```lean
theorem analyticAt_completedRiemannZeta_of_ne_zero_one
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  ...
```

`{0,1}ᶜ` 上の `DifferentiableOn` を作り `analyticOnNhd` に上げる route が安全。

### 5.3 Xi order = completed-zeta order

`ρ ≠ 0,1` は neighborhood property なので、PPW-018 の pointwise identity を eventually equality に上げる。

```text
pascalRiemannXiKernel
  =ᶠ[𝓝 ρ]
fun w => pascalXiPolynomialFactor w * completedRiemannZeta w
```

それから

```lean
analyticOrderAt_congr
analyticOrderAt_mul
```

を使い polynomial factor の order `0` を消す。

必須 theorem:

```lean
theorem analyticOrderAt_pascalRiemannXiKernel_eq_completedRiemannZeta_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    analyticOrderAt pascalRiemannXiKernel ρ =
      analyticOrderAt completedRiemannZeta ρ
```

### 5.4 completed-zeta order = zeta order

ここでは `Gammaℝ` 自体の analytic continuation を再構成しない。

Mathlib の global analytic unit candidate

```text
w ↦ (Complex.Gammaℝ w)⁻¹
```

を使う。

`Complex.differentiable_Gammaℝ_inv` から `AnalyticAt` を作る helper:

```lean
theorem analyticAt_GammaR_inv (s : ℂ) :
    AnalyticAt ℂ (fun w => (Complex.Gammaℝ w)⁻¹) s := by
  have h : AnalyticOnNhd ℂ (fun w => (Complex.Gammaℝ w)⁻¹) Set.univ :=
    Complex.differentiable_Gammaℝ_inv.differentiableOn.analyticOnNhd isOpen_univ
  exact h s (Set.mem_univ s)
```

`0 < ρ.re` により `Gammaℝ ρ ≠ 0`、従って inverse factor も非零で order `0`。

`riemannZeta_def_of_ne_zero` を neighborhood equality にして、

```text
riemannZeta
  =ᶠ[𝓝 ρ]
fun w => completedRiemannZeta w * (Complex.Gammaℝ w)⁻¹
```

を得る。

それから同様に order additivity を使う。

必須 theorem:

```lean
theorem analyticOrderAt_completedRiemannZeta_eq_riemannZeta_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    analyticOrderAt completedRiemannZeta ρ =
      analyticOrderAt riemannZeta ρ
```

方向はどちらでもよいが、最終 statement はこの形へ揃える。

### 5.5 uncentered Xi ↔ zeta order

上記二本を合成して:

```lean
@[simp] theorem analyticOrderAt_pascalRiemannXiKernel_eq_riemannZeta_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    analyticOrderAt pascalRiemannXiKernel ρ =
      analyticOrderAt riemannZeta ρ
```

これが uncentered multiplicity transport の load-bearing theorem。

---

## 6. Phase C — affine centering transport

`pascalCenteredRiemannXiKernel` は

```text
z ↦ pascalRiemannXiKernel (criticalLineCenter + z)
```

である。

Mathlib の

```lean
analyticOrderAt_comp_of_deriv_ne_zero
```

を使用する。

inner affine map

```lean
fun z : ℂ => criticalLineCenter + z
```

は analytic、derivative は `1 ≠ 0`。

非自明 zero `ρ` の centered coordinate

```text
zρ = ρ - criticalLineCenter
```

では inner map の値が `ρ` になる。

必須 theorem:

```lean
theorem analyticOrderAt_pascalCenteredXi_sub_center_eq_riemannZeta
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    analyticOrderAt pascalCenteredRiemannXiKernel
        (ρ - criticalLineCenter) =
      analyticOrderAt riemannZeta ρ
```

続いて `analyticOrderNatAt` を unfold / `congrArg ENat.toNat` で transport し、今回の最重要 multiplicity theorem:

```lean
@[simp] theorem pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    pascalCenteredXiZeroMultiplicity (ρ - criticalLineCenter) =
      riemannZetaZeroMultiplicity ρ
```

を完成させる。

**停止線:** zero-set equivalenceだけから multiplicity equality を証明してはならない。必ず analytic order の nonvanishing-factor transport を通すこと。

---

## 7. Phase D — centered Xi local factorization / residue

### 7.1 local factorization

任意の centered Xi zero `z` に対して:

```lean
theorem exists_pascalCenteredXi_local_factorization
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z ∧
      g z ≠ 0 ∧
      pascalCenteredRiemannXiKernel =ᶠ[𝓝 z]
        (fun w => (w - z) ^ pascalCenteredXiZeroMultiplicity z * g w)
```

PPW-014 `exists_riemannZeta_local_factorization` の proof pattern をそのまま踏襲してよい。

### 7.2 fixed Xi negative log-derivative residue

PPW-014 の arbitrary multiplicity proof を Xi へ移す。

```lean
theorem tendsto_mul_pascalCenteredXiNegLogDeriv_zeroMultiplicity
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    Tendsto
      (fun w => (w - z) * pascalCenteredXiNegLogDeriv w)
      (𝓝[≠] z)
      (𝓝 (-(pascalCenteredXiZeroMultiplicity z : ℂ)))
```

可能なら PPW-014 の長い proof を general helper へ refactor して再利用してもよいが、既存 Green theorem を壊す大きな改変は不要。

非自明 zeta zero 専用 corollary:

```lean
theorem tendsto_mul_pascalCenteredXiNegLogDeriv_of_nontrivial
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    Tendsto
      (fun w =>
        (w - (ρ - criticalLineCenter)) * pascalCenteredXiNegLogDeriv w)
      (𝓝[≠] (ρ - criticalLineCenter))
      (𝓝 (-(riemannZetaZeroMultiplicity ρ : ℂ)))
```

ここで初めて fixed Xi log derivative residue と既存 zeta multiplicity が exact に一致する。

---

## 8. Phase E — centered Xi isolating radius

Xi は entire なので、zeta の pole `1` を避ける clause は不要。

```lean
def IsPascalCenteredXiIsolatingRadius (z : ℂ) (r : ℝ) : Prop :=
  0 < r ∧
    ∀ w ∈ Metric.closedBall z r,
      w ≠ z → pascalCenteredRiemannXiKernel w ≠ 0
```

`isDiscrete_pascalCenteredXiZeros` と

```lean
Metric.exists_closedBall_inter_eq_singleton_of_discrete
```

を使い、zero `z` について existence:

```lean
theorem exists_isPascalCenteredXiIsolatingRadius
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    ∃ r : ℝ, IsPascalCenteredXiIsolatingRadius z r
```

chosen radius:

```lean
noncomputable def pascalCenteredXiIsolatingRadius (z : ℂ) : ℝ := ...
```

spec:

```lean
theorem pascalCenteredXiIsolatingRadius_spec
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    IsPascalCenteredXiIsolatingRadius z
      (pascalCenteredXiIsolatingRadius z)
```

```lean
theorem pascalCenteredXiIsolatingRadius_pos ...
```

まで用意する。

---

## 9. Phase F — fixed local circle charge

### 9.1 residue kernel

```lean
noncomputable def pascalCenteredXiLocalResidueKernel
    (z w : ℂ) : ℂ :=
  (w - z) * pascalCenteredXiNegLogDeriv w
```

Phase D の limit をそのまま wrapper 化する。

punctured disk 上の differentiability / closed punctured disk 上の continuity は PPW-015 と同じ構造でよい。

Xi は entire なので domain pole clause は不要であり、isolating radius から必要なのは `Xi(w) ≠ 0` だけである。

### 9.2 local circle theorem

Mathlib standard orientation のまま:

```lean
theorem circleIntegral_pascalCenteredXiNegLogDeriv_eq_of_isolatingRadius
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros)
    {r : ℝ} (hr : IsPascalCenteredXiIsolatingRadius z r) :
    circleIntegral pascalCenteredXiNegLogDeriv z r =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity z : ℂ)
```

chosen radius 版:

```lean
theorem circleIntegral_pascalCenteredXiNegLogDeriv_eq
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
    circleIntegral pascalCenteredXiNegLogDeriv z
      (pascalCenteredXiIsolatingRadius z) =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity z : ℂ)
```

非自明 zeta zero 専用 transport:

```lean
theorem circleIntegral_pascalCenteredXiNegLogDeriv_sub_center_eq_riemannMultiplicity
    {ρ : ℂ} (hρ : NontrivialRiemannZetaZero ρ) :
    circleIntegral pascalCenteredXiNegLogDeriv
      (ρ - criticalLineCenter)
      (pascalCenteredXiIsolatingRadius (ρ - criticalLineCenter)) =
      -(2 * Real.pi * Complex.I) *
        (riemannZetaZeroMultiplicity ρ : ℂ)
```

この theorem で PPW-015 の zeta local charge と PPW-019 の Xi local charge が multiplicity level で一致する。

---

## 10. Phase G — generic fixed holomorphic weight

PPW-020 outer contour に備え、integrand と weight を zero-independent に固定できる API を今回作る。

### 10.1 weighted Xi residue kernel

```lean
noncomputable def pascalCenteredXiWeightedLocalResidueKernel
    (h : ℂ → ℂ) (z w : ℂ) : ℂ :=
  h w * pascalCenteredXiLocalResidueKernel z w
```

`h` が `z` で continuous なら limit:

```lean
theorem tendsto_pascalCenteredXiWeightedLocalResidueKernel
    {h : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeros)
    (hh : ContinuousAt h z) :
    Tendsto
      (pascalCenteredXiWeightedLocalResidueKernel h z)
      (𝓝[≠] z)
      (𝓝 (h z * (-(pascalCenteredXiZeroMultiplicity z : ℂ))))
```

### 10.2 weighted local circle theorem

```lean
theorem circleIntegral_weight_mul_pascalCenteredXiNegLogDeriv_eq
    {h : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeros)
    (hh : Differentiable ℂ h) :
    circleIntegral
      (fun w => h w * pascalCenteredXiNegLogDeriv w)
      z (pascalCenteredXiIsolatingRadius z) =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity z : ℂ) * h z
```

ここで `h` は一つの fixed function である。center `z` は変わるが integrand family の analytic weight 自体を zero から作らない。

---

## 11. Phase H — finite PPW window fixed local charges

outer contour はまだ作らず、既存 window `pascalCriticalMirrorZeroWindowFinset R` を index set として使う。

### 11.1 unweighted fixed Xi local mass

```lean
noncomputable def pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass
    (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    circleIntegral pascalCenteredXiNegLogDeriv
      (ρ - criticalLineCenter)
      (pascalCenteredXiIsolatingRadius (ρ - criticalLineCenter))
```

termwise multiplicity transport から:

```lean
theorem pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass R =
      -(2 * Real.pi * Complex.I) *
        (pascalCriticalMirrorZeroWindowMultiplicity R : ℂ)
```

normalized:

```lean
theorem pascalCriticalMirrorZeroWindowNormalizedCenteredXiLocalContourMass_eq
    (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass R =
      -(pascalCriticalMirrorZeroWindowMultiplicity R : ℂ)
```

これは PPW-015 と同じ multiplicity mass を、**fixed centered Xi log derivative** から再取得する theorem である。

### 11.2 generic fixed weighted finite mass

```lean
noncomputable def pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass
    (h : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    circleIntegral
      (fun w => h w * pascalCenteredXiNegLogDeriv w)
      (ρ - criticalLineCenter)
      (pascalCenteredXiIsolatingRadius (ρ - criticalLineCenter))
```

```lean
theorem pascalCriticalMirrorZeroWindowNormalizedCenteredXiWeightedLocalContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass h R =
      -∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        (riemannZetaZeroMultiplicity ρ : ℂ) *
          h (ρ - criticalLineCenter)
```

これが finite moment accounting の general API となる。

---

## 12. Phase I — fixed centered second moment

fixed polynomial weight:

```lean
noncomputable def pascalCenteredXiSecondWeight (z : ℂ) : ℂ := z ^ 2
```

```lean
theorem differentiable_pascalCenteredXiSecondWeight :
    Differentiable ℂ pascalCenteredXiSecondWeight := by
  fun_prop
```

finite local contour mass:

```lean
noncomputable def pascalCriticalMirrorZeroWindowCenteredXiSecondLocalContourMass
    (R : ℝ) : ℂ :=
  pascalCriticalMirrorZeroWindowCenteredXiWeightedLocalContourMass
    pascalCenteredXiSecondWeight R
```

最重要 second-moment theorem:

```lean
theorem pascalCriticalMirrorZeroWindowNormalizedCenteredXiSecondLocalContourMass_eq
    (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowCenteredXiSecondLocalContourMass R =
      -pascalCriticalMirrorZeroWindowCenteredSecondMoment R
```

PPW-016 の centered second moment

```text
Σ mρ * (ρ - 1/2)^2
```

を、zero-independent fixed function

```text
z ↦ z^2 * pascalCenteredXiNegLogDeriv z
```

の local-circle finite accounting として exact に再構成する。

ここが PPW-019 の第二 load-bearing endpoint。

---

## 13. 何が進み、何が残るか

PPW-017 radial side:

```text
zero-dependent hρ
  ↓
Σ mρ |ρ - 1/2|²
  ↓
CF2D q2 radial mass
```

PPW-019 fixed Xi side:

```text
fixed Xi_centered
  ↓
fixed -logDeriv Xi_centered
  ↓
fixed polynomial weight z²
  ↓
Σ mρ (ρ - 1/2)²
```

従って **holomorphic centered second moment** は fixed observable 化できる。

しかし radial quantity

```text
|z|² = z * conj(z)
```

は holomorphic weight ではない。

PPW-017 で radial mass を読むために zero-dependent mirror-frozen factor が必要だった理由はここに残る。

PPW-019 完了後の研究 gap は、より明確に:

```text
fixed holomorphic Xi moments
        vs
non-holomorphic / mirror-paired CF2D q2 radial mass
```

となる。

---

## 14. 今回やらないこと

PPW-019 では以下を実装しない。

```text
local-circle finite sum = one outer contour
argument principle on a large disk / rectangle
all centered Xi zeros = centered nontrivial zeta zeros の global classification
outer contour 内に extra Xi zero が無いという無証明の仮定
frozen radial mass = fixed Xi outer contour
|z|² を holomorphic weight として積分
SecondMomentDefect = 0
HorizontalEnergy = 0
primeMirror window energy = 0
RiemannHypothesis の導出
critical-strip finite PHZ convergence
explicit formula / Li / Weil positivity
```

---

## 15. Stop conditions / audit warnings

1. `Xi zero ↔ zeta zero` の pointwise zero equivalenceだけから multiplicity equalityを推論しない。multiplicity transport は analytic-order additivityで証明する。
2. `Gammaℝ` の pole structure を独自に展開しない。今回必要なのは Mathlib の entire `Gammaℝ⁻¹` 側である。
3. `riemannZeta_def_of_ne_zero` を `s = 0` へ無条件 extension しない。neighborhood equality を作る時も `ρ ≠ 0` を使う。
4. `pascalRiemannXiKernel_eq_mul_completedRiemannZeta` は `s ≠ 0,1` の local theorem として使う。
5. centered affine translation は multiplicity を保存するが、これは derivative `1 ≠ 0` を持つためである。単なる zero correspondence だけで済ませない。
6. Xi local residue の値を `riemannZetaZeroMultiplicity` と書くのは transport theorem 完成後のみ。
7. local circles の integrand が同じ fixed function になっても、有限和を outer contour と同一視してはならない。contour deformation / extra-zero exclusion / boundary avoidance が別途必要。
8. `z^2` は holomorphic だが `|z|²` は holomorphic ではない。両者を置換しない。
9. evenness `Xi_centered(-z) = Xi_centered(z)` は RH ではない。off-axis zero pair `±z` を許す。
10. PPW-017 radial contour mass は zero-dependent weight を使っている。PPW-019 fixed Xi second moment と同じ object ではない。
11. `pascalCriticalMirrorZeroWindowSecondMomentDefect = 0` を新 theorem 名で言い換えて completion 条件にしない。
12. 新しい `Provider : Prop` を置くだけで研究前進としない。

---

## 16. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMultiplicityLocalChargeBridge
lake build DkMath.RH
./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiMultiplicityLocalChargeBridge
git diff --check
```

新規 module に

```text
sorry
axiom
admit
```

を追加しない。

### mandatory acceptance

```text
pascalCenteredXiZeros
pascalCenteredXiZeroMultiplicity

analyticOrderAt_pascalCenteredXi_ne_top_of_mem
pascalCenteredXiZeroMultiplicity_pos

analyticOrderAt_pascalRiemannXiKernel_eq_riemannZeta_of_nontrivial
analyticOrderAt_pascalCenteredXi_sub_center_eq_riemannZeta
pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity

exists_pascalCenteredXi_local_factorization
tendsto_mul_pascalCenteredXiNegLogDeriv_zeroMultiplicity

exists_isPascalCenteredXiIsolatingRadius
pascalCenteredXiIsolatingRadius_spec
circleIntegral_pascalCenteredXiNegLogDeriv_eq
circleIntegral_pascalCenteredXiNegLogDeriv_sub_center_eq_riemannMultiplicity

pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass_eq
pascalCriticalMirrorZeroWindowNormalizedCenteredXiLocalContourMass_eq

pascalCriticalMirrorZeroWindowNormalizedCenteredXiWeightedLocalContourMass_eq
pascalCriticalMirrorZeroWindowNormalizedCenteredXiSecondLocalContourMass_eq
```

### strongly recommended

```text
isClosed_pascalCenteredXiZeros
isDiscrete_pascalCenteredXiZeros
finite_pascalCenteredXiZeros_in_compact

analyticOrderAt_pascalRiemannXiKernel_eq_completedRiemannZeta_of_nontrivial
analyticOrderAt_completedRiemannZeta_eq_riemannZeta_of_nontrivial

analyticAt_completedRiemannZeta_of_ne_zero_one
analyticAt_GammaR_inv
```

---

## 17. PPW-019 の完了条件の意味

PPW-019 が Green になれば、PPW-018 の fixed Xi は単に「zero-independent entire function」であるだけでなく、既存 zeta zero multiplicity を exact に保持し、同じ fixed log derivative が local charge を読むところまで到達する。

さらに fixed polynomial `z²` を掛けた一つの analytic observableから、PPW-016 の centered complex second momentを有限 local-circle accounting として再取得できる。

その時点で PPW-020 の問いは明確になる。

```text
同じ fixed integrand / fixed weight を持つ local circles の有限和
  ↓
一つの fixed outer contour へ変形できるか
  ↓
その outer contour 内の Xi zero set を PPW window と exact に一致させられるか
  ↓
fixed holomorphic moment と radial q2 mass の残差は何か
```

PPW-019 は、outer-contour argument principle へ進む前の multiplicity-safe fixed-observable checkpoint とする。
