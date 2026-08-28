# PPW-021 — centered Xi finite-pole subtraction / one outer-contour residue bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-020 complete Green
previous implementation: 45c9824faecbebceec1f61623bcbbc8a8571fca8
Lean toolchain: v4.32.2
mathlib rev: 905b95818eb32af7874a58b427f50c1711a5e96c
```

PPW-020 までで、fixed entire function

```text
pascalCenteredRiemannXiKernel : ℂ → ℂ
```

について以下が Green になった。

```text
centered Xi zero set = centered nontrivial zeta zero set
closed centered disk の Xi zero Finset = PPW window の centered image
Xi intrinsic multiplicity = zeta multiplicity
boundary-safe radius は任意の閾値より外側に存在
outer circle 上では -Xi'/Xi が continuous / CircleIntegrable
```

さらに PPW-019 では、各零点の独立 local circle に対して fixed integrand

```text
pascalCenteredXiNegLogDeriv
```

と fixed holomorphic weight `h` を使い、local residue charge が exact に構成されている。

PPW-021 の目的は、ここまでの有限 local-circle accounting を **一つの fixed outer circle** へ移すことである。

今回の中心 theorem は、boundary-safe `R` と entire differentiable weight `h` に対する

```text
circleIntegral (fun z => h z * pascalCenteredXiNegLogDeriv z) 0 R
```

の weighted finite residue formula である。

一般 residue theorem を新たに仮定しない。disk 内の有限個の Xi zero の principal part を明示的に差し引き、removable singularity を有限個だけ埋め、Mathlib の Cauchy-Goursat を適用する。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalCenteredXiOuterContourResidueBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` の PPW-020 import 直後へ公開 import を追加する。

---

## 3. pinned Mathlib API audit

current branch の `lean/dk_math/lake-manifest.json` は mathlib

```text
905b95818eb32af7874a58b427f50c1711a5e96c
```

を pin している。

この rev で以下を確認済みである。

### 3.1 Cauchy-Goursat with countable exceptional set

```lean
#check Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
```

概形は

```text
0 ≤ R
s.Countable
ContinuousOn f (closedBall c R)
∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z
```

から

```text
circleIntegral f c R = 0
```

を与える。

したがって PPW-021 では、有限 zero set を exceptional set とし、**零点上では differentiability を要求せず continuity だけを removable patch で回復**すればよい。

### 3.2 simple Cauchy kernel integral

```lean
#check circleIntegral.integral_sub_inv_of_mem_ball
```

`a ∈ Metric.ball 0 R` なら

```text
circleIntegral (fun z => (z - a)⁻¹) 0 R
```

は標準正向きで `2 * π * I` になる。

### 3.3 circle integral linearity

current `CircleIntegral.lean` に以下がある。

```lean
#check circleIntegral.integral_add
#check circleIntegral.integral_sub
#check circleIntegral.integral_fun_sum
#check circleIntegral.integral_const_mul
#check CircleIntegrable.fun_sum
```

実装開始時に local toolchain で exact implicit arguments を再確認すること。

### 3.4 derivative as slope limit

```lean
#check hasDerivAt_iff_tendsto_slope
#check HasDerivAt.tendsto_slope
```

`slope h a w` は punctured neighborhood で

```text
(w - a)⁻¹ • (h w - h a)
```

に一致し、`h` が differentiable なら `deriv h a` へ収束する。

### 3.5 removable point patch

```lean
#check continuousAt_update_same
#check continuousWithinAt_update_same
```

特に

```text
ContinuousAt (Function.update f a L) a
```

は

```text
Tendsto f (𝓝[≠] a) (𝓝 L)
```

へ還元できる。

これは有限 zero set の removable singularity を一個ずつ埋める際に使用できる。

---

## 4. Phase A — weighted disk moment と principal parts

### 4.1 generic weighted disk moment

まず Xi disk 自身を index にした fixed-weight moment を置く。

```lean
noncomputable def pascalCenteredXiZeroDiskWeightedMoment
    (h : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∑ a ∈ pascalCenteredXiZeroDiskFinset R,
    (pascalCenteredXiZeroMultiplicity a : ℂ) * h a
```

special cases:

```text
h = 1    → multiplicity mass
h = z^2  → centered complex second moment
```

必須 theorem:

```lean
@[simp] theorem pascalCenteredXiZeroDiskWeightedMoment_one
    (R : ℝ) :
    pascalCenteredXiZeroDiskWeightedMoment (fun _ => 1) R =
      (pascalCenteredXiZeroDiskMultiplicity R : ℂ)
```

```lean
@[simp] theorem pascalCenteredXiZeroDiskWeightedMoment_second
    (R : ℝ) :
    pascalCenteredXiZeroDiskWeightedMoment pascalCenteredXiSecondWeight R =
      pascalCenteredXiZeroDiskSecondMoment R
```

名前は多少変更してよい。

### 4.2 one outer contour の generic definition

```lean
noncomputable def pascalCenteredXiWeightedOuterContourMass
    (h : ℂ → ℂ) (R : ℝ) : ℂ :=
  circleIntegral
    (fun z => h z * pascalCenteredXiNegLogDeriv z)
    0 R
```

PPW-020 の既存

```text
pascalCenteredXiOuterContourMass
pascalCenteredXiSecondOuterContourMass
```

は `h = 1`, `h = z^2` の special case として後で接続する。

### 4.3 principal part

centered Xi zero `a` における weighted integrand の residue は

```text
-(pascalCenteredXiZeroMultiplicity a : ℂ) * h a
```

である。

従って principal part を例えば

```lean
noncomputable def pascalCenteredXiWeightedPrincipalPart
    (h : ℂ → ℂ) (a w : ℂ) : ℂ :=
  (-(pascalCenteredXiZeroMultiplicity a : ℂ) * h a) * (w - a)⁻¹
```

とする。

finite disk sum:

```lean
noncomputable def pascalCenteredXiDiskWeightedPrincipalPartSum
    (h : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  ∑ a ∈ pascalCenteredXiZeroDiskFinset R,
    pascalCenteredXiWeightedPrincipalPart h a w
```

raw regularizer:

```lean
noncomputable def pascalCenteredXiDiskWeightedRawRegularizer
    (h : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  h w * pascalCenteredXiNegLogDeriv w -
    pascalCenteredXiDiskWeightedPrincipalPartSum h R w
```

この raw function は zero 以外では analytic だが、Mathlib の totalized division のため zero 上の値は removable limit と一致するとは限らない。従ってこのまま Cauchy-Goursat の continuity hypothesis に使用してはならない。

---

## 5. Phase B — 一個の Xi pole を exact に除去する

ここが PPW-021 の第一 load-bearing 部分。

PPW-019 の

```text
exists_pascalCenteredXi_local_factorization
```

から、zero `a` に対して

```text
Xi(w) = (w-a)^m * g(w)
g analytic at a
g(a) ≠ 0
m = pascalCenteredXiZeroMultiplicity a
```

を得る。

punctured neighborhood では

```text
pascalCenteredXiNegLogDeriv w
```

を exact に

```text
-(m : ℂ) * (w - a)⁻¹ - logDeriv g w
```

へ展開できる。

強く推奨する helper:

```lean
theorem exists_pascalCenteredXiNegLogDeriv_local_expansion
    {a : ℂ} (ha : a ∈ pascalCenteredXiZeros) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g a ∧
      g a ≠ 0 ∧
      pascalCenteredXiNegLogDeriv =ᶠ[𝓝[≠] a]
        (fun w =>
          -(pascalCenteredXiZeroMultiplicity a : ℂ) * (w - a)⁻¹ -
            logDeriv g w)
```

名前・statement の細部は変更可。

### 5.1 weighted own-pole cancellation

`h` が complex differentiable なら

```text
h(w) * (-m/(w-a)) - (-m*h(a))/(w-a)
```

は

```text
-m * (h(w)-h(a))/(w-a)
```

となる。

`HasDerivAt.tendsto_slope` により、この項は

```text
-(m : ℂ) * deriv h a
```

へ収束する。

一方 `g(a) ≠ 0` と analyticity により `logDeriv g` は `a` で連続。

従って必須の removable limit theorem:

```lean
theorem exists_tendsto_pascalCenteredXiWeightedOwnPoleCanceled
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {a : ℂ} (ha : a ∈ pascalCenteredXiZeros) :
    ∃ L : ℂ,
      Tendsto
        (fun w =>
          h w * pascalCenteredXiNegLogDeriv w -
            pascalCenteredXiWeightedPrincipalPart h a w)
        (𝓝[≠] a) (𝓝 L)
```

可能なら選んだ local factor `g` を使い、limit を

```text
-(m : ℂ) * deriv h a - h a * logDeriv g a
```

と explicit にしてよい。

ただし最終 outer theorem にはこの local regular value の具体値は不要である。

---

## 6. Phase C — finite principal-part subtraction の removable limit

`R` を固定し、

```text
S := pascalCenteredXiZeroDiskFinset R
```

とする。

`a ∈ S` に対して、raw regularizer は

```text
own-pole-canceled part
  -
other principal parts
```

に分解できる。

`b ∈ S.erase a` なら `b ≠ a` なので

```text
w ↦ pascalCenteredXiWeightedPrincipalPart h b w
```

は `a` の近傍で continuous / differentiable である。

有限和ゆえ、Phase B と合わせて raw regularizer 全体にも有限 removable limit が存在する。

必須 theorem:

```lean
theorem exists_tendsto_pascalCenteredXiDiskWeightedRawRegularizer
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {a : ℂ}
    (ha : a ∈ pascalCenteredXiZeroDiskFinset R) :
    ∃ L : ℂ,
      Tendsto
        (pascalCenteredXiDiskWeightedRawRegularizer h R)
        (𝓝[≠] a) (𝓝 L)
```

proof では `Finset.sum_erase` / `sum_erase_add` 等を使い own term と others を明示的に分離すること。

**停止線:** `rawRegularizer a` 自身がこの `L` に等しいとは仮定しない。totalized division の点値は removable value を保証しない。

---

## 7. Phase D — finite removable patch

Cauchy-Goursat に必要なのは closed disk 上の continuity である。

実装方法は自由だが、推奨は次のいずれか。

### Route A — chosen removable values + finite membership patch

各 `a ∈ S` について Phase C の limit `L_a` を `Classical.choose` で選び、

```text
if w ∈ S then L_w else rawRegularizer(w)
```

という patched function を作る。

### Route B — `Function.update` を finite に反復

各 zero について `Function.update` で removable value を埋め、`continuousAt_update_same` を使う。

どちらでもよい。

外部公開 API として regularizer の具体的 patch 構造を固定する必要はない。proof-local `let` / private helper にしてもよい。

ただし以下の theorem-facing facts は必要。

### 7.1 closed disk continuity

```lean
theorem pascalCenteredXiDiskWeightedRegularizer_continuousOn_closedBall
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ContinuousOn
      (pascalCenteredXiDiskWeightedRegularizer h R)
      (Metric.closedBall 0 R)
```

名前は実装に合わせて変更可。

zero `a ∈ S` では Phase C の punctured limit と `continuousAt_update_same` を使う。

zero でない closed-disk point `w` では、PPW-020 の disk classification から

```text
pascalCenteredRiemannXiKernel w ≠ 0
```

を得て raw function の ordinary continuity を使う。

### 7.2 open disk differentiability off finite zero set

```lean
theorem pascalCenteredXiDiskWeightedRegularizer_differentiableAt_of_mem_ball_not_mem
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball 0 R)
    (hwS : w ∉ pascalCenteredXiZeroDiskFinset R) :
    DifferentiableAt ℂ
      (pascalCenteredXiDiskWeightedRegularizer h R) w
```

`w ∈ ball 0 R` かつ `w ∉ S` なら、Xi zero であれば PPW-020 の disk Finset に入るはずなので Xi は非零。

また `w ≠ a` for all `a ∈ S` なので principal-part finite sum も differentiable。

finite patch は `w` の近傍で raw function と一致することを使う。

### 7.3 sphere 上では raw と patched が一致

boundary-safe `R` では sphere 上に zero は無い。

```lean
theorem pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_sphere
    {h : ℂ → ℂ} {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    Set.EqOn
      (pascalCenteredXiDiskWeightedRegularizer h R)
      (pascalCenteredXiDiskWeightedRawRegularizer h R)
      (Metric.sphere 0 R)
```

を用意すると後続 integral congruence が簡単になる。

---

## 8. Phase E — Cauchy-Goursat で regularizer outer integral を 0 にする

finite exceptional set

```text
↑(pascalCenteredXiZeroDiskFinset R) : Set ℂ
```

は Countable。

Phase D の continuity / differentiability を

```lean
Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
```

へ渡す。

必須 theorem:

```lean
theorem circleIntegral_pascalCenteredXiDiskWeightedRegularizer_eq_zero
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    circleIntegral
      (pascalCenteredXiDiskWeightedRegularizer h R)
      0 R = 0
```

さらに sphere 上 EqOn から

```lean
theorem circleIntegral_pascalCenteredXiDiskWeightedRawRegularizer_eq_zero
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    circleIntegral
      (pascalCenteredXiDiskWeightedRawRegularizer h R)
      0 R = 0
```

を得る。

これが一般 residue theorem を使わない finite-pole subtraction の核心である。

---

## 9. Phase F — principal-part outer integrals

boundary-safe `R` と

```text
a ∈ pascalCenteredXiZeroDiskFinset R
```

から PPW-020 の

```text
mem_centeredXiZeroDiskFinset_iff_mem_ball_of_boundarySafe
```

を使い

```text
a ∈ Metric.ball 0 R
```

を得る。

従って

```lean
circleIntegral.integral_sub_inv_of_mem_ball
```

から

```text
∮ (z-a)⁻¹ dz = 2πi
```

である。

必須 helper:

```lean
theorem circleIntegral_pascalCenteredXiWeightedPrincipalPart_eq
    {h : ℂ → ℂ} {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R)
    {a : ℂ} (ha : a ∈ pascalCenteredXiZeroDiskFinset R) :
    circleIntegral
      (pascalCenteredXiWeightedPrincipalPart h a)
      0 R =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity a : ℂ) * h a
```

multiplication order は `ring` で整理してよい。

finite sum 版:

```lean
theorem circleIntegral_pascalCenteredXiDiskWeightedPrincipalPartSum_eq
    {h : ℂ → ℂ} {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    circleIntegral
      (pascalCenteredXiDiskWeightedPrincipalPartSum h R)
      0 R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h R
```

`CircleIntegrable.fun_sum` と `circleIntegral.integral_fun_sum` を使用する。

---

## 10. Phase G — generic one outer-contour residue theorem

Phase E で

```text
outer weighted integrand - principal part sum
```

の circle integral が `0`。

Phase F で principal part sum の integral が exact に評価済み。

従って PPW-021 の主 theorem:

```lean
theorem pascalCenteredXiWeightedOuterContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiWeightedOuterContourMass h R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h R
```

を完成させる。

これは今回の第一最終 endpoint。

数学的内容は

```text
∮ h(z) (-Xi_c'(z)/Xi_c(z)) dz
  = -2πi Σ_{a inside} m_a h(a)
```

である。

一般 residue theorem / argument principle の公理追加ではなく、current disk の finite zero list に対する explicit finite-pole subtraction から証明すること。

normalized generic theorem も推奨:

```lean
theorem pascalCenteredXiNormalizedWeightedOuterContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiWeightedOuterContourMass h R =
      -pascalCenteredXiZeroDiskWeightedMoment h R
```

---

## 11. Phase H — unweighted outer argument count

`h = 1` を specialize する。

既存 PPW-020 definition:

```text
pascalCenteredXiOuterContourMass R
```

について必須 theorem:

```lean
theorem pascalCenteredXiOuterContourMass_eq_zeroDiskMultiplicity
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiOuterContourMass R =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroDiskMultiplicity R : ℂ)
```

normalized:

```lean
theorem pascalCenteredXiNormalizedOuterContourMass_eq_zeroDiskMultiplicity
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiOuterContourMass R =
      -(pascalCenteredXiZeroDiskMultiplicity R : ℂ)
```

PPW-020 transport を入れて window 版:

```lean
theorem pascalCenteredXiNormalizedOuterContourMass_eq_windowMultiplicity
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiOuterContourMass R =
      -(pascalCriticalMirrorZeroWindowMultiplicity R : ℂ)
```

さらに PPW-019 local-circle mass と one outer circle を exact に接続する。

必須 theorem:

```lean
theorem pascalCenteredXiOuterContourMass_eq_windowLocalContourMass
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiOuterContourMass R =
      pascalCriticalMirrorZeroWindowCenteredXiLocalContourMass R
```

ここで初めて

```text
finite independent local circles
```

と

```text
one fixed outer circle
```

が theorem として一致する。

---

## 12. Phase I — fixed `z²` outer second moment

`h(z) = z²` を specialize する。

既存 PPW-020 definition:

```text
pascalCenteredXiSecondOuterContourMass R
```

について必須 theorem:

```lean
theorem pascalCenteredXiSecondOuterContourMass_eq_zeroDiskSecondMoment
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiSecondOuterContourMass R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskSecondMoment R
```

normalized:

```lean
theorem pascalCenteredXiNormalizedSecondOuterContourMass_eq_zeroDiskSecondMoment
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiSecondOuterContourMass R =
      -pascalCenteredXiZeroDiskSecondMoment R
```

PPW window transport:

```lean
theorem pascalCenteredXiNormalizedSecondOuterContourMass_eq_windowCenteredSecondMoment
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiSecondOuterContourMass R =
      -pascalCriticalMirrorZeroWindowCenteredSecondMoment R
```

PPW-019 fixed local-circle second mass との equality:

```lean
theorem pascalCenteredXiSecondOuterContourMass_eq_windowSecondLocalContourMass
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiSecondOuterContourMass R =
      pascalCriticalMirrorZeroWindowCenteredXiSecondLocalContourMass R
```

これが PPW-021 の第二最終 endpoint。

---

## 13. Phase J — PPW-016 second-moment defect への outer-contour 置換

PPW-016 では

```text
SecondMomentDefect
  = RadialSecondMoment
      - Re(NormalizedCenteredSecondContourMass)
```

であった。

PPW-021 により holomorphic second-moment 側は one outer Xi circle へ置換できる。

強く推奨:

```lean
theorem pascalSecondMomentDefect_eq_radial_sub_centeredXiOuter_re
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCriticalMirrorZeroWindowSecondMomentDefect R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R -
        ((2 * Real.pi * Complex.I)⁻¹ *
          pascalCenteredXiSecondOuterContourMass R).re
```

または既存 normalized contour object と outer Xi contour の equality を先に置いてよい。

この theorem は defect の消滅を主張しない。

到達点は

```text
fixed entire Xi
  ↓
one fixed boundary-safe outer circle
  ↓
fixed holomorphic z² moment
  ↓
centered complex second moment
```

までである。

radial quantity

```text
Σ m_a |a|²
```

は依然として non-holomorphic であり、PPW-017 の mirror-frozen / CF2D q2 route に残る。

---

## 14. 今回やらないこと

PPW-021 では以下を実装しない。

```text
一般 residue theorem のライブラリ化
一般 argument principle API の大規模実装
|z|² を holomorphic weight とすること
radial q2 mass = fixed Xi outer contour
SecondMomentDefect = 0
HorizontalEnergy = 0
primeMirror window energy = 0
RiemannHypothesis
critical-strip finite PHZ convergence
Li / Weil positivity
explicit formula からの新規 positivity estimate
```

---

## 15. Stop conditions / audit warnings

1. raw regularizer の zero 上の totalized valueを removable limit と同一視しない。
2. principal part の residue sign は `pascalCenteredXiNegLogDeriv = -Xi'/Xi` に由来し `-m` である。符号を途中で反転させない。
3. weight `h` の pole cancellation では `h(w)` を `h(a)` に無条件置換しない。差 `h(w)-h(a)` から slope / derivative 項が出る。
4. multiplicity `m > 1` を simple zero として扱わない。PPW-019 intrinsic multiplicity をそのまま使う。
5. disk zero Finset の completeness は PPW-020 global classification に依存する。別の部分集合へ勝手に縮めない。
6. closed disk と open disk interior の差は boundary-safe hypothesis を通して処理する。
7. sphere 上に zero がある radius に outer theorem を適用しない。
8. Cauchy-Goursat の exceptional set は finite zero setでよいが、continuity は zero 上も必要である。removable patch を省略しない。
9. `circleIntegral.integral_sub_inv_of_mem_ball` を使う前に各 zero が open ball 内にあることを boundary-safe theorem から得る。
10. local-circle sum と outer circle を「同じ integrandだから」だけで同一視しない。Phase E–G の subtraction proof を通す。
11. `z²` outer moment が Green になっても `|z|²` radial momentは得られない。
12. outer second moment と radial second moment の一致を completion 条件にしない。それは horizontal-energy zero と同値な核心へ戻る。
13. `SecondMomentDefect = 0` と同値な theorem を別名の Provider として追加しない。
14. RH を示す theorem は今回の acceptance に含めない。

---

## 16. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
lake build DkMath.RH
./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
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
pascalCenteredXiZeroDiskWeightedMoment
pascalCenteredXiWeightedOuterContourMass
pascalCenteredXiWeightedPrincipalPart
pascalCenteredXiDiskWeightedPrincipalPartSum
pascalCenteredXiDiskWeightedRawRegularizer

exists_tendsto_pascalCenteredXiWeightedOwnPoleCanceled
exists_tendsto_pascalCenteredXiDiskWeightedRawRegularizer

circleIntegral_pascalCenteredXiDiskWeightedRegularizer_eq_zero
circleIntegral_pascalCenteredXiWeightedPrincipalPart_eq
circleIntegral_pascalCenteredXiDiskWeightedPrincipalPartSum_eq

pascalCenteredXiWeightedOuterContourMass_eq

pascalCenteredXiOuterContourMass_eq_zeroDiskMultiplicity
pascalCenteredXiNormalizedOuterContourMass_eq_windowMultiplicity
pascalCenteredXiOuterContourMass_eq_windowLocalContourMass

pascalCenteredXiSecondOuterContourMass_eq_zeroDiskSecondMoment
pascalCenteredXiNormalizedSecondOuterContourMass_eq_windowCenteredSecondMoment
pascalCenteredXiSecondOuterContourMass_eq_windowSecondLocalContourMass
```

### strongly recommended

```text
exists_pascalCenteredXiNegLogDeriv_local_expansion

pascalCenteredXiDiskWeightedRegularizer_continuousOn_closedBall
pascalCenteredXiDiskWeightedRegularizer_differentiableAt_of_mem_ball_not_mem
pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_sphere
circleIntegral_pascalCenteredXiDiskWeightedRawRegularizer_eq_zero

pascalCenteredXiNormalizedWeightedOuterContourMass_eq
pascalCenteredXiNormalizedOuterContourMass_eq_zeroDiskMultiplicity
pascalCenteredXiNormalizedSecondOuterContourMass_eq_zeroDiskSecondMoment

pascalSecondMomentDefect_eq_radial_sub_centeredXiOuter_re
```

regularizer の public 名は実装都合で変更可。重要なのは、zero 上の continuity を removable patch で実証し、generic weighted outer theorem が explicit finite-pole subtractionから導かれていることである。

---

## 17. PPW-021 完了条件の意味

PPW-021 が Green になれば、PPW-015 から続いていた

```text
local residue
  ↓
independent local circles
  ↓
finite local-circle sum
```

に対して、初めて

```text
one boundary-safe outer circle
```

が exact に接続される。

しかも integrand は zero-dependent ではなく、PPW-018 で導入した一つの fixed entire Xi の negative log derivativeである。

unweighted では disk 内 multiplicity countを one outer circle から読み、fixed weight `z²` では centered complex second momentを one outer circle から読む。

従って PPW-021 完了後の本質的な残差は、もはや contour bookkeeping ではない。

```text
fixed holomorphic outer Xi second moment
        vs
non-holomorphic radial / CF2D q2 mass
```

この差が PPW-016 の horizontal energy / SecondMomentDefect そのものとして残る。

次 checkpoint では、この radial side に zero-list-independent な情報を供給できるかを監査する。critical-mirror pairing、completed-Xi symmetry、prime-side explicit formula、CF2D q2 invariant のいずれを使う場合も、`|z|²` を holomorphic weightへ偽装しないことを最優先停止線とする。