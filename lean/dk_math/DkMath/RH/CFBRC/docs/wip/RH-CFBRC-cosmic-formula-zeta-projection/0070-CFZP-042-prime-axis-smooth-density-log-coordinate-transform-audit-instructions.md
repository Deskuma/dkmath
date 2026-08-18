# CFZP-0070 / CFZP-042

## prime-axis smooth density / log-coordinate transform — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-039: eligible prime-axis signed mass = exact periodic leading carrier + `K / log p` remainder; exponential one-period transform model
- CFZP-040: finite Abel prime sum; smooth model `x / log x`; exact prime-counting discrepancy split
- CFZP-041: one carrier cell = smooth Abel + discrepancy; smooth/discrepancy reservoir -> radial endpoint

CFZP-041 は Green-A。current source で特に次が CLOSED:

```text
cfzp041CarrierCellNaturalLeft_le_right
cfzp041EligiblePrimeAxisBlockSupport_eq_carrierCellSupport
cfzp041EligibleLeadingCarrierMass_eq_cellMass
cfzp041EligibleRemainderDebt_eq_cellDebt
cfzp041CellMass_eq_smooth_add_discrepancy
cfzp041PrimeCountingDiscrepancyCellDebt
Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt
cfzp041SmoothSubDiscrepancy_le_cellMass
cfzp041SmoothDiscrepancyCellReservoir_implies_radialContactDeficit_le
```

**CFZP-042 の目的は prime distribution ではなく、CFZP-041 に残った `SmoothAbelCarrierModel` の解析的正体を exact に解剖すること。まず `x / log x` の derivative density に integration by parts で落とし、次に `x = exp u` で log-coordinate へ移し、最後に一周期 cell を CFZP-039 の exponential carrier transform と slowly-varying density weight の variation error に exact 分解する。**

本段の最終 structural identity は概念的に

```text
SmoothCell(U)
=
exp(β U) *
  ( q(U) * ExponentialCarrierTransform(c)
    + WeightVariationError(U,c) )
```

where

```text
β = 1 - σ
q(u) = 1/u - 1/u^2
U = c + n P
P = 2π / T
```

である。

**042 では variation error の小ささや SmoothCell の eventual positivity までは要求しない。** そこは次段の quantitative target とする。

本段では PNT、prime-counting discrepancy decay、infinite prime sums、summability、limit exchange、automatic `σ < 1`、exceptional/higher-power residual elimination、CFZP-018 provider、RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothDensityLogCoordinateTransformAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisSmoothDensityLogCoordinateTransformAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothDiscrepancyCellReservoirAudit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
```

current Mathlib では integration by parts / substitution に

```text
intervalIntegral.integral_mul_deriv_eq_deriv_mul
intervalIntegral.integral_deriv_smul_comp'
```

等がある。deprecated alias より current preferred theorem を使う。

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — smooth prime-counting density

CFZP-040 の elementary smooth model

```text
M(x) = x / log x
```

の derivative を first-class にする。

候補:

```lean
noncomputable def cfzp042PrimeCountingSmoothDensity (x : ℝ) : ℝ :=
  1 / Real.log x - 1 / (Real.log x) ^ 2
```

`1 < x` の下で少なくとも

```text
HasDerivAt cfzp040PrimeCountingSmoothModel
  (cfzp042PrimeCountingSmoothDensity x) x
```

を閉じる。

同値な algebraic normal form

```text
(log x - 1) / (log x)^2
```

との equality も helper として追加してよい。

さらに later positivity 用に

```text
1 < x -> 0 <= cfzp042PrimeCountingSmoothDensity x
```

または strict version `Real.exp 1 < x -> 0 < ...` が短く閉じるなら追加してよい。ただし Gate A の本質は derivative identity。

---

## 3. Gate B — smooth Abel model = density integral

略記:

```text
F(x) := cfzp040PrimeAxisCarrierTestFunction ε W x
M(x) := cfzp040PrimeCountingSmoothModel x
m(x) := cfzp042PrimeCountingSmoothDensity x
```

CFZP-040 の smooth Abel model は

```text
F(b) M(b) - F(a) M(a) - ∫_{(a,b]} F'(x) M(x) dx
```

である。

integration by parts から exact に

```text
SmoothAbelCarrierModel(a,b)
=
∫_{(a,b]} F(x) * m(x) dx
```

へ落とす。

候補 theorem:

```lean
theorem cfzp042SmoothAbelCarrierModel_eq_densityIntegral
    {ε a b : ℝ}
    (hε : ε ≠ 0)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzp040SmoothAbelCarrierModel ε W a b =
      ∫ x in Set.Ioc a b,
        cfzp040PrimeAxisCarrierTestFunction ε W x *
          cfzp042PrimeCountingSmoothDensity x := by
  ...
```

`1 ≤ a` で `log x ≠ 0` が足りない箇所があれば `1 < a` に強めてよい。cell specialization では later-cell condition を供給できる。

proof spine:

1. `cfzp040PrimeAxisCarrierTestFunction_hasDerivAt`
2. Gate A の smooth model derivative
3. current `intervalIntegral.integral_mul_deriv_eq_deriv_mul` または同等 theorem
4. `a ≤ b` で interval integral と `Set.Ioc` integral を変換
5. `deriv F` を HasDerivAt uniqueness で explicit derivative と一致させる

可能なら elementary continuity on compact interval から必要 interval-integrability を内部で閉じる。

もし current API 上、integrability hypotheses を theorem 引数に残す方が短く堅い場合は許容する。ただし **cell specialization が 041 の既存 regularity data から直接使える形**にする。

---

## 4. Gate C — log density weight and `x = exp u` substitution

log-coordinate density weight:

```lean
noncomputable def cfzp042LogDensityWeight (u : ℝ) : ℝ :=
  1 / u - 1 / u ^ 2
```

cell endpoints:

```text
L := cfzp039CarrierCellLeft  W c n
R := cfzp039CarrierCellRight W c n
```

log-coordinate smooth cell integral:

```lean
noncomputable def cfzp042SmoothLogCellIntegral
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  ∫ u in L..R,
    Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W u *
      cfzp042LogDensityWeight u
```

`x = exp u`, `dx = exp u du` と

```text
exp u * exp (-σ u) = exp ((1 - σ) u)
```

を使い、late/safe cell で

```text
cfzp040SmoothAbelCarrierModel ε W (exp L) (exp R)
=
cfzp042SmoothLogCellIntegral ε W c n
```

を exact に閉じる。

ここでは current Mathlib の

```text
intervalIntegral.integral_deriv_smul_comp'
```

等の substitution API を優先する。

重要:

- `log (exp u) = u` を exact に使う。
- `L < R` は carrier period positivity から既存 theorem で得る。
- set integral / interval integral の orientation を曖昧にしない。
- `β = 1 - σ` は `cfzp039PrimeAxisGrowthExponent` を使う。

---

## 5. Gate D — natural-period translation to `[0,P]`

```text
P := cfzp036PrimeAxisCarrierPeriod W
U := cfzp039CarrierCellLeft W c n = c + n P
```

まず leading carrier の Nat-period translation helper を閉じる。

候補:

```text
carrier(c + n*P + t) = carrier(c + t)
```

`cfzp036PrimeAxisLeadingPeriodicCarrier_periodic` を Nat induction で持ち上げればよい。

次に translation `u = U + t` で

```text
SmoothLogCellIntegral
=
exp(β U) *
  ∫ t in 0..P,
    exp(β t) * carrier(c+t) * q(U+t)
```

を exact に閉じる。

候補 definition:

```lean
noncomputable def cfzp042TranslatedSmoothCellIntegral
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (cfzp039PrimeAxisGrowthExponent W *
      cfzp039CarrierCellLeft W c n) *
    ∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
      Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
        cfzp042LogDensityWeight
          (cfzp039CarrierCellLeft W c n + t)
```

`cfzp042SmoothLogCellIntegral = cfzp042TranslatedSmoothCellIntegral` を証明する。

---

## 6. Gate E — close the exponential one-period carrier integral identity

CFZP-039 では closed-form model

```text
cfzp039ExponentialCarrierPeriodTransform ε W c
```

を定義したが、interval-integral identification は Gap に残していた。

ここで first-class moment を定義する。

```lean
noncomputable def cfzp042ExponentialCarrierMoment
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
    Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)
```

そして `ε ≠ 0` の下で

```text
cfzp042ExponentialCarrierMoment ε W c
=
cfzp039ExponentialCarrierPeriodTransform ε W c
```

を exact に閉じる。

数学的 primitive は

```text
∫ exp(βt) sin(φ+Tt) dt
∫ exp(βt) cos(φ+Tt) dt
```

であり、一周期 `P = 2π/T` では endpoint phase が同じになるため、CFZP-039 の transformed coefficients

```text
Sβ = β*S + T*C
Cβ = β*C - T*S
```

がそのまま現れる。

推奨 proof:

1. `cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair`
2. explicit antiderivative を定義
3. `HasDerivAt` + FTC で endpoint difference
4. `T * P = 2π`
5. `sin/cos` period simplification
6. ring / field normalization

**この Gate E は 042 の主要 completion target。** ここで 039 の `noIntervalIntegralIdentification` に相当する未接続を実質的に解消する。

---

## 7. Gate F — exact main transform + slowly-varying weight error split

cell left coordinate:

```text
U := cfzp039CarrierCellLeft W c n
```

weight variation error を定義する。

```lean
noncomputable def cfzp042SmoothWeightVariationError
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
    Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
      (cfzp042LogDensityWeight
          (cfzp039CarrierCellLeft W c n + t) -
        cfzp042LogDensityWeight
          (cfzp039CarrierCellLeft W c n))
```

Gate D + Gate E と単なる integral linearity から exact に

```text
SmoothCell
=
exp(β U) *
  ( q(U) * cfzp039ExponentialCarrierPeriodTransform ε W c
    + cfzp042SmoothWeightVariationError ε W c n )
```

を閉じる。

候補 theorem:

```lean
theorem cfzp042SmoothAbelCell_eq_transform_add_weightError
    ... :
    cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) *
        (cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n) *
            cfzp039ExponentialCarrierPeriodTransform ε W c +
          cfzp042SmoothWeightVariationError ε W c n) := by
  ...
```

この theorem は prime distribution を含まない。

さらに短く閉じられるなら:

```text
1 < U -> 0 < q(U)
```

を追加する。

CFZP-039 の

```text
cfzp039ExponentialCarrierPeriodTransform_exists_pos
```

と合わせれば、次段は variation error の量的支配だけに集中できる。

---

## 8. Gap / firewall

候補:

```lean
inductive Cfzp042PrimeAxisSmoothDensityLogCoordinateTransformGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noSmoothWeightVariationErrorBound
  | noEventualSmoothAbelCellPositiveLowerBound
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination
```

Gate E を閉じたので、この新 module では `noIntervalIntegralIdentification` を Gap に再導入しない。

本段では以下を導入しない:

- PNT / Mertens / Dirichlet / Bertrand
- prime-counting discrepancy decay theorem
- prime-log equidistribution
- infinite prime sums
- summability / limit exchange
- automatic `σ < 1`
- variation error の無条件 negligible claim
- SmoothCell の無条件 positivity
- exceptional / higher-power residual elimination
- CFZP-018 provider
- RH

---

## 9. Roadmap

CFZP-042 entry を追加し、最低限:

```text
smooth counting density derivative: CLOSED
smooth Abel model -> x-density integral: CLOSED
x-density integral -> log-coordinate cell integral: CLOSED
period-cell translation to [0,P]: CLOSED
exponential carrier moment = CFZP-039 transform: CLOSED
smooth cell = transform main + weight-variation error: CLOSED
weight-variation quantitative bound: OPEN / GAP
eventual smooth-cell positive lower bound: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
exceptional/higher-power residual elimination: OPEN / GAP
```

を記録する。

---

## Completion criterion

Green の最小条件:

```text
Gate A CLOSED
Gate B CLOSED
Gate C CLOSED
Gate D CLOSED
Gate E CLOSED
Gate F CLOSED
public import added
roadmap updated
no new sorry / axiom / native_decide
```

042 完了時点の狙いは、「smooth model positivity」の問題を次の一式に完全圧縮すること:

```text
positive exponential carrier transform
vs.
slowly-varying q(u) weight error
```

prime distribution はまだ別問題として触らない。