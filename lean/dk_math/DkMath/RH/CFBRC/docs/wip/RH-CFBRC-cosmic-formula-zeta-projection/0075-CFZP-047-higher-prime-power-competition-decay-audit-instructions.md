# CFZP-0075 / CFZP-047

## higher-prime-power competition-kernel decay / residual elimination — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-043: positive transform phase で explicit smooth margin を構築
- CFZP-044: late exceptional prime-axis support / mass を exact `0` に消去
- CFZP-045: raw higher-prime-power mass を finite sigma-tail に圧縮
- CFZP-046: sigma-tail を distribution-free な cell counting で explicit exponential envelope に圧縮

CFZP-046 は Green-A。

current source で閉じた主要 API:

```text
cfzp046HigherPowerPairLogCoordinate_mem_carrierCell
cfzp046HigherPowerPairBlockSupport_card_le
cfzp046HigherPowerSigmaTailTerm_le_cellUniform
cfzp046HigherPowerSigmaTail_le_exponentialEnvelope
cfzp046HigherPowerSigmaTailExponentialEnvelope_eq_normalForm
cfzp046CarrierCellHigherPowerReferenceMass_le_exponentialEnvelope
cfzp046HigherPowerMarginCompetitionKernel
cfzp046HigherPowerEnvelope_le_half_explicitSmoothMargin_of_kernel
```

CFZP-046 の最後で、higher-power envelope と explicit smooth margin の競合は

```text
competitionKernel(U)
= 8 * U * K(ε,W) * exp(P/2)
    * ((U+P)/log 2 + 1)
    * exp(-U/2)
```

へ完全に還元された。

ここで

```text
U := cfzp039CarrierCellLeft W c n
P := cfzp036PrimeAxisCarrierPeriod W
R := U + P
```

である。

**CFZP-047 の目的は、この kernel が `U -> +∞` で `0` に収束することを Mathlib の標準 exponential limit だけで証明し、higher-prime-power residual domination を OPEN/GAP から CLOSED へ移すこと。**

本段の数学は prime distribution ではない。

```text
U * ((U+P)/log2 + 1) * exp(-U/2)
```

という高々二次多項式 × 指数減衰の standard real-analysis problem だけである。

current Mathlib には

```lean
Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n : ℕ) :
  Filter.Tendsto (fun x : ℝ => x ^ n * Real.exp (-x))
    Filter.atTop (nhds 0)
```

が存在する。これを `x = U / 2` に compose して使うのを第一選択とする。

また positive constant による scale には current API

```text
Filter.Tendsto.atTop_div_const
```

等がある。exact invocation syntax は current toolchain で確認してよい。

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、prime density theorem、infinite prime sums、summability、limit exchange、automatic `σ < 1`、discrepancy decay、prime-axis remainder elimination、CFZP-018 provider、global RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerCompetitionDecayAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaHigherPrimePowerCompetitionDecayAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerCellCountingEnvelopeAudit
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
```

`DkMath/RH.lean` に公開 import を追加する。

---

## 2. Gate A — cell-free competition profile

046 kernel は `c,n` に依存して見えるが、`R = U + P` を代入すれば dependence は cell-left coordinate `U` だけになる。

first-class profile を作る。

```lean
noncomputable def cfzp047HigherPowerCompetitionProfile
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (U : ℝ) : ℝ :=
  8 * U * cfzp045HigherPowerReferenceMassConstant ε W *
    Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
    ((U + cfzp036PrimeAxisCarrierPeriod W) / Real.log 2 + 1) *
    Real.exp (-U / 2)
```

そして exact rewrite:

```lean
theorem cfzp047HigherPowerMarginCompetitionKernel_eq_profile
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp046HigherPowerMarginCompetitionKernel ε W c n =
      cfzp047HigherPowerCompetitionProfile ε W
        (cfzp039CarrierCellLeft W c n) := by
  ...
```

proof は

```text
cfzp046CarrierCellRight_eq_left_add_period
```

を rewrite して ring normalization だけで閉じる。

この theorem は重要。以後の decay proof から `c,n` を一旦完全に外す。

### polynomial expansion

limit proof を短くするため、profile を degree 2 + degree 1 の二項へ exact 展開する。

定数 helper は任意。

例えば

```lean
noncomputable def cfzp047CompetitionQuadraticCoeff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  8 * cfzp045HigherPowerReferenceMassConstant ε W *
    Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) /
    Real.log 2

noncomputable def cfzp047CompetitionLinearCoeff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  8 * cfzp045HigherPowerReferenceMassConstant ε W *
    Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
    (cfzp036PrimeAxisCarrierPeriod W / Real.log 2 + 1)
```

として

```lean
theorem cfzp047HigherPowerCompetitionProfile_eq_quadratic_linear
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (U : ℝ) :
    cfzp047HigherPowerCompetitionProfile ε W U =
      cfzp047CompetitionQuadraticCoeff ε W *
          (U ^ 2 * Real.exp (-U / 2)) +
        cfzp047CompetitionLinearCoeff ε W *
          (U * Real.exp (-U / 2)) := by
  ...
```

を閉じる。

`Real.log 2 ≠ 0` は `Real.log_pos (by norm_num)` から得る。

---

## 3. Gate B — half-rate exponential decay helpers

必要なのは `m = 1,2` の二つだけ。generic theorem を無理に作る必要はない。

```lean
theorem cfzp047_tendsto_mul_exp_neg_half :
    Filter.Tendsto
      (fun U : ℝ => U * Real.exp (-U / 2))
      Filter.atTop (nhds 0) := by
  ...

 theorem cfzp047_tendsto_sq_mul_exp_neg_half :
    Filter.Tendsto
      (fun U : ℝ => U ^ 2 * Real.exp (-U / 2))
      Filter.atTop (nhds 0) := by
  ...
```

recommended proof spine:

1. `U -> U/2` が `atTop -> atTop` を証明する。
2. `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1` / `2` を compose。
3. exact identities

```text
U * exp(-U/2)
= 2 * ((U/2) * exp(-(U/2)))

U^2 * exp(-U/2)
= 4 * ((U/2)^2 * exp(-(U/2)))
```

で固定係数を戻す。

`Filter.Tendsto.atTop_div_const` を使えるなら第一候補。

**ここでは explicit epsilon threshold を自作しない。Mathlib にある standard limit theorem を使う。**

---

## 4. Gate C — competition profile tends to zero

Gate A/B から

```lean
theorem cfzp047HigherPowerCompetitionProfile_tendsto_zero
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow) :
    Filter.Tendsto
      (cfzp047HigherPowerCompetitionProfile ε W)
      Filter.atTop (nhds 0) := by
  ...
```

を閉じる。

これは fixed coefficients × two zero limits + addition だけ。

この theorem に

- `hε`
- `hsub`
- `hstrip`
- prime distribution hypothesis

は不要。

profile の eventual positivity / nonnegativity は main limit に不要。ただし short なら

```lean
cfzp047HigherPowerCompetitionProfile_nonneg_of_zero_le
```

を helper として追加してよい。

---

## 5. Gate D — carrier-cell left coordinate tends to +∞

043 には explicit Archimedean theorem:

```text
cfzp043_carrierCellLeft_eventually_ge W c K
```

が既にある。

これを standard filter statement に package する。

```lean
theorem cfzp047CarrierCellLeft_tendsto_atTop
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => cfzp039CarrierCellLeft W c n)
      Filter.atTop Filter.atTop := by
  ...
```

proof は `Filter.tendsto_atTop_atTop` を開いて 043 theorem を渡すだけでよい。

prime / sigma / epsilon は関係しない。

---

## 6. Gate E — actual cell competition kernel tends to zero

Gate A + Gate C + Gate D を compose:

```lean
theorem cfzp047HigherPowerMarginCompetitionKernel_tendsto_zero
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        cfzp046HigherPowerMarginCompetitionKernel ε W c n)
      Filter.atTop (nhds 0) := by
  ...
```

これは CFZP-046 の

```text
noHigherPowerCompetitionKernelEventualDecay
```

を直接閉じる theorem。

続いて positive threshold version:

```lean
theorem cfzp047HigherPowerMarginCompetitionKernel_eventually_le
    {ε δ : ℝ}
    (hδ : 0 < δ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp046HigherPowerMarginCompetitionKernel ε W c n ≤ δ := by
  ...
```

`kernel -> 0` と `0 < δ` から standard order-topology eventual theorem を使う。

例えば current Mathlib の `eventually_lt_of_tendsto_lt` 系 API を利用してよい。

さらに radial-late 条件を同じ `N` に統合する convenience theorem を Green-required とする。

```lean
theorem cfzp047_eventually_radialLate_and_kernel_le
    {ε δ : ℝ}
    (hδ : 0 < δ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp044RadialLateThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n ∧
      cfzp046HigherPowerMarginCompetitionKernel ε W c n ≤ δ := by
  ...
```

use:

```text
cfzp043_carrierCellLeft_eventually_ge
cfzp047HigherPowerMarginCompetitionKernel_eventually_le
```

and take `max` of the two natural thresholds.

---

## 7. Gate F — positive transform eventually beats the kernel

positive phase `c` を固定する。

```lean
theorem cfzp047_eventually_kernel_le_positiveTransform
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp044RadialLateThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n ∧
      cfzp046HigherPowerMarginCompetitionKernel ε W c n ≤
          cfzp039ExponentialCarrierPeriodTransform ε W c := by
  ...
```

Gate E に

```text
δ := cfzp039ExponentialCarrierPeriodTransform ε W c
```

を代入するだけ。

ここで初めて `hM` を使う。

---

## 8. Gate G — higher-power exponential envelope eventually <= half smooth margin

046 main comparisonを直接消費する。

```lean
theorem cfzp047HigherPowerEnvelope_eventually_le_half_explicitSmoothMargin
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp044RadialLateThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n ∧
      cfzp045HigherPowerReferenceMassConstant ε W *
          cfzp046HigherPowerSigmaTailExponentialEnvelope W c n ≤
        cfzp044ExplicitSmoothMargin ε W c n / 2 := by
  ...
```

proof:

1. Gate F から `hLate`, `hkernel`;
2. `cfzp046HigherPowerEnvelope_le_half_explicitSmoothMargin_of_kernel`。

ここには `hε2`, `hsub` はまだ不要。

---

## 9. Gate H — raw higher-prime-power residual eventually <= half smooth margin

ここが CFZP-047 の主要 elimination theorem。

```lean
theorem cfzp047HigherPowerReferenceMass_eventually_le_half_explicitSmoothMargin
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp044RadialLateThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n ∧
      cfzp034HigherPowerReferenceMass ε W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) ≤
        cfzp044ExplicitSmoothMargin ε W c n / 2 := by
  ...
```

proof spine:

1. Gate G で `K * envelope <= margin/2`;
2. `cfzp046CarrierCellHigherPowerReferenceMass_le_exponentialEnvelope`
   で raw mass `<= K * envelope`;
3. transitivity。

**この theorem が閉じた時点で higher-prime-power residual domination は OPEN/GAP ではなく CLOSED。**

もう caller が higher-power decay provider を持ち込む必要はない。

---

## 10. Gate I — positive phase + cofinal higher-power domination package

039 の positive-transform existence と Gate H を合成する。

```lean
theorem cfzp047_exists_positive_transform_cofinal_higherPower_domination
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W) :
    ∃ (c : ℝ) (N : ℕ),
      0 < cfzp039ExponentialCarrierPeriodTransform ε W c ∧
      ∀ n : ℕ, N ≤ n →
        cfzp044RadialLateThreshold ε W c ≤
            cfzp039CarrierCellLeft W c n ∧
        cfzp034HigherPowerReferenceMass ε W
            (cfzp040CarrierCellNaturalLeft W c n)
            (cfzp040CarrierCellNaturalRight W c n) ≤
          cfzp044ExplicitSmoothMargin ε W c n / 2 := by
  ...
```

use:

```text
cfzp039ExponentialCarrierPeriodTransform_exists_pos
cfzp047HigherPowerReferenceMass_eventually_le_half_explicitSmoothMargin
```

この theorem は higher powers に関して cofinal phase を完全に閉じる。

`hstrip` / `hsub` の automatic provider はこの段では作らない。

---

## 11. Gate J — remaining-half radial budget

higher-power residual が eventual に smooth margin の半分以下になったので、radial budget の caller が今後支払うべき残りを明示する。

```lean
def Cfzp047RemainingHalfExplicitSmoothMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp039PrimeAxisRemainderCellDebt ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) + D ≤
    cfzp044ExplicitSmoothMargin ε W c n / 2 + η
```

finite adapter:

```lean
theorem cfzp047RemainingHalfBudget_implies_radialContactDeficit_le
    {ε η D : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hHigher :
      cfzp034HigherPowerReferenceMass ε W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) ≤
        cfzp044ExplicitSmoothMargin ε W c n / 2)
    (... same finite SmoothAbel / discrepancy readiness as CFZP-044 ...)
    (hbudget : Cfzp047RemainingHalfExplicitSmoothMarginBudgetAt
      ε η D W c n) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  ...
```

proof:

1. remaining-half budget + `hHigher` から

```text
G_A + remainder + higher + D <= explicitMargin + η
```

を得る。
2. `cfzp044ExplicitSmoothMarginBudget_implies_radialContactDeficit_le` を適用。

`hsub` は 044 main theorem の signature に無ければ追加しない。current source exact signature に合わせること。

この Gate は 047 後の frontier を明瞭にするため Green-required。

### optional eventual adapter

短ければ Gate H と Gate J を合成し、固定 positive phase `c` について sufficiently late な cell では higher-power premise を自動供給できる theorem を追加してよい。

ただし analytic readiness / discrepancy / remainder budget 自体を自動化したふりはしない。

---

## 12. Mathematical interpretation to preserve in docstring

CFZP-047 で重要なのは単に「higher powers are small」ではない。

046 までで

```text
higher-power debt scale
~ polynomial(U) * exp((1/2 - σ)U)
```

smooth margin は

```text
smooth margin scale
~ exp((1 - σ)U) / U
```

である。

ratio は

```text
polynomial(U) * exp(-U/2)
```

となり、rectangle parameter `σ` は消える。

したがって higher-prime-power residual の eventual domination は prime distribution の事実ではなく、**`j >= 2` という prime-power geometry と exponential growth-rate separation の帰結**である。

この数学的意味を module docstring / roadmap に残す。

---

## 13. Gap / firewall

例:

```lean
inductive Cfzp047HigherPrimePowerCompetitionDecayGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothAbelLogCellReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noPrimeAxisRemainderCellDebtDecayProvider
  | noCofinalRemainingHalfBudgetProvider
```

重要:

**`noHigherPowerCompetitionKernelEventualDecay` と `noHigherPowerResidualDomination` を残さないこと。**

この checkpoint の目的はそこを閉じることだからである。

禁止:

- PNT
- Mertens
- Dirichlet
- Bertrand
- prime-log equidistribution
- prime density theorem
- infinite prime sums
- summability
- limit exchange
- automatic `σ < 1`
- unconditional discrepancy decay
- unconditional prime-axis remainder decay
- CFZP-018 provider
- global RH

---

## 14. Roadmap update

CFZP-047 節を追加し、最低限:

```text
cell-free higher-power competition profile: CLOSED
profile quadratic/linear exponential normal form: CLOSED
U * exp(-U/2) -> 0: CLOSED
U^2 * exp(-U/2) -> 0: CLOSED
higher-power competition profile -> 0: CLOSED
carrier cell-left -> +infinity: CLOSED
actual cell competition kernel -> 0: CLOSED
positive transform eventually dominates kernel: CLOSED
higher-power exponential envelope eventually <= half smooth margin: CLOSED
raw higher-power reference mass eventually <= half smooth margin: CLOSED
positive phase + cofinal higher-power domination package: CLOSED
remaining-half budget -> radial endpoint: CLOSED
higher-prime-power residual domination: CLOSED
prime-axis remainder-cell debt decay: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
automatic SmoothAbel -> SmoothLogCell readiness: OPEN / GAP
actual cofinal remaining-half budget provider: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

---

## 15. Green criterion

CFZP-047 is Green only if theorem-level chain is exact:

```text
competitionKernel(c,n)
  = profile(U_n)

profile(U)
  = A2 * U^2 * exp(-U/2)
    + A1 * U * exp(-U/2)

U^2 * exp(-U/2) -> 0
U   * exp(-U/2) -> 0

therefore
profile(U) -> 0

U_n -> +infinity

therefore
competitionKernel(c,n) -> 0

M(c) > 0
  -> eventually competitionKernel(c,n) <= M(c)
  -> eventually K * higherEnvelope(c,n) <= explicitSmoothMargin(c,n)/2
  -> eventually rawHigherPowerMass(c,n) <= explicitSmoothMargin(c,n)/2
```

and a finite radial adapter exists:

```text
G_A + remainderDebt + discrepancyDebt
  <= explicitSmoothMargin/2 + η

rawHigherPowerMass <= explicitSmoothMargin/2

--------------------------------------
G_B <= η
```

CFZP-047 完了後、higher-prime-power residual は radial closure の未解決項から外れる。

次 checkpoint は原則として **prime-axis remainder-cell debt** を解析し、これも explicit smooth margin に対して eventual に小さくできるかを攻める。prime-counting discrepancy はその後まで named debt として固定する。
