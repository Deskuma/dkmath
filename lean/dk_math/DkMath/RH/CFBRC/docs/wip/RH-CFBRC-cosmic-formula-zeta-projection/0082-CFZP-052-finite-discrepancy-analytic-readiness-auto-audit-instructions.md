# CFZP-0082 / CFZP-052

## finite discrepancy analytic readiness auto audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-049: carrier/remainder discrepancy を同一 finite Abel sensitivity へ統合
- CFZP-050: actual test functions から `CombinedSensitivity <= C_sens * exp(-sigma U)` を finite に実現
- CFZP-051: standard PNT ratio provider から eventual cell-relative discrepancy、さらに `CombinedDebt <= Margin / 8` まで reduction

CFZP-051 は Green-A。

---

## 0. 現在の frontier

CFZP-051 の Green-facing theorem

```lean
cfzp051_pntRatio_eventually_combinedDebt_le_eighthMargin
```

には arithmetic provider

```lean
Cfzp051PrimeCountingPNTRatioAtTop
```

とは別に、有限解析 readiness

```lean
∀ᶠ n : ℕ in Filter.atTop,
  Cfzp051FiniteDiscrepancyAnalyticReadyAt epsilon W c n
```

が残っている。

その中身は四つの有限 `IntegrableOn`:

```text
|carrier derivative|
carrier derivative * prime-counting discrepancy
|remainder derivative|
remainder derivative * prime-counting discrepancy
```

である。

**CFZP-052 の目的は、この finite readiness を actual test functions と exact discrepancy definition から自動生成し、051 の Green-facing PNT -> eighth-margin theorem から `hReady` を消すこと。**

これは PNT でも asymptotic でもない。有限 exponential cell 上の measurable/bounded/integrable plumbing だけを閉じる。

本段では:

- PNT ratio 自体を証明しない;
- external PNT dependency を追加しない;
- left radial eighth-credit を証明しない;
- interior-strip provider を証明しない;
- SmoothAbel -> SmoothLogCell provider を証明しない;
- limit exchange / infinite prime sum / RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFiniteDiscrepancyAnalyticReadinessAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaFiniteDiscrepancyAnalyticReadinessAudit.lean
```

imports:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeCountingPNTToRelativeDiscrepancyAudit
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

---

## 2. Canonical notation

概念的に:

```text
U := cfzp039CarrierCellLeft W c n
R := cfzp039CarrierCellRight W c n

a := cfzp040CarrierCellExpLeft W c n  = exp U
b := cfzp040CarrierCellExpRight W c n = exp R

PC(x) := (Nat.primeCounting floor(x) : ℝ)
S(x)  := cfzp040PrimeCountingSmoothModel x = x / log x
E(x)  := cfzp040PrimeCountingDiscrepancy x = PC(x) - S(x)
```

Late assumption:

```text
1 <= U
```

then every `x ∈ Ioc a b` satisfies:

```text
1 < x
1 <= log x
0 < log x
0 < x
```

Reuse:

```text
cfzp050_cell_log_bounds
cfzp040CarrierCellExpLeft_pos
cfzp040CarrierCellExpLeft_lt_right
cfzp040_log_carrierCellExpLeft
cfzp040_log_carrierCellExpRight
```

Do not rebuild logarithmic geometry.

---

## 3. Gate A — measurability of the floor prime-counting term

Mathlib current APIs include `Nat.measurable_floor` / `Measurable.nat_floor` and `measurable_of_countable`.

Prove a first-class theorem:

```lean
theorem cfzp052_primeCountingFloor_measurable :
    Measurable (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) := by
  ...
```

Suggested route:

```text
x -> floor_Nat x          measurable
n -> (primeCounting n : ℝ) measurable because Nat is countable
composition               measurable
```

Use current exact API names. `measurability` is acceptable if it closes from the same facts.

Also prove:

```lean
theorem cfzp052_primeCountingSmoothModel_measurable :
    Measurable cfzp040PrimeCountingSmoothModel := by
  ...

theorem cfzp052_primeCountingDiscrepancy_measurable :
    Measurable cfzp040PrimeCountingDiscrepancy := by
  ...
```

The smooth model may be globally defined at `log x = 0`; measurability is enough here. Do not assert global continuity.

This Gate is Green-required because the discrepancy-product integrands must not remain opaque nonmeasurable providers.

---

## 4. Gate B — explicit carrier derivative formula on the finite cell

040 already proves:

```lean
cfzp040PrimeAxisCarrierTestFunction_hasDerivAt
```

with derivative

```text
exp(-sigma * log x) / x *
  (-sigma * LeadingCarrier(log x) + LeadingCarrierDerivative(log x)).
```

If useful define:

```lean
noncomputable def cfzp052CarrierDerivativeFormula
    (epsilon : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (x : ℝ) : ℝ :=
  Real.exp (-W.rectangle.σ * Real.log x) / x *
    (-W.rectangle.σ *
        cfzp036PrimeAxisLeadingPeriodicCarrier epsilon W (Real.log x) +
      cfzp040LeadingCarrierDerivative epsilon W (Real.log x))
```

Then for `hε : 0 < epsilon`, `hU : 1 <= U`, and `x ∈ Ioc a b` prove:

```lean
theorem cfzp052_carrier_deriv_eq_formula_on_cell
    ... :
    deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x =
      cfzp052CarrierDerivativeFormula epsilon W x := by
  ...
```

via `.deriv` from the existing HasDerivAt theorem.

Prove the formula is measurable / continuous on the late cell. Recommended shape:

```lean
theorem cfzp052_carrierDerivativeFormula_continuousOn_cell
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W ...) (c : ℝ) (n : ℕ)
    (hU : 1 <= U) :
    ContinuousOn
      (cfzp052CarrierDerivativeFormula epsilon W)
      (Set.Icc a b) := by
  ...
```

`fun_prop` should be usable after the positivity/nonzero log/x facts are supplied.

Do not re-prove the trigonometric derivative.

---

## 5. Gate C — explicit remainder derivative formula on the finite cell

Reuse the existing named function:

```text
cfzp048PrimeAxisRemainderTestDerivative W x
```

and exact theorem:

```text
cfzp048PrimeAxisRemainderTestFunction_hasDerivAt
```

For `1 <= U`, `x ∈ Ioc a b` prove:

```lean
theorem cfzp052_remainder_deriv_eq_formula_on_cell
    ... :
    deriv (cfzp048PrimeAxisRemainderTestFunction W) x =
      cfzp048PrimeAxisRemainderTestDerivative W x := by
  ...
```

and:

```lean
theorem cfzp052_remainderDerivativeFormula_continuousOn_cell
    (W ...) (c : ℝ) (n : ℕ)
    (hU : 1 <= U) :
    ContinuousOn
      (cfzp048PrimeAxisRemainderTestDerivative W)
      (Set.Icc a b) := by
  ...
```

Again finite positivity of `x` and `log x` is all that is needed.

---

## 6. Gate D — automatic absolute-derivative integrability

050 already proved pointwise finite envelopes:

```text
cfzp050CarrierTestFunction_deriv_abs_le_on_cell
cfzp050RemainderTestFunction_deriv_abs_le_on_cell
```

Use Gates B-C to obtain measurable / a.e.-strongly-measurable derivative functions on the cell, then close the two absolute derivative readiness terms.

Green-required:

```lean
theorem cfzp052CarrierDerivativeAbs_integrableOn
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W ...) (c : ℝ) (n : ℕ)
    (hU : 1 <= U) :
    IntegrableOn
      (fun x => |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|)
      (Set.Ioc a b) := by
  ...
```

and:

```lean
theorem cfzp052RemainderDerivativeAbs_integrableOn
    (W ...) (c : ℝ) (n : ℕ)
    (hU : 1 <= U) :
    IntegrableOn
      (fun x => |deriv (cfzp048PrimeAxisRemainderTestFunction W) x|)
      (Set.Ioc a b) := by
  ...
```

Preferred proof route:

```text
finite volume of Ioc(a,b)
+ AEStronglyMeasurable / measurableOn integrand
+ finite pointwise constant bound from 050
=> IntegrableOn.of_bound
```

Equivalent compact-continuity route is fine.

Do not keep any new integrability hypothesis in these theorems.

---

## 7. Gate E — a crude distribution-free discrepancy bound on one cell

To prove integrability of `deriv * discrepancy`, no PNT smallness is needed. Only a finite bound is required.

Define a deliberately coarse nonnegative bound. Recommended:

```lean
noncomputable def cfzp052FiniteCellDiscrepancyAbsBound
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  (cfzp040CarrierCellNaturalRight W c n : ℝ) + 1 +
    cfzp040CarrierCellExpRight W c n
```

Equivalent larger finite expression is fine.

Prove:

```lean
theorem cfzp052FiniteCellDiscrepancyAbsBound_nonneg ... :
  0 <= cfzp052FiniteCellDiscrepancyAbsBound W c n := by
  ...
```

and Green-required:

```lean
theorem cfzp052_primeCountingDiscrepancy_abs_le_on_cell
    (W ...) (c : ℝ) (n : ℕ)
    (hU : 1 <= U)
    {x : ℝ} (hx : x ∈ Set.Ioc a b) :
    |cfzp040PrimeCountingDiscrepancy x| <=
      cfzp052FiniteCellDiscrepancyAbsBound W c n := by
  ...
```

Suggested elementary estimates:

```text
primeCounting floor(x) <= floor(x) + 1
floor(x) <= floor(b) = NaturalRight

0 <= S(x) = x/log x
S(x) <= x <= b

|PC(x) - S(x)| <= PC(x) + S(x)
```

For the counting bound, use `Nat.primeCounting = Nat.count Prime (n+1)` plus `Nat.count_le` if no direct theorem is convenient.

This Gate must remain completely distribution-free.

---

## 8. Gate F — automatic discrepancy-product integrability

Now combine:

```text
derivative formula measurable on cell
E(x) measurable
|derivative| <= finite D
|E(x)| <= finite B
```

so:

```text
|derivative * E(x)| <= D * B
```

on a finite-measure cell.

Green-required carrier theorem:

```lean
theorem cfzp052CarrierDerivativeMulDiscrepancy_integrableOn
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W ...) (c : ℝ) (n : ℕ)
    (hU : 1 <= U) :
    IntegrableOn
      (fun x => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
        cfzp040PrimeCountingDiscrepancy x)
      (Set.Ioc a b) := by
  ...
```

Green-required remainder theorem:

```lean
theorem cfzp052RemainderDerivativeMulDiscrepancy_integrableOn
    (W ...) (c : ℝ) (n : ℕ)
    (hU : 1 <= U) :
    IntegrableOn
      (fun x => deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
        cfzp040PrimeCountingDiscrepancy x)
      (Set.Ioc a b) := by
  ...
```

Again `IntegrableOn.of_bound` is preferred if the measurable product is easy to expose.

Do not use the PNT relative bound to prove integrability. The result must be finite and unconditional.

---

## 9. Gate G — realize the full CFZP-051 readiness predicate

Close:

```lean
theorem cfzp052FiniteDiscrepancyAnalyticReadyAt_of_late
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n) :
    Cfzp051FiniteDiscrepancyAnalyticReadyAt epsilon W c n := by
  refine ⟨
    cfzp052CarrierDerivativeAbs_integrableOn hε W c n hU,
    cfzp052CarrierDerivativeMulDiscrepancy_integrableOn hε W c n hU,
    cfzp052RemainderDerivativeAbs_integrableOn W c n hU,
    cfzp052RemainderDerivativeMulDiscrepancy_integrableOn W c n hU
  ⟩
```

Equivalent theorem names/order matching the actual predicate are fine.

This is the primary Green criterion.

---

## 10. Gate H — eventual readiness from cell cofinality

Using

```text
cfzp047CarrierCellLeft_tendsto_atTop
```

close:

```lean
theorem cfzp052_eventually_finiteDiscrepancyAnalyticReady
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp051FiniteDiscrepancyAnalyticReadyAt epsilon W c n := by
  ...
```

The only threshold needed should be `1 <= U`.

---

## 11. Gate I — remove `hReady` from the PNT -> eighth-margin theorem

Green-facing theorem:

```lean
theorem cfzp052_pntRatio_eventually_combinedDebt_le_eighthMargin_autoReady
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    ∀ᶠ n : ℕ in Filter.atTop,
      cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n <=
        cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  exact cfzp051_pntRatio_eventually_combinedDebt_le_eighthMargin
    hε W c hM hPNT
    (cfzp052_eventually_finiteDiscrepancyAnalyticReady hε W c)
```

No finite analytic readiness hypothesis may remain in this wrapper.

---

## 12. Gate J — synchronize with a left eighth-credit provider

Do not prove left radial credit in this checkpoint. But expose the exact next frontier.

If:

```lean
hLeft : ∀ᶠ n : ℕ in Filter.atTop,
  Cfzp051LeftRadialEighthCreditBudgetAt epsilon eta W c n
```

then under `hPNT` prove eventually:

```lean
theorem cfzp052_pntRatio_and_leftEighthCredit_eventually_remainingQuarter
    {epsilon eta : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    (hLeft : ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp051LeftRadialEighthCreditBudgetAt epsilon eta W c n) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp049CombinedRemainingQuarterBudgetAt epsilon eta W c n := by
  ...
```

Use only:

```text
cfzp052_pntRatio_eventually_combinedDebt_le_eighthMargin_autoReady
cfzp051_eighthDiscrepancy_and_leftEighthCredit_implies_combinedBudget
```

This theorem should make the next unresolved object visually unique: the left eighth-credit provider.

---

## 13. GAP / firewall

Introduce e.g.

```lean
inductive Cfzp052FiniteDiscrepancyAnalyticReadinessGap : Prop
  | noPrimeCountingPNTRatioProvider
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticLeadingSmoothAbelLogCellReadinessProvider
  | noAutomaticLeftRadialEighthCreditBudgetProvider
  | noCofinalFinalRadialBudgetProvider
```

The old 051 constructor

```text
noAutomaticFiniteDiscrepancyAnalyticReadinessProvider
```

must be RETIRED if Gates G-I close.

Do not add a replacement measurability/integrability provider gap. The entire point of 052 is to close that finite plumbing internally.

---

## 14. Roadmap update

Add CFZP-052 with at least:

```text
primeCounting(floor x) measurability: CLOSED
prime-counting discrepancy measurability: CLOSED
carrier derivative exact formula on late cell: CLOSED
remainder derivative exact formula on late cell: CLOSED
carrier absolute derivative finite-cell integrability: CLOSED
remainder absolute derivative finite-cell integrability: CLOSED
distribution-free finite cell discrepancy absolute bound: CLOSED
carrier derivative * discrepancy integrability: CLOSED
remainder derivative * discrepancy integrability: CLOSED
Cfzp051FiniteDiscrepancyAnalyticReadyAt from 1 <= U: CLOSED
eventual finite analytic readiness: CLOSED
PNT provider -> eventual combined debt <= margin / 8 without hReady: CLOSED
PNT + left eighth-credit provider -> eventual remaining-quarter budget: CLOSED
finite discrepancy analytic readiness GAP: RETIRED
standard PNT ratio theorem itself: OPEN / arithmetic provider
left radial eighth-credit provider: OPEN / next structural frontier
automatic interior-strip / SmoothAbel -> SmoothLogCell providers: OPEN / GAP
CFZP-018 / global RH: OUT OF SCOPE
```

---

## 15. Green criterion

CFZP-052 is Green only if the theorem-level chain is actual:

```text
Nat.floor measurable
Nat -> primeCounting -> Real measurable
--------------------------------------
PC(x) measurable
S(x) measurable
E(x) measurable

actual carrier/remainder derivative formulas on late cell
+ 050 pointwise derivative bounds
+ finite Ioc volume
--------------------------------------
|carrier derivative| IntegrableOn
|remainder derivative| IntegrableOn

finite distribution-free |E(x)| <= B_cell
+ measurable products
+ finite derivative bounds
--------------------------------------
carrier derivative * E IntegrableOn
remainder derivative * E IntegrableOn

1 <= U
--------------------------------------
Cfzp051FiniteDiscrepancyAnalyticReadyAt

U_n -> +infinity
--------------------------------------
eventually readiness

PNT ratio provider
+ eventually readiness generated internally
--------------------------------------
eventually CombinedDebt <= Margin/8
```

There must be **no caller-supplied `Cfzp051FiniteDiscrepancyAnalyticReadyAt` or four `IntegrableOn` hypotheses** in the final Green-facing PNT/eighth-margin theorem.

After CFZP-052, do not begin CFZP-053 until review. The likely next target is the now-isolated `Cfzp051LeftRadialEighthCreditBudgetAt`, but its exact attack route must be chosen from the current radial recurrence/API rather than guessed in advance.
