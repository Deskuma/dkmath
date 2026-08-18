# CFZP-0080 / CFZP-050 correction

## realize the finite cell sensitivity envelope — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

対象 module:

`DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisCombinedDiscrepancySensitivityEnvelopeAudit`

file:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisCombinedDiscrepancySensitivityEnvelopeAudit.lean`

---

## 0. 判定

CFZP-050 は **まだ Green ではない**。

現在実装は coefficient algebra と cancellation 自体は正しいが、Green criterion で要求した

```text
CarrierSensitivity(U,R) <= C_car * exp(-sigma U)
RemainderSensitivity(U,R) <= C_rem * exp(-sigma U)
```

を actual carrier/remainder test function から証明せず、

```lean
Cfzp050CellSensitivityEnvelope ...
```

を caller-supplied hypothesis として要求している。

したがって現在の theorem

```lean
cfzp050CarrierDiscrepancyCellSensitivity_le
cfzp050RemainderDiscrepancyCellSensitivity_le
cfzp050CombinedPrimeCountingDiscrepancySensitivity_le
cfzp050CombinedDebt_le_explicitRelativeEnvelope
```

は、050 の本来の analytic burden を certificate provider に移した形であり、まだ closure ではない。

**CFZP-051 へ進まず、CFZP-050 のままこの certificate を actual finite-cell estimates から生成すること。**

`Cfzp050CellSensitivityEnvelope` 自体は helper structure として残してよい。問題は、それを外部仮定のままにしないこと。

---

## 1. 既存 Green 部分は保持

以下はそのまま保持する。

```text
cfzp050LeadingCarrierAbsConstant
cfzp050LeadingCarrierDerivativeAbsConstant
cfzp050LeadingPeriodicCarrier_abs_le
cfzp050LeadingCarrierDerivative_abs_le

cfzp050CarrierSensitivityConstant
cfzp050RemainderSensitivityConstant
cfzp050CombinedSensitivityConstant

cfzp050RelativeCombinedDiscrepancyExplicitEnvelope
Cfzp050RelativeDiscrepancyMarginShareCondition
Cfzp050RelativeDiscrepancyQuarterMarginCondition
Cfzp050RelativeDiscrepancyEighthMarginCondition
Cfzp050LeftRadialDeficitBudgetAt
```

また coefficient cancellation

```text
exp(R) * exp(-sigma U)
= exp(P) * exp((1-sigma)U)
```

および margin-share algebra は Green。

今回の修正対象は **cell sensitivity certificate の realization** のみ。

---

## 2. Canonical notation

概念的に

```text
U := cfzp039CarrierCellLeft W c n
R := cfzp039CarrierCellRight W c n
P := cfzp036PrimeAxisCarrierPeriod W
sigma := W.rectangle.σ

a := cfzp040CarrierCellExpLeft W c n  = exp U
b := cfzp040CarrierCellExpRight W c n = exp R
```

既存:

```text
cfzp040CarrierCellExpLeft_pos
cfzp040CarrierCellExpLeft_lt_right
cfzp040_log_carrierCellExpLeft
cfzp040_log_carrierCellExpRight
cfzp046CarrierCellRight_eq_left_add_period
cfzp034_rectangleSigma_gt_half
```

を再利用する。

`hU : 1 <= U` から

```text
0 < U
1 < exp U
0 < sigma
0 < a
0 < b
```

を必要に応じて得る。

---

## 3. Gate A — carrier endpoint bounds を actual theorem 化

`f_car(x)` は

```text
exp(-sigma * log x) * L(log x)
```

であり、既に

```text
|L(u)| <= C0
```

は閉じている。

### A1. left endpoint

Green-required:

```lean
theorem cfzp050CarrierTestFunction_expLeft_abs_le
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    |cfzp040PrimeAxisCarrierTestFunction epsilon W
        (cfzp040CarrierCellExpLeft W c n)| <=
      cfzp050LeadingCarrierAbsConstant epsilon W *
        Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) := by
  ...
```

Use `log(exp U)=U` and `cfzp050LeadingPeriodicCarrier_abs_le`.

### A2. right endpoint lowered to left weight

For `hU : 1 <= U` (or weaker if convenient):

```lean
theorem cfzp050CarrierTestFunction_expRight_abs_le_leftWeight
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    |cfzp040PrimeAxisCarrierTestFunction epsilon W
        (cfzp040CarrierCellExpRight W c n)| <=
      cfzp050LeadingCarrierAbsConstant epsilon W *
        Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) := by
  ...
```

Proof:

```text
|f_car(exp R)|
<= C0 * exp(-sigma R)
<= C0 * exp(-sigma U)
```

using `0 < sigma` and `U <= R`.

No phase occupancy theorem is involved.

---

## 4. Gate B — carrier derivative pointwise bound on the x-cell

040 already gives exact derivative:

```text
f_car'(x)
= exp(-sigma log x) / x *
    (-sigma * L(log x) + L'(log x)).
```

For

```text
x in Ioc(exp U, exp R)
1 <= U
```

prove:

```text
exp(-sigma log x) <= exp(-sigma U)
1/x <= exp(-U)
|-sigma L(log x) + L'(log x)| <= sigma*C0 + C1
```

where

```text
C0 = cfzp050LeadingCarrierAbsConstant epsilon W
C1 = cfzp050LeadingCarrierDerivativeAbsConstant epsilon W.
```

Green-required theorem:

```lean
theorem cfzp050CarrierTestFunction_deriv_abs_le_on_cell
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)) :
    |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x| <=
      Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) *
        Real.exp (-cfzp039CarrierCellLeft W c n) *
        (W.rectangle.σ * cfzp050LeadingCarrierAbsConstant epsilon W +
          cfzp050LeadingCarrierDerivativeAbsConstant epsilon W) := by
  ...
```

Use

```text
cfzp040PrimeAxisCarrierTestFunction_hasDerivAt
cfzp050LeadingPeriodicCarrier_abs_le
cfzp050LeadingCarrierDerivative_abs_le
cfzp050_cell_log_bounds
```

and `.deriv` to rewrite `deriv`.

Do not re-derive the derivative formula.

---

## 5. Gate C — carrier derivative integral bound

The old 050 instruction explicitly allowed a finite derivative-absolute integrability premise if Mathlib plumbing is disproportionate.

Therefore it is acceptable to take only

```lean
hDerivAbsInt : IntegrableOn
  (fun x => |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|)
  (Set.Ioc a b)
```

and prove the numeric bound internally.

Define conceptually

```text
D_car
:= exp(-sigma U) * exp(-U) * (sigma*C0 + C1).
```

From Gate B and finite interval monotonicity:

```text
Integral_Ioc |f_car'|
<= D_car * (exp R - exp U)
<= D_car * exp R
= exp(-sigma U) * exp(P) * (sigma*C0 + C1).
```

Use

```text
R = U + P
exp(R) * exp(-U) = exp(P).
```

Green-required theorem:

```lean
theorem cfzp050CarrierDerivativeIntegral_le
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    (hDerivAbsInt : IntegrableOn
      (fun x => |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))) :
    (∫ x in Set.Ioc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n),
      |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|) <=
      Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) *
        Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
        (W.rectangle.σ * cfzp050LeadingCarrierAbsConstant epsilon W +
          cfzp050LeadingCarrierDerivativeAbsConstant epsilon W) := by
  ...
```

Current Mathlib provides finite interval tools such as:

```text
intervalIntegrable_const
intervalIntegrable_iff_integrableOn_Ioc_of_le
intervalIntegral.integral_of_le
intervalIntegral.integral_const
setIntegral_mono_on
```

Use whichever current signature is simplest. Do not introduce a new analytic provider merely to integrate a constant.

---

## 6. Gate D — construct the carrier certificate internally

Now prove:

```lean
theorem cfzp050CarrierCellSensitivityEnvelope_of_late
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    (hDerivAbsInt : IntegrableOn
      (fun x => |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))) :
    Cfzp050CellSensitivityEnvelope
      (cfzp040PrimeAxisCarrierTestFunction epsilon W)
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)
      (cfzp039CarrierCellLeft W c n)
      W.rectangle.σ
      (cfzp050CarrierSensitivityConstant epsilon W) := by
  ...
```

Recall

```text
C_car = 2*C0 + exp(P)*(sigma*C0 + C1).
```

Endpoint sum is at most

```text
2*C0*exp(-sigma U)
```

and derivative integral is at most

```text
exp(P)*(sigma*C0+C1)*exp(-sigma U).
```

These exactly add to `C_car * exp(-sigma U)`.

This theorem is the carrier-side closure missing from the current implementation.

---

## 7. Gate E — remainder endpoint bounds

For

```text
f_rem(x) = exp(-sigma log x) / log x
```

and `1 <= U`, prove actual endpoint theorems:

```lean
theorem cfzp050RemainderTestFunction_expLeft_abs_le
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n) :
    |cfzp048PrimeAxisRemainderTestFunction W
        (cfzp040CarrierCellExpLeft W c n)| <=
      Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) := by
  ...
```

and

```lean
theorem cfzp050RemainderTestFunction_expRight_abs_le_leftWeight
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n) :
    |cfzp048PrimeAxisRemainderTestFunction W
        (cfzp040CarrierCellExpRight W c n)| <=
      Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) := by
  ...
```

Use

```text
1/log x <= 1
exp(-sigma R) <= exp(-sigma U).
```

---

## 8. Gate F — remainder derivative pointwise and integral bounds

048 exact derivative:

```text
f_rem'(x)
= -(exp(-sigma log x)/x) *
    (sigma/log x + 1/(log x)^2).
```

For `1 <= U <= log x`, use

```text
1/log x <= 1
1/(log x)^2 <= 1
```

and prove:

```lean
theorem cfzp050RemainderTestFunction_deriv_abs_le_on_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)) :
    |deriv (cfzp048PrimeAxisRemainderTestFunction W) x| <=
      Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) *
        Real.exp (-cfzp039CarrierCellLeft W c n) *
        (W.rectangle.σ + 1) := by
  ...
```

Use

```text
cfzp048PrimeAxisRemainderTestFunction_hasDerivAt
```

because `hU >= 1` gives every x in the cell `x > 1`.

Then, with only derivative-absolute integrability if needed, prove:

```lean
theorem cfzp050RemainderDerivativeIntegral_le
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    (hDerivAbsInt : IntegrableOn
      (fun x => |deriv (cfzp048PrimeAxisRemainderTestFunction W) x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))) :
    (∫ x in Set.Ioc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n),
      |deriv (cfzp048PrimeAxisRemainderTestFunction W) x|) <=
      Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) *
        Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
        (W.rectangle.σ + 1) := by
  ...
```

---

## 9. Gate G — construct the remainder certificate internally

Prove:

```lean
theorem cfzp050RemainderCellSensitivityEnvelope_of_late
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    (hDerivAbsInt : IntegrableOn
      (fun x => |deriv (cfzp048PrimeAxisRemainderTestFunction W) x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))) :
    Cfzp050CellSensitivityEnvelope
      (cfzp048PrimeAxisRemainderTestFunction W)
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)
      (cfzp039CarrierCellLeft W c n)
      W.rectangle.σ
      (cfzp050RemainderSensitivityConstant W) := by
  ...
```

Recall

```text
C_rem = 2 + exp(P)*(sigma+1).
```

Again the endpoint + derivative integral budget exactly matches this coefficient.

---

## 10. Gate H — remove hEnvelope from the sensitivity API

The current theorem signatures must no longer require caller-supplied

```text
hCarrier : Cfzp050CellSensitivityEnvelope ...
hRemainder : Cfzp050CellSensitivityEnvelope ...
```

Replace/add Green-facing theorems of shape:

```lean
theorem cfzp050CarrierDiscrepancyCellSensitivity_le_auto
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    (hDerivAbsInt : IntegrableOn ...) :
    cfzp049CarrierDiscrepancyCellSensitivity epsilon W c n <=
      cfzp050CarrierSensitivityConstant epsilon W *
        Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) := by
  ...
```

```lean
theorem cfzp050RemainderDiscrepancyCellSensitivity_le_auto
    ...
    (hU : 1 <= U)
    (hDerivAbsInt : IntegrableOn ...) :
    cfzp049RemainderDiscrepancyCellSensitivity W c n <=
      cfzp050RemainderSensitivityConstant W * Real.exp (-sigma*U) := by
  ...
```

and crucially:

```lean
theorem cfzp050CombinedPrimeCountingDiscrepancySensitivity_le_auto
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= U)
    (hCarrierDerivAbsInt : IntegrableOn ...)
    (hRemainderDerivAbsInt : IntegrableOn ...) :
    cfzp049CombinedPrimeCountingDiscrepancySensitivity epsilon W c n <=
      cfzp050CombinedSensitivityConstant epsilon W *
        Real.exp (-sigma*U) := by
  ...
```

Existing certificate-consuming lemmas may remain as internal adapters, but public closure theorem must not require `Cfzp050CellSensitivityEnvelope` from the caller.

---

## 11. Gate I — repair the explicit relative-debt theorem

Add a Green-facing theorem that invokes Gate H automatically.

It may retain the finite integrability hypotheses already demanded by CFZP-049, especially the two derivative-times-discrepancy integrability premises.

Suggested shape:

```lean
theorem cfzp050CombinedDebt_le_explicitRelativeEnvelope_auto
    {epsilon delta : ℝ} (hε : 0 < epsilon) (hδ : 0 <= delta)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 <= U)
    (hRel : Cfzp049PrimeCountingRelativeDiscrepancyBoundAt W c n delta)
    (hCarrierDerivAbsInt : IntegrableOn ...)
    (hCarrierDerivDiscInt : IntegrableOn ...)
    (hRemainderDerivAbsInt : IntegrableOn ...)
    (hRemainderDerivDiscInt : IntegrableOn ...) :
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n <=
      cfzp050RelativeCombinedDiscrepancyExplicitEnvelope
        epsilon delta W c n := by
  ...
```

No `hCarrier : Cfzp050CellSensitivityEnvelope` and no `hRemainder : ...` may remain in this Green-facing route.

Then the existing margin-share / quarter algebra can be reused unchanged.

Optional but useful direct corollary:

```text
relative discrepancy + finite integrability + quarter coefficient
=> CombinedDebt <= Margin/4.
```

---

## 12. Roadmap / docstring correction

Current roadmap text

```text
automatic finite-cell endpoint/derivative certificate generation: OPEN / GAP
```

must become something equivalent to

```text
actual carrier endpoint and derivative cell bounds: CLOSED
actual remainder endpoint and derivative cell bounds: CLOSED
carrier/remainder derivative integral finite envelope: CLOSED
Cfzp050CellSensitivityEnvelope generated from actual cell estimates: CLOSED
combined sensitivity <= C_sens * exp(-sigma U): CLOSED without envelope-provider hypothesis
relative combined debt explicit envelope: CLOSED without envelope-provider hypothesis
```

It is acceptable for the technical hypotheses

```text
IntegrableOn |deriv f|
IntegrableOn (deriv f * discrepancy)
```

to remain explicit if needed by current finite Abel plumbing. These are not asymptotic magnitude providers.

Do not add a GAP constructor for cell sensitivity certificate generation after this correction.

---

## 13. Firewall remains

Keep open:

```text
noAutomaticInteriorStripWindowProvider
noAutomaticLeadingSmoothAbelLogCellReadinessProvider
noRelativePrimeCountingDiscrepancyDecayProvider
noAutomaticLeftRadialDeficitBudgetProvider
noCofinalReducedRemainingQuarterBudgetProvider
```

Still forbidden in CFZP-050 correction:

- PNT / asymptotic prime-counting decay;
- Mertens / Dirichlet / Bertrand / equidistribution;
- infinite prime sums or summability;
- limit exchange;
- automatic interior strip;
- automatic left radial deficit;
- CFZP-018 provider;
- global RH.

---

## 14. Corrected Green criterion

CFZP-050 becomes Green only after the theorem-level chain is internal:

```text
|L(u)| <= C0
|L'(u)| <= C1

actual carrier endpoint bounds
actual carrier derivative pointwise bound
actual carrier derivative integral bound
=> CarrierSensitivity(U,R) <= C_car * exp(-sigma U)

actual remainder endpoint bounds
actual remainder derivative pointwise bound
actual remainder derivative integral bound
=> RemainderSensitivity(U,R) <= C_rem * exp(-sigma U)

=> CombinedSensitivity(U,R) <= C_sens * exp(-sigma U)
```

with no caller-supplied `Cfzp050CellSensitivityEnvelope` in the Green-facing theorem.

Then retain the already-correct algebra:

```text
CombinedDebt
<= delta * exp(R)/U * CombinedSensitivity
<= delta * exp(P) * C_sens * exp((1-sigma)U)/U
```

and

```text
4 * delta * exp(P) * C_sens <= theta * M(c)
=> CombinedDebt <= theta * Margin.
```

Quarter:

```text
16 * delta * exp(P) * C_sens <= M(c)
=> CombinedDebt <= Margin/4.
```

Only after this corrected criterion is satisfied may CFZP-051 begin the relative prime-counting discrepancy provider audit.
