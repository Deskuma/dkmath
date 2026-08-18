# CFZP-0079 / CFZP-050

## combined discrepancy sensitivity explicit cell envelope — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-036: sigma-stripped prime-axis leading periodic carrier + exact derivative-ready sine/cosine normal form
- CFZP-040: x-axis carrier test function and exact derivative
- CFZP-048: remainder test function and exact derivative; structural smooth remainder `<= Margin/4`
- CFZP-049: carrier + remainder discrepancy functionals unified under one pointwise discrepancy and one combined sensitivity

CFZP-049 は Green-A。

**CFZP-050 の目的は、CFZP-049 で残った `combined sensitivity` 自体を一周期 cell 上の explicit finite constant で支配し、relative prime-counting discrepancy envelope と explicit smooth margin の比較から `U` と `sigma` の成長因子を exact に相殺すること。**

CFZP-049 の現在形は概念的に

```text
CombinedDebt
  <= delta * exp(R) / U * CombinedSensitivity(U,R).
```

本段で

```text
CombinedSensitivity(U,R)
  <= C_sens(epsilon,W) * exp(-sigma U)
```

を閉じれば、`R = U + P` より

```text
CombinedDebt
  <= delta * exp(P) * C_sens(epsilon,W)
       * exp((1-sigma)U) / U.
```

一方、CFZP-044 explicit smooth margin は

```text
Margin
  = exp((1-sigma)U) * M(c) / (4U).
```

したがって比較は完全に cell coordinate から独立な係数条件

```text
4 * delta * exp(P) * C_sens <= theta * M(c)
```

へ落ちる。この条件なら

```text
CombinedDebt <= theta * Margin.
```

特に `theta = 1/4` なら

```text
16 * delta * exp(P) * C_sens <= M(c)
```

から

```text
CombinedDebt <= Margin / 4.
```

**ここが CFZP-050 の魔核。relative discrepancy と smooth margin は同じ `exp((1-sigma)U)/U` スケールを持ち、最後に残る勝負は `delta` と有限係数だけになる。**

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、relative prime-counting error の eventual decay、infinite prime sums、summability、limit exchange、CFZP-018 provider、global RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisCombinedDiscrepancySensitivityEnvelopeAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisCombinedDiscrepancySensitivityEnvelopeAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisCombinedDiscrepancyEnvelopeAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に公開 import を追加する。

---

## 2. Canonical notation

以下を概念的に固定する。

```text
U := cfzp039CarrierCellLeft W c n
R := cfzp039CarrierCellRight W c n
P := cfzp036PrimeAxisCarrierPeriod W
sigma := W.rectangle.sigma
beta := cfzp039PrimeAxisGrowthExponent W = 1 - sigma
M := cfzp039ExponentialCarrierPeriodTransform epsilon W c
```

既存 exact theorem:

```text
cfzp046CarrierCellRight_eq_left_add_period:
  R = U + P
```

既存 positivity:

```text
cfzp036PrimeAxisCarrierPeriod_pos W
W.rectangle.hT
cfzpModePhaseAbscissa_pos W
```

また rectangle sigma は `1/2` より大きい既存 034 theorem から正である。current repository の exact theorem name を検索して使用すること。新しい仮定 `0 < sigma` を外から要求しない。

---

## 3. Gate A — finite carrier amplitude constants

CFZP-036 の exact normal form:

```text
L(u)
= (S * sin(Tu) + C * cos(Tu)) / epsilon
```

where

```text
S := cfzp036LeadingSinCoeffNumerator epsilon W
C := cfzp036LeadingCosCoeffNumerator epsilon W.
```

040 の coordinate derivative:

```text
L'(u)
= (T / epsilon) *
    (S * cos(Tu) - C * sin(Tu)).
```

これらに対する explicit constants を first-class にする。

推奨:

```lean
noncomputable def cfzp050LeadingCarrierAbsConstant
    (epsilon : Real) (W : PascalCenteredXiResidueTransportWindow) : Real :=
  (abs (cfzp036LeadingSinCoeffNumerator epsilon W) +
    abs (cfzp036LeadingCosCoeffNumerator epsilon W)) / epsilon

noncomputable def cfzp050LeadingCarrierDerivativeAbsConstant
    (epsilon : Real) (W : PascalCenteredXiResidueTransportWindow) : Real :=
  W.rectangle.T *
    (abs (cfzp036LeadingSinCoeffNumerator epsilon W) +
      abs (cfzp036LeadingCosCoeffNumerator epsilon W)) / epsilon
```

Equivalent positive reassociation is fine.

For `hε : 0 < ε`, prove:

```lean
cfzp050LeadingCarrierAbsConstant_nonneg
cfzp050LeadingCarrierDerivativeAbsConstant_nonneg
```

and Green-required uniform bounds:

```lean
theorem cfzp050LeadingPeriodicCarrier_abs_le
    {epsilon u : Real} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow) :
    abs (cfzp036PrimeAxisLeadingPeriodicCarrier epsilon W u) <=
      cfzp050LeadingCarrierAbsConstant epsilon W := by
  ...

theorem cfzp050LeadingCarrierDerivative_abs_le
    {epsilon u : Real} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow) :
    abs (cfzp040LeadingCarrierDerivative epsilon W u) <=
      cfzp050LeadingCarrierDerivativeAbsConstant epsilon W := by
  ...
```

Use only:

```text
cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair
abs(sin) <= 1
abs(cos) <= 1
triangle inequality
W.rectangle.hT
hε
```

No phase-arc occupancy argument is needed.

---

## 4. Gate B — common finite-cell geometry helpers

For a late cell with

```text
1 <= U
```

and

```text
x in Icc(exp U, exp R),
```

close reusable helpers:

```text
0 < x
U <= log x
log x <= R
0 < log x
1 <= log x
```

Also derive sigma-weight monotonicity:

```text
exp(-sigma * log x) <= exp(-sigma * U)
```

using `0 < sigma` from the existing rectangle geometry.

For the deliberately coarse but Lean-friendly derivative integral envelope, also prove:

```text
1 / x <= exp(-U)
exp(R) * exp(-U) = exp(P)
```

and a cell-length estimate sufficient for

```text
(exp R - exp U) * exp(-U) <= exp(P).
```

You may instead use the exact integral

```text
integral_{exp U}^{exp R} 1/x dx = P
```

if it is easier with current Mathlib. **Do not make the proof harder for a sharper constant.** The coarse `exp(P)` bound is fully sufficient for this checkpoint.

Recommended helper shape:

```lean
theorem cfzp050_cell_inv_x_integral_scale_le_exp_period
    (W ...) (c : Real) (n : Nat)
    (hU : 1 <= U) :
    ... <= Real.exp P := by
  ...
```

Exact internal representation may follow whichever integral API is easiest.

---

## 5. Gate C — carrier test function sensitivity envelope

Recall 040 exact derivative:

```text
f_car(x) = exp(-sigma log x) * L(log x)

f_car'(x)
= exp(-sigma log x) / x *
    (-sigma * L(log x) + L'(log x)).
```

Define a finite carrier sensitivity constant. Recommended coarse version:

```lean
noncomputable def cfzp050CarrierSensitivityConstant
    (epsilon : Real) (W : PascalCenteredXiResidueTransportWindow) : Real :=
  2 * cfzp050LeadingCarrierAbsConstant epsilon W +
    Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      (W.rectangle.sigma * cfzp050LeadingCarrierAbsConstant epsilon W +
        cfzp050LeadingCarrierDerivativeAbsConstant epsilon W)
```

Prove nonnegative under `hε`.

Then prove pointwise endpoint bounds:

```text
|f_car(exp U)| <= C0 * exp(-sigma U)
|f_car(exp R)| <= C0 * exp(-sigma U)
```

and derivative bound on the x-cell:

```text
|deriv f_car x|
<= exp(-sigma U) * exp(-U) *
     (sigma*C0 + C1).
```

Use `cfzp040PrimeAxisCarrierTestFunction_hasDerivAt` to rewrite `deriv`; do not unfold `deriv` abstractly if the existing theorem already supplies it.

Then integrate over the finite cell and close:

```lean
theorem cfzp050CarrierDiscrepancyCellSensitivity_le
    {epsilon : Real} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    (... minimal derivative-absolute integrability if genuinely required ...) :
    cfzp049CarrierDiscrepancyCellSensitivity epsilon W c n <=
      cfzp050CarrierSensitivityConstant epsilon W *
        Real.exp (-(W.rectangle.sigma) *
          cfzp039CarrierCellLeft W c n) := by
  ...
```

This is Green-required.

Prefer to prove the simple finite derivative-absolute integrability automatically from continuity on the positive compact cell if convenient. If Mathlib plumbing is disproportionately large, keeping the same finite integrability premise already used by CFZP-049 is acceptable; do not create a new abstract asymptotic provider.

---

## 6. Gate D — remainder test sensitivity envelope

Recall 048:

```text
f_rem(x) = exp(-sigma log x) / log x

f_rem'(x)
= -(exp(-sigma log x)/x) *
    (sigma/log x + 1/(log x)^2).
```

For `1 <= U <= log x`, use the intentionally coarse estimates

```text
1/log x <= 1
1/(log x)^2 <= 1.
```

Define:

```lean
noncomputable def cfzp050RemainderSensitivityConstant
    (W : PascalCenteredXiResidueTransportWindow) : Real :=
  2 + Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
    (W.rectangle.sigma + 1)
```

Prove it is nonnegative from rectangle sigma positivity.

Endpoint bounds:

```text
|f_rem(exp U)| <= exp(-sigma U)
|f_rem(exp R)| <= exp(-sigma U)
```

Derivative cell bound:

```text
|deriv f_rem x|
<= exp(-sigma U) * exp(-U) * (sigma + 1).
```

Use the existing exact derivative certificate

```text
cfzp048PrimeAxisRemainderTestFunction_hasDerivAt
```

on `x > 1`.

Then Green-required:

```lean
theorem cfzp050RemainderDiscrepancyCellSensitivity_le
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    (... finite derivative-absolute integrability if required ...) :
    cfzp049RemainderDiscrepancyCellSensitivity W c n <=
      cfzp050RemainderSensitivityConstant W *
        Real.exp (-(W.rectangle.sigma) *
          cfzp039CarrierCellLeft W c n) := by
  ...
```

A sharper `/U` remainder sensitivity is welcome but **not required**. The coarse same-scale `exp(-sigma U)` bound is enough to close the common envelope.

---

## 7. Gate E — combined sensitivity constant

Define:

```lean
noncomputable def cfzp050CombinedSensitivityConstant
    (epsilon : Real) (W : PascalCenteredXiResidueTransportWindow) : Real :=
  cfzp050CarrierSensitivityConstant epsilon W +
    cfzp036PrimeAxisRemainderConstant epsilon W *
      cfzp050RemainderSensitivityConstant W
```

Prove positive/nonnegative under `hε : 0 < ε`.

Using CFZP-049 exact definition

```text
CombinedSensitivity
= CarrierSensitivity + K_rem * RemainderSensitivity,
```

close the main sensitivity theorem:

```lean
theorem cfzp050CombinedPrimeCountingDiscrepancySensitivity_le
    {epsilon : Real} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    (... finite integrability inputs only if needed ...) :
    cfzp049CombinedPrimeCountingDiscrepancySensitivity epsilon W c n <=
      cfzp050CombinedSensitivityConstant epsilon W *
        Real.exp (-(W.rectangle.sigma) *
          cfzp039CarrierCellLeft W c n) := by
  ...
```

**This theorem retires `noCombinedSensitivityAsymptoticEnvelope` as a GAP.** It is not asymptotic; it is a uniform finite-cell bound.

---

## 8. Gate F — explicit relative discrepancy cell envelope

CFZP-049 already proved:

```text
CombinedDebt
<= (delta * exp(R) / U) * CombinedSensitivity.
```

Define the floor-free, sensitivity-free explicit envelope:

```lean
noncomputable def cfzp050RelativeCombinedDiscrepancyExplicitEnvelope
    (epsilon delta : Real)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat) : Real :=
  delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
    cfzp050CombinedSensitivityConstant epsilon W *
    (Real.exp (cfzp039PrimeAxisGrowthExponent W *
      cfzp039CarrierCellLeft W c n) /
      cfzp039CarrierCellLeft W c n)
```

Under `hδ : 0 <= δ`, `hU : 1 <= U`, a relative discrepancy provider, and the finite integrability premises used by 049, prove:

```lean
theorem cfzp050CombinedDebt_le_explicitRelativeEnvelope
    {epsilon delta : Real} (hε : 0 < epsilon) (hδ : 0 <= delta)
    (W ...) (c : Real) (n : Nat)
    (hU : 1 <= U)
    (hRel : Cfzp049PrimeCountingRelativeDiscrepancyBoundAt W c n delta)
    ... :
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n <=
      cfzp050RelativeCombinedDiscrepancyExplicitEnvelope
        epsilon delta W c n := by
  ...
```

Proof spine:

```text
CombinedDebt
<= delta * exp(R)/U * CombinedSensitivity
<= delta * exp(R)/U * C_sens * exp(-sigma U)
=  delta * exp(P) * C_sens * exp((1-sigma)U)/U.
```

Use exact

```text
R = U + P
beta = 1 - sigma
exp(a+b)=exp(a)exp(b)
```

No asymptotic theorem is required.

Also prove the explicit normal-form equality separately if helpful:

```lean
cfzp050RelativeCombinedDiscrepancyExplicitEnvelope_eq_normalForm
```

---

## 9. Gate G — general margin-share competition

Do not hardwire the final quarter too early. Define a reusable finite coefficient condition for a requested margin share `theta`:

```lean
def Cfzp050RelativeDiscrepancyMarginShareCondition
    (epsilon delta theta : Real)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) : Prop :=
  4 * delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      cfzp050CombinedSensitivityConstant epsilon W <=
    theta * cfzp039ExponentialCarrierPeriodTransform epsilon W c
```

Reason:

```text
theta * Margin
= theta * exp(beta U) * M / (4U).
```

Thus the coefficient condition is exactly sufficient for

```text
ExplicitRelativeEnvelope <= theta * Margin.
```

Green-required theorem:

```lean
theorem cfzp050RelativeEnvelope_le_marginShare
    {epsilon delta theta : Real}
    (hε : 0 < epsilon) (hδ : 0 <= delta) (hθ : 0 <= theta)
    (W ...) (c : Real) (n : Nat)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hU : 1 <= U)
    (hShare : Cfzp050RelativeDiscrepancyMarginShareCondition
      epsilon delta theta W c) :
    cfzp050RelativeCombinedDiscrepancyExplicitEnvelope epsilon delta W c n <=
      theta * cfzp044ExplicitSmoothMargin epsilon W c n := by
  ...
```

`hM` may not be algebraically necessary once `hShare` is supplied, but retaining it is fine if it simplifies positivity/division.

The crucial proof should be finite algebra after canceling the common positive factor

```text
exp(beta U) / U.
```

Do not prove this by asymptotic comparison.

---

## 10. Gate H — quarter-margin and eighth-margin corollaries

Provide the exact quarter specialization:

```lean
def Cfzp050RelativeDiscrepancyQuarterMarginCondition
    (epsilon delta : Real)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) : Prop :=
  16 * delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      cfzp050CombinedSensitivityConstant epsilon W <=
    cfzp039ExponentialCarrierPeriodTransform epsilon W c
```

Prove it is equivalent/sufficient to the general share with `theta=1/4`.

Then:

```lean
theorem cfzp050CombinedDebt_le_quarter_explicitSmoothMargin
    ...
    (hCondition : Cfzp050RelativeDiscrepancyQuarterMarginCondition
      epsilon delta W c) :
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n <=
      cfzp044ExplicitSmoothMargin epsilon W c n / 4 := by
  ...
```

Also strongly preferred, because it leaves real positive credit for the starting radial deficit:

```lean
def Cfzp050RelativeDiscrepancyEighthMarginCondition ... : Prop :=
  32 * delta * exp(P) * C_sens <= M
```

with theorem

```text
CombinedDebt <= Margin/8.
```

The eighth-margin theorem is not needed to prove the coefficient cancellation, but it is strategically useful for the next radial-budget phase.

---

## 11. Gate I — reduced remaining-quarter budget

Once combined discrepancy is at most `theta * Margin`, the corrected 049/048 budget becomes a statement only about the left radial deficit.

For the quarter specialization, define or prove a helper:

```lean
def Cfzp050LeftRadialDeficitBudgetAt
    (epsilon eta : Real)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
      (cfzp040CarrierCellNaturalLeft W c n) <= eta
```

Then:

```lean
theorem cfzp050_quarterDiscrepancy_and_leftDeficit_implies_combinedBudget
    ...
    (hDisc : CombinedDebt <= Margin/4)
    (hLeft : cfzp050LeftRadialDeficitBudgetAt epsilon eta W c n) :
    Cfzp049CombinedRemainingQuarterBudgetAt epsilon eta W c n := by
  ...
```

This is only an adapter. **Do not claim `hLeft` automatically holds.**

For the eighth-margin specialization, expose the stronger useful residual:

```text
CombinedDebt <= Margin/8
G_A <= Margin/8 + eta
--------------------------------
G_A + CombinedDebt <= Margin/4 + eta.
```

A theorem/predicate capturing this is strongly preferred because it leaves half of the last quarter as genuine carrier credit.

Then, if convenient, compose with

```text
cfzp049CombinedRemainingQuarterBudget_implies_radialContactDeficit_le
```

using all current analytic readiness / higher-power inputs. Do not duplicate the 048/049 radial proof.

---

## 12. What CFZP-050 must NOT claim

After this checkpoint, the following is **not** yet automatic:

```text
there exists an eventually small relative prime-counting discrepancy delta
```

CFZP-050 only proves:

```text
IF a relative cell discrepancy bound with delta is supplied,
THEN the complete carrier+remainder discrepancy debt is
an explicit coefficient times the same exp(beta U)/U scale as the smooth margin.
```

The arithmetic provider `delta -> 0` is a separate next checkpoint.

Likewise do not claim:

- automatic interior-strip window provider;
- automatic positive-transform phase if not already supplied by 039;
- automatic SmoothAbel -> SmoothLogCell readiness;
- automatic left-radial-deficit budget;
- CFZP-018 cofinal provider;
- global RH.

---

## 13. GAP / firewall

Introduce e.g.

```lean
inductive Cfzp050CombinedDiscrepancySensitivityEnvelopeGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticLeadingSmoothAbelLogCellReadinessProvider
  | noRelativePrimeCountingDiscrepancyDecayProvider
  | noAutomaticLeftRadialDeficitBudgetProvider
  | noCofinalReducedRemainingQuarterBudgetProvider
```

The old 049 gaps

```text
noCombinedSensitivityAsymptoticEnvelope
noRelativeEnvelopeToQuarterMarginDomination
```

must be retired if Gates E-H are closed.

No PNT/Mertens/Dirichlet/Bertrand/equidistribution/infinite-sum theorem belongs in 050.

---

## 14. Roadmap update

Add CFZP-050 with at least:

```text
leading carrier uniform absolute constant: CLOSED
leading carrier derivative uniform absolute constant: CLOSED
carrier test-function cell sensitivity <= C_car * exp(-sigma U): CLOSED
remainder test-function cell sensitivity <= C_rem * exp(-sigma U): CLOSED
combined sensitivity <= C_sens * exp(-sigma U): CLOSED
relative combined discrepancy explicit cell envelope: CLOSED
exp(R) * exp(-sigma U) -> exp(P) * exp((1-sigma)U): CLOSED
relative envelope and smooth margin share the same exp((1-sigma)U)/U scale: CLOSED
general coefficient condition -> theta * margin: CLOSED
quarter-margin coefficient condition -> combined debt <= margin/4: CLOSED
optional eighth-margin residual-credit specialization: CLOSED if implemented
combined sensitivity asymptotic-envelope gap: RETIRED
relative-envelope to quarter-margin domination gap: RETIRED
relative prime-counting discrepancy decay provider: OPEN / GAP
left radial deficit / cofinal reduced budget provider: OPEN / GAP
automatic SmoothAbel -> SmoothLogCell readiness: OPEN / GAP
automatic interior-strip window provider: OPEN / GAP
CFZP-018 provider / global RH: OUT OF SCOPE
```

---

## 15. Green criterion

CFZP-050 is Green only if the theorem-level chain is explicit:

```text
|L(u)| <= C0
|L'(u)| <= C1

CarrierSensitivity(U,R)
  <= C_car * exp(-sigma U)

RemainderSensitivity(U,R)
  <= C_rem * exp(-sigma U)

CombinedSensitivity(U,R)
  <= C_sens * exp(-sigma U)
```

then, using CFZP-049,

```text
CombinedDebt
  <= delta * exp(R)/U * CombinedSensitivity
  <= delta * exp(P) * C_sens
       * exp((1-sigma)U)/U.
```

And because

```text
Margin
  = exp((1-sigma)U) * M(c)/(4U),
```

prove the finite coefficient reduction

```text
4 * delta * exp(P) * C_sens <= theta * M(c)
------------------------------------------------
CombinedDebt <= theta * Margin.
```

Quarter specialization:

```text
16 * delta * exp(P) * C_sens <= M(c)
------------------------------------------------
CombinedDebt <= Margin/4.
```

There must be **no remaining `U`-dependent competition kernel** in this comparison. The entire cell growth factor must cancel exactly.

After CFZP-050, the next checkpoint should attack the sole arithmetic provider now exposed cleanly: an eventually small **relative finite prime-counting discrepancy** on the exponential carrier cells. That checkpoint must first inspect the current Mathlib `Nat.primeCounting` asymptotic APIs before deciding whether to use a library PNT theorem or a repository-internal route.