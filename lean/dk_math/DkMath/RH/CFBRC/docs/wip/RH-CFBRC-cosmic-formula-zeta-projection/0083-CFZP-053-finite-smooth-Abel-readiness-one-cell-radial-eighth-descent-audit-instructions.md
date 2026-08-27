# CFZP-0083 / CFZP-053

## finite smooth-Abel readiness + one-cell radial eighth descent — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-049: carrier/remainder discrepancy を一つの combined debt へ統合
- CFZP-050: actual test functions から finite sensitivity envelope を実現
- CFZP-051: standard PNT ratio provider から eventual `CombinedDebt <= Margin / 8` へ reduction
- CFZP-052: finite discrepancy analytic readiness を actual finite-cell estimates から自動生成し、051 Green-facing theorem から `hReady` を除去

CFZP-052 は **Green-A**。

---

## 0. 今回の狙い

CFZP-052 後、prime-counting discrepancy 側は、標準 PNT ratio provider を除けば finite analytic plumbing まで閉じた。

しかし radial endpoint theorem

```lean
cfzp049CombinedRemainingQuarterBudget_implies_radialContactDeficit_le
```

にはなお、以下の有限 smooth-Abel 証明書が explicit input として残っている。

```text
hG_int
hSplit
hDebtEq
hSmoothEq
hSmoothLog
hf_diff
hf_int
hM_int
hD_int
```

このうち `hD_int` は CFZP-052 ですでに自動化済みであり、残りも PNT や無限極限とは無関係な **有限セル解析** である。

CFZP-053 の第一目的は、これらを actual carrier/remainder test functions と 042/048 の finite identities から自動生成すること。

第二目的は、その auto-ready endpoint theorem を使って、CFZP-051 の discrepancy eighth-credit を単なる「remaining-quarter budget の半分」ではなく、**一セルごとの radial deficit の実減少**へ変換すること。

概念的に

```text
G_n := radial deficit at NaturalLeft(n)
M_n := explicit smooth margin at cell n
D_n := combined discrepancy debt at cell n
```

と置く。

CFZP-051/052 から late cell では

```text
D_n <= M_n / 8.
```

049 の remaining-quarter condition に

```text
eta := G_n - M_n / 8
```

を代入すると

```text
G_n + D_n
<= G_n + M_n/8
 = M_n/4 + (G_n - M_n/8).
```

したがって 049 endpoint theorem は

```text
G(right_n) <= G_n - M_n/8
```

を返す。

さらに carrier cells は連結しているので

```text
NaturalRight(n) = NaturalLeft(n+1).
```

ゆえに最終的に

```text
G_{n+1} <= G_n - M_n/8
```

を得る。

**この one-cell descent が CFZP-053 の新しい魔核である。**

なお本 checkpoint では、`sum M_n` の発散や最終的な `G_n <= eta` までは主張しない。それは一セル descent を有限和へ畳み込んだ後に別 checkpoint で攻める。

---

## 1. New module

推奨:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFiniteSmoothAbelReadinessRadialEighthDescentAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaFiniteSmoothAbelReadinessRadialEighthDescentAudit.lean
```

imports:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaFiniteDiscrepancyAnalyticReadinessAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

---

## 2. Canonical notation / existing APIs

概念的に:

```text
U_n := cfzp039CarrierCellLeft W c n
R_n := cfzp039CarrierCellRight W c n
P   := cfzp036PrimeAxisCarrierPeriod W

a_n := cfzp040CarrierCellExpLeft W c n
b_n := cfzp040CarrierCellExpRight W c n

A_n := cfzp040CarrierCellNaturalLeft W c n
B_n := cfzp040CarrierCellNaturalRight W c n

G_A(n) := pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W A_n
G_B(n) := pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W B_n

Margin(n) := cfzp044ExplicitSmoothMargin epsilon W c n
Debt(n)   := cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n
```

重要な既存 API:

```text
cfzp040CarrierCellExpLeft_pos
cfzp040CarrierCellExpLeft_lt_right
cfzp040_log_carrierCellExpLeft
cfzp040_log_carrierCellExpRight
cfzp046CarrierCellRight_eq_left_add_period
cfzp047CarrierCellLeft_tendsto_atTop

cfzp040PrimeAxisCarrierTestFunction_hasDerivAt
cfzp042CarrierTestFunction_hasDerivAt
cfzp042PrimeCountingSmoothModel_hasDerivAt
cfzp042SmoothAbelCarrierModel_eq_densityIntegral
cfzp042SmoothDensityIntegral_eq_logCellIntegral

cfzp048PrimeAxisRemainderTestFunction_hasDerivAt
cfzp048PrimeRemainderSumIoc_eq_smooth_add_discrepancy
cfzp048PrimeRemainderSmoothAbelModel_eq_densityIntegral
cfzp048PrimeRemainderSmoothAbelCell_eq_logCell
cfzp048PrimeAxisRemainderCellDebt_eq_constant_mul_primeRemainderSum

cfzp052CarrierDerivativeAbs_integrableOn
cfzp052RemainderDerivativeAbs_integrableOn
cfzp052CarrierDerivativeMulDiscrepancy_integrableOn
cfzp052RemainderDerivativeMulDiscrepancy_integrableOn
cfzp052_primeCountingSmoothModel_measurable
cfzp052_pntRatio_eventually_combinedDebt_le_eighthMargin_autoReady

cfzp049CombinedRemainingQuarterBudget_implies_radialContactDeficit_le
```

Use exact current signatures from repository. If a theorem name differs slightly, use the existing declaration rather than duplicating it.

---

## 3. Gate A — late-cell geometry package

A large fraction of the smooth readiness only needs a cell safely to the right of `1`.

Define a compact helper if useful:

```lean
def Cfzp053LateSmoothCell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat) : Prop :=
  2 <= cfzp039CarrierCellLeft W c n
```

or simply pass `hU : 2 <= U_n`.

From this prove/reuse:

```text
1 < U_n
1 < exp(U_n)
0 < a_n
0 < b_n
U_n <= R_n
for x in Icc(a_n,b_n): 1 < x and 0 < log x
```

Do not introduce a new asymptotic notion for this.

The quarter threshold

```text
cfzp048PrimeAxisRemainderQuarterMarginThreshold epsilon W c <= U_n
```

already implies the radial-late threshold and hence `2 <= U_n`.

---

## 4. Gate B — automatic carrier differentiability and derivative integrability

049 currently asks for

```lean
hf_diff : forall t in Icc a_n b_n,
  DifferentiableAt Real (cfzp040PrimeAxisCarrierTestFunction epsilon W) t

hf_int : IntegrableOn
  (deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W))
  (Icc a_n b_n)
```

Close both from the actual derivative theorem.

Green-required target shapes:

```lean
theorem cfzp053CarrierTestFunction_differentiableOn_cell
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 2 <= cfzp039CarrierCellLeft W c n) :
    forall x in Set.Icc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt Real
        (cfzp040PrimeAxisCarrierTestFunction epsilon W) x := by
  ...
```

and

```lean
theorem cfzp053CarrierDerivative_integrableOn_Icc
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 2 <= cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W))
      (Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  ...
```

Prefer to reuse the explicit derivative formula / continuity machinery introduced in CFZP-052. Do not re-derive the trig derivative.

It is fine to first establish interval integrability of the explicit formula and transfer by pointwise equality on the cell.

---

## 5. Gate C — automatic remainder differentiability and derivative integrability

Analogously close:

```lean
theorem cfzp053RemainderTestFunction_differentiableOn_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 2 <= cfzp039CarrierCellLeft W c n) :
    forall x in Set.Icc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt Real
        (cfzp048PrimeAxisRemainderTestFunction W) x := by
  ...
```

and the `Icc` derivative integrability needed by

```text
cfzp048PrimeRemainderSumIoc_eq_smooth_add_discrepancy.
```

Again use the existing exact HasDerivAt theorem and finite compact cell positivity.

---

## 6. Gate D — smooth model density finite regularity

042/048 density-integral theorems use

```text
cfzp042PrimeCountingSmoothModel_hasDerivAt
cfzp042PrimeCountingSmoothDensity
```

on the finite positive cell.

Close the reusable finite facts:

```lean
theorem cfzp053SmoothModel_hasDerivAt_on_cell ...

theorem cfzp053SmoothDensity_intervalIntegrable ...
```

for `2 <= U_n`.

Also establish interval integrability of:

```text
cfzp042CarrierTestFunctionDerivative epsilon W
cfzp048PrimeAxisRemainderTestDerivative W
```

on `a_n..b_n`.

These are smooth functions on a compact interval bounded away from `0` and `1`; `ContinuousOn.intervalIntegrable` is preferred.

---

## 7. Gate E — automatic derivative × smooth-model integrability

CFZP-052 automatically closed derivative × discrepancy. 053 must close the parallel smooth terms required by 040/048:

```lean
theorem cfzp053CarrierDerivativeMulSmooth_integrableOn
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 2 <= cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (fun x =>
        deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
          cfzp040PrimeCountingSmoothModel x)
      (Set.Ioc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  ...
```

and

```lean
theorem cfzp053RemainderDerivativeMulSmooth_integrableOn ...
```

No PNT is needed. On a finite late cell:

```text
0 <= x/log x <= x <= b_n
```

and CFZP-050 already provides finite derivative bounds.

You may reuse CFZP-052's general bounded-measurable integrability helper where convenient.

---

## 8. Gate F — carrier SmoothAbel -> SmoothLogCell auto realization

042 already separates this into two finite steps:

```text
cfzp042SmoothAbelCarrierModel_eq_densityIntegral
cfzp042SmoothDensityIntegral_eq_logCellIntegral
```

Build the regularity inputs internally.

Required Green-facing theorem:

```lean
theorem cfzp053CarrierSmoothAbel_eq_logCell_auto
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 2 <= cfzp039CarrierCellLeft W c n) :
    cfzp040SmoothAbelCarrierModel epsilon W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp042SmoothLogCellIntegral epsilon W c n := by
  ...
```

For the change-of-variables readiness, prove internally:

```text
ContinuousOn
  (carrierTest * smoothDensity)
  (exp '' uIcc U_n R_n)

IntegrableOn
  (carrierTest * smoothDensity)
  (exp '' uIcc U_n R_n)

IntegrableOn
  (((carrierTest * smoothDensity) o exp) * exp)
  (uIcc U_n R_n)
```

All are finite compact regularity statements.

This theorem retires

```text
noAutomaticLeadingSmoothAbelLogCellReadinessProvider
```

from the Green-facing chain.

---

## 9. Gate G — remainder split and SmoothAbel -> SmoothLogCell auto realization

First close the exact finite split automatically:

```lean
theorem cfzp053PrimeRemainderSum_eq_smooth_add_discrepancy_auto
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 2 <= cfzp039CarrierCellLeft W c n) :
    cfzp048PrimeRemainderSumIoc W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp048PrimeRemainderSmoothAbelModel W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) +
      cfzp048PrimeRemainderCellDiscrepancyFunctional W c n := by
  ...
```

Use:

```text
cfzp048PrimeRemainderSumIoc_eq_smooth_add_discrepancy
```

with:
- automatic remainder differentiability;
- automatic derivative integrability;
- automatic derivative × smooth integrability;
- CFZP-052 automatic derivative × discrepancy integrability.

Then close the log-cell identity:

```lean
theorem cfzp053RemainderSmoothAbel_eq_logCell_auto
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 2 <= cfzp039CarrierCellLeft W c n) :
    cfzp048PrimeRemainderSmoothAbelModel W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp048PrimeRemainderSmoothLogCell W c n := by
  ...
```

Reuse:

```text
cfzp048PrimeRemainderSmoothAbelModel_eq_densityIntegral
cfzp048PrimeRemainderSmoothAbelCell_eq_logCell
```

and generate all finite continuity/integrability premises internally.

---

## 10. Gate H — smooth remainder log-integrand interval integrability

049 also asks for:

```lean
hG_int : IntervalIntegrable
  (fun u => exp(beta*u) * (1/u^2 - 1/u^3))
  volume U_n R_n
```

For `2 <= U_n`, this integrand is continuous on `uIcc U_n R_n`.

Close:

```lean
theorem cfzp053RemainderSmoothLogIntegrand_intervalIntegrable
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hU : 2 <= cfzp039CarrierCellLeft W c n) :
    IntervalIntegrable
      (fun u =>
        Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
          (1 / u ^ 2 - 1 / u ^ 3))
      volume
      (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n) := by
  ...
```

No asymptotic input.

---

## 11. Gate I — exact remainder debt identity auto adapter

049 asks for:

```text
hDebtEq :
  RemainderCellDebt = Krem * PrimeRemainderSumIoc.
```

This is already an exact finite theorem in 048:

```text
cfzp048PrimeAxisRemainderCellDebt_eq_constant_mul_primeRemainderSum
```

Add a small canonical cell wrapper if its current arguments are inconvenient, but **do not reprove the identity**.

The Green-facing 053 radial theorem must not ask the caller for `hDebtEq`.

---

## 12. Gate J — aggregate all finite smooth readiness

A helper structure/predicate is fine internally, e.g.

```lean
structure Cfzp053FiniteSmoothRadialReadyAt
    (epsilon : Real)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat) : Prop where
  smoothLog : ...
  remainderSplit : ...
  remainderDebtEq : ...
  remainderSmoothEq : ...
  carrierDiff : ...
  carrierDerivInt : ...
  carrierDerivSmoothInt : ...
  carrierDerivDiscInt : ...
  remainderLogInt : ...
```

But, as in CFZP-050 correction, **do not leave this as a caller-supplied provider**.

Required:

```lean
theorem cfzp053FiniteSmoothRadialReadyAt_of_threshold
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hThreshold :
      cfzp048PrimeAxisRemainderQuarterMarginThreshold epsilon W c <=
        cfzp039CarrierCellLeft W c n) :
    Cfzp053FiniteSmoothRadialReadyAt epsilon W c n := by
  ...
```

If no structure is introduced, provide equivalent `_auto` wrappers directly.

---

## 13. Gate K — natural endpoint contiguity

This is structurally important and should be a named theorem.

First coordinate contiguity:

```lean
theorem cfzp053CarrierCellRight_eq_nextLeft
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat) :
    cfzp039CarrierCellRight W c n =
      cfzp039CarrierCellLeft W c (n + 1) := by
  ...
```

Then exponential endpoints:

```lean
theorem cfzp053CarrierCellExpRight_eq_nextExpLeft ... :
  cfzp040CarrierCellExpRight W c n =
    cfzp040CarrierCellExpLeft W c (n + 1) := by
  ...
```

Finally the natural endpoints:

```lean
theorem cfzp053CarrierCellNaturalRight_eq_nextNaturalLeft
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat) :
    cfzp040CarrierCellNaturalRight W c n =
      cfzp040CarrierCellNaturalLeft W c (n + 1) := by
  ...
```

This should be exact by the definitions and

```text
R_n = U_n + P = U_{n+1}.
```

No floor inequality is needed once the real endpoints are shown equal.

---

## 14. Gate L — one-cell radial eighth descent

This is the main theorem of CFZP-053.

Inputs may keep genuinely non-finite providers explicit:

```text
hstrip : Cfzp039PrimeAxisInteriorStrip W
hM     : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c
hThreshold
hHigher : HigherPowerReferenceMass <= Margin/2
hDisc   : CombinedDebt <= Margin/8
```

All finite smooth readiness from Gates B-J must be internal.

Target:

```lean
theorem cfzp053_oneCell_radialDeficit_le_sub_eighthMargin
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hThreshold :
      cfzp048PrimeAxisRemainderQuarterMarginThreshold epsilon W c <=
        cfzp039CarrierCellLeft W c n)
    (hHigher :
      cfzp034HigherPowerReferenceMass epsilon W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) <=
        cfzp044ExplicitSmoothMargin epsilon W c n / 2)
    (hDisc :
      cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n <=
        cfzp044ExplicitSmoothMargin epsilon W c n / 8) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
        (cfzp040CarrierCellNaturalRight W c n) <=
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
          (cfzp040CarrierCellNaturalLeft W c n) -
        cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  ...
```

Proof spine:

```text
let G := radial deficit at left
let M := explicit margin
let eta := G - M/8

hDisc : D <= M/8

G + D <= G + M/8
        = M/4 + (G - M/8)
        = M/4 + eta
```

Hence construct

```lean
Cfzp049CombinedRemainingQuarterBudgetAt epsilon eta W c n
```

and feed

```text
cfzp049CombinedRemainingQuarterBudget_implies_radialContactDeficit_le
```

using the auto finite smooth readiness from this checkpoint.

**Do not assume the left radial eighth-credit predicate. This theorem derives an actual radial decrease from the discrepancy eighth.**

---

## 15. Gate M — left-to-next-left recurrence

Compose Gate L with natural endpoint contiguity.

Define if useful:

```lean
noncomputable def cfzp053LeftRadialDeficit
    (epsilon : Real)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) (n : Nat) : Real :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
    (cfzp040CarrierCellNaturalLeft W c n)
```

Then Green-required:

```lean
theorem cfzp053_leftRadialDeficit_succ_le_sub_eighthMargin
    ...same structural inputs... :
    cfzp053LeftRadialDeficit epsilon W c (n + 1) <=
      cfzp053LeftRadialDeficit epsilon W c n -
        cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  ...
```

This is the canonical recurrence for the next checkpoint.

---

## 16. Gate N — eventual recurrence under the PNT provider

Use CFZP-052:

```text
cfzp052_pntRatio_eventually_combinedDebt_le_eighthMargin_autoReady
```

to obtain eventual `hDisc` with **no finite readiness input**.

For higher powers and quarter-threshold, reuse the existing 047/048 eventual synchronization theorem, preferably:

```text
cfzp048_eventually_higherPowerHalf_and_remainderQuarterLate
```

or the current exact equivalent.

It may require:

```text
hsub : Cfzp027SubcriticalPhaseAspect W
```

Keep that geometric hypothesis explicit if no existing implication from `hstrip` is available.

Green-required theorem shape:

```lean
theorem cfzp053_pntRatio_eventually_leftRadialDeficit_succ_le_sub_eighthMargin
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : Real)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    forallᶠ n : Nat in Filter.atTop,
      cfzp053LeftRadialDeficit epsilon W c (n + 1) <=
        cfzp053LeftRadialDeficit epsilon W c n -
          cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  ...
```

The key point is that this theorem must not ask for:

```text
finite IntegrableOn readiness
hSmoothLog
hSplit
hSmoothEq
hDebtEq
cell-relative discrepancy provider
left radial eighth-credit provider
```

Those are all eliminated before this theorem.

---

## 17. Gate O — finite telescoping of the radial descent

Do not yet prove an infinite sum theorem. But the finite iteration should be recorded now.

A generic helper is acceptable:

```lean
theorem cfzp053_leftRadialDeficit_iterate_le_sub_sum
    {epsilon : Real}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real)
    (N m : Nat)
    (hstep : forall k : Nat, N <= k ->
      cfzp053LeftRadialDeficit epsilon W c (k + 1) <=
        cfzp053LeftRadialDeficit epsilon W c k -
          cfzp044ExplicitSmoothMargin epsilon W c k / 8) :
    cfzp053LeftRadialDeficit epsilon W c (N + m) <=
      cfzp053LeftRadialDeficit epsilon W c N -
        sum k in Finset.range m,
          cfzp044ExplicitSmoothMargin epsilon W c (N + k) / 8 := by
  ...
```

Equivalent indexing is fine. Prove by finite induction only.

Then turn an eventual recurrence into a thresholded finite telescoping theorem:

```text
exists N, forall m,
  G_{N+m} <= G_N - sum_{k<m} Margin_{N+k}/8.
```

This exposes the next exact frontier:

```text
how much cumulative positive smooth credit does the tail supply?
```

Do **not** claim divergence yet.

---

## 18. Optional but valuable — relation to the old left-eighth-credit predicate

The old CFZP-051 predicate

```lean
Cfzp051LeftRadialEighthCreditBudgetAt epsilon eta W c n
```

is still useful as an endpoint adapter, but after this checkpoint it should no longer be treated as a primitive mysterious provider.

Show a sufficient cumulative-credit form if convenient:

```text
if
  G_N - sum_{k=N}^{n-1} Margin_k/8 <= Margin_n/8 + eta,
then
  Cfzp051LeftRadialEighthCreditBudgetAt epsilon eta W c n.
```

This is algebraic and clarifies that the remaining problem is cumulative credit, not another local prime-distribution estimate.

---

## 19. GAP / firewall after CFZP-053

Introduce/update e.g.

```lean
inductive Cfzp053FiniteSmoothAbelReadinessRadialEighthDescentGap : Prop
  | noPrimeCountingPNTRatioProvider
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSubcriticalAspectProvider
  | noCumulativeEighthMarginCreditEscapeProvider
  | noCofinalFinalRadialBudgetProvider
```

Retire if Gates F-J close:

```text
noAutomaticLeadingSmoothAbelLogCellReadinessProvider
finite smooth-Abel readiness provider
remainder finite split provider
remainder SmoothAbel -> SmoothLogCell provider
```

Do not introduce or claim:

- a proof of PNT;
- an external PNT dependency;
- Mertens / Dirichlet / Bertrand / prime-log equidistribution;
- infinite prime sums;
- exchange of sum/integral/limit;
- divergence of the smooth-margin series unless actually proved;
- automatic `sigma < 1`;
- automatic subcritical aspect unless an existing theorem supplies it;
- global RH.

---

## 20. Roadmap update

Add CFZP-053, preferably section 65, with at least:

```text
carrier differentiability / derivative finite-cell readiness: CLOSED
remainder differentiability / derivative finite-cell readiness: CLOSED
carrier derivative * smooth-model integrability: CLOSED
remainder derivative * smooth-model integrability: CLOSED
carrier SmoothAbel -> SmoothLogCell readiness: CLOSED automatically
remainder finite smooth+discrepancy split: CLOSED automatically
remainder SmoothAbel -> SmoothLogCell readiness: CLOSED automatically
remainder smooth log-integrand interval integrability: CLOSED automatically
canonical remainder debt equality hookup: CLOSED
all finite smooth radial readiness: CLOSED from late threshold
carrier real/exp/natural endpoint contiguity: CLOSED
combined discrepancy eighth -> one-cell radial deficit decrease by Margin/8: CLOSED
left-to-next-left radial eighth recurrence: CLOSED
PNT provider -> eventual radial eighth recurrence: CLOSED modulo explicit window hypotheses
finite telescoping of radial eighth recurrence: CLOSED
finite discrepancy analytic readiness: inherited CLOSED from CFZP-052
standard PNT ratio theorem: OPEN / external arithmetic provider
automatic interior-strip / subcritical window provider: OPEN / GAP
cumulative eighth-margin credit sufficient for final radial escape: OPEN / GAP
CFZP-018 / global RH: OUT OF SCOPE
```

---

## 21. Green criterion

CFZP-053 is Green only if the theorem-level chain is explicit:

```text
late finite carrier cell
  |
  +--> actual carrier/remainder differentiability
  +--> finite derivative integrability
  +--> finite derivative*smooth integrability
  +--> finite SmoothAbel -> LogCell identities
  +--> remainder split / debt identity
  |
  `--> all 049 finite smooth readiness generated internally
```

then

```text
PNT ratio provider
  ↓
CFZP-052 eventual CombinedDebt <= Margin/8
  ↓
049 remaining-quarter endpoint theorem
  with eta := G_left - Margin/8
  ↓
G_right <= G_left - Margin/8
  ↓
NaturalRight(n) = NaturalLeft(n+1)
  ↓
G_{n+1} <= G_n - Margin_n/8
```

and finally finite iteration:

```text
G_{N+m}
<= G_N - sum_{k<m} Margin_{N+k}/8.
```

There must be **no caller-supplied finite SmoothAbel readiness** and **no caller-supplied left radial eighth-credit** in the Green-facing one-cell/eventual recurrence theorem.

After this checkpoint, the radial problem should be exposed as a cumulative-credit question rather than another local discrepancy problem.
