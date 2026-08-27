# CFZP-0081 / CFZP-051

## prime-counting PNT → relative cell discrepancy decay — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-049: carrier/remainder discrepancy を同一 prime-counting discrepancy の finite Abel functional へ統合
- CFZP-050: actual carrier/remainder test function から finite sensitivity envelope を生成し、relative discrepancy と smooth margin の座標成長を完全相殺
- CFZP-050 correction: caller-supplied `Cfzp050CellSensitivityEnvelope` を Green-facing `_auto` API から除去

CFZP-050 は Green-A。

---

## 0. 現在の算術 frontier

CFZP-050 後、prime-counting 側の本質的な未閉鎖条件は

```text
Cfzp049PrimeCountingRelativeDiscrepancyBoundAt W c n delta
```

のみである。

既に

```text
CombinedDebt
  <= delta * exp(P) * C_sens(epsilon,W)
       * exp((1-sigma)U) / U
```

かつ

```text
Margin
  = exp((1-sigma)U) * M(c) / (4U)
```

なので、cell coordinate `U` と rectangle exponent `sigma` は競争から消えている。

**CFZP-051 の目的は、標準的な prime number theorem ratio を唯一の arithmetic provider として固定し、その provider から finite exponential carrier cells 上の relative discrepancy bound を eventually 自動生成すること。**

さらに CFZP-050 の coefficient comparison と接続し、eventually

```text
CombinedDebt <= Margin / 8
```

まで運ぶ。

これにより custom GAP

```text
noRelativePrimeCountingDiscrepancyDecayProvider
```

を

```text
one standard PNT ratio provider
```

へ還元する。

---

## 1. Mathlib / dependency audit result — implementation constraint

Current repository:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.32.2"
```

`Mathlib.NumberTheory.PrimeCounting` in v4.32.2 contains:

```text
Nat.primeCounting
Nat.monotone_primeCounting
Nat.tendsto_primeCounting
Nat.primeCounting'_add_le
Nat.primeCounting_add_le
```

but **does not contain the prime number theorem asymptotic** `pi(x) ~ x/log x`.

Mathlib's own theorem-100 tracker points the Prime Number Theorem to the external project
`AlexKontorovich/PrimeNumberTheoremAnd` rather than a Mathlib declaration.

Therefore in CFZP-051:

- do NOT invent a nonexistent Mathlib PNT theorem;
- do NOT add an external Lake dependency yet;
- do NOT modify `lakefile.toml`;
- do NOT copy the PNT+ proof into DkMath;
- define one standard PNT provider interface and prove the full DkMath reduction from it.

A later checkpoint may decide whether to discharge this interface by an external PNT+ dependency, vendored bridge, or an internal DkMath theorem.

---

## 2. New module

Candidate:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeCountingPNTToRelativeDiscrepancyAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeCountingPNTToRelativeDiscrepancyAudit.lean
```

imports:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisCombinedDiscrepancySensitivityEnvelopeAudit
import Mathlib.Tactic
```

Add public import to `DkMath/RH.lean`.

---

## 3. Gate A — canonical PNT ratio on the exact DkMath real/floor interface

Current exact objects:

```text
cfzp040PrimeCountingSmoothModel x
  = x / log x

cfzp040PrimeCountingDiscrepancy x
  = (Nat.primeCounting floor(x) : Real) - x/log x
```

Use the repository's exact current definitions; do not duplicate them.

Define a real/floor PNT ratio function:

```lean
noncomputable def cfzp051PrimeCountingPNTRatio (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ) /
    cfzp040PrimeCountingSmoothModel x
```

and a standard provider:

```lean
def Cfzp051PrimeCountingPNTRatioAtTop : Prop :=
  Filter.Tendsto cfzp051PrimeCountingPNTRatio
    Filter.atTop (nhds 1)
```

This is the sole arithmetic asymptotic provider of this checkpoint.

Also define normalized discrepancy:

```lean
noncomputable def cfzp051PrimeCountingRelativeDiscrepancyRatio (x : ℝ) : ℝ :=
  cfzp040PrimeCountingDiscrepancy x /
    cfzp040PrimeCountingSmoothModel x
```

Green-required theorem:

```lean
theorem cfzp051_pntRatio_implies_relativeDiscrepancyRatio_tendsto_zero
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Filter.Tendsto cfzp051PrimeCountingRelativeDiscrepancyRatio
      Filter.atTop (nhds 0) := by
  ...
```

Proof spine:

```text
for x > 1:
  smooth(x) > 0

relativeDiscrepancyRatio(x)
= primeCountingPNTRatio(x) - 1
```

then use `hPNT.sub_const 1` or the current equivalent filter API.

The equality only needs to hold eventually; use `Filter.Tendsto.congr'` / `Filter.EventuallyEq` rather than proving it at small `x` where `log x = 0` can occur.

Do not weaken the provider to the custom discrepancy statement before recording the standard ratio form.

---

## 4. Gate B — eventual pointwise relative discrepancy

Define the exact eventual property:

```lean
def Cfzp051EventuallyRelativePrimeCountingDiscrepancy
    (delta : ℝ) : Prop :=
  ∀ᶠ x : ℝ in Filter.atTop,
    |cfzp040PrimeCountingDiscrepancy x| <=
      delta * cfzp040PrimeCountingSmoothModel x
```

For every positive tolerance:

```lean
theorem cfzp051_pntRatio_implies_eventually_relativeDiscrepancy
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    {delta : ℝ} (hdelta : 0 < delta) :
    Cfzp051EventuallyRelativePrimeCountingDiscrepancy delta := by
  ...
```

Required reasoning:

```text
relativeDiscrepancyRatio -> 0
=> eventually |relativeDiscrepancyRatio| < delta
=> eventually |discrepancy| <= delta * smooth
```

Carry simultaneously the eventual region `1 < x`, so

```text
0 < log x
0 < smooth(x)
```

and multiplication by the smooth denominator is legal.

Prefer `<=` in the final provider because CFZP-049 uses a non-strict finite bound.

---

## 5. Gate C — carrier-cell left endpoint tends to infinity

Reuse the existing cofinal cell theorem, preferably

```text
cfzp047CarrierCellLeft_tendsto_atTop
```

or current exact equivalent.

Prove:

```lean
theorem cfzp051CarrierCellExpLeft_tendsto_atTop
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => cfzp040CarrierCellExpLeft W c n)
      Filter.atTop Filter.atTop := by
  ...
```

This should be composition of

```text
U_n -> +infinity
exp -> +infinity.
```

Do not introduce a prime-distribution statement here.

---

## 6. Gate D — eventual real pointwise bound → eventual cell provider

This is the main transport theorem.

Green-required:

```lean
theorem cfzp051_pntRatio_implies_eventually_cellRelativeDiscrepancy
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    {delta : ℝ} (hdelta : 0 < delta)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp049PrimeCountingRelativeDiscrepancyBoundAt W c n delta := by
  ...
```

Proof strategy:

1. From Gate B obtain

```text
exists X, forall x >= X,
  |Discrepancy x| <= delta * SmoothModel x.
```

using `eventually_atTop`.

2. From Gate C obtain eventually

```text
X <= exp(U_n).
```

3. For any

```text
x in Icc(exp U_n, exp R_n)
```

we have

```text
X <= exp U_n <= x
```

so the pointwise bound applies.

4. Unfold only

```text
Cfzp049PrimeCountingRelativeDiscrepancyBoundAt
Cfzp040PrimeCountingRelativeDiscrepancyBoundOn
```

as necessary.

This theorem retires the cell-local relative discrepancy provider as an independent arithmetic object: it becomes a direct corollary of one global PNT ratio provider.

---

## 7. Gate E — choose an explicit PNT tolerance that guarantees the eighth-margin coefficient condition

Let

```text
P := cfzp036PrimeAxisCarrierPeriod W
C := cfzp050CombinedSensitivityConstant epsilon W
M := cfzp039ExponentialCarrierPeriodTransform epsilon W c
```

Define a strictly positive safe tolerance:

```lean
noncomputable def cfzp051EighthMarginRelativeTolerance
    (epsilon : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  cfzp039ExponentialCarrierPeriodTransform epsilon W c /
    (32 * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      (cfzp050CombinedSensitivityConstant epsilon W + 1))
```

Equivalent harmless reassociation is fine.

Under

```text
hε : 0 < epsilon
hM : 0 < M
```

prove:

```lean
cfzp051EighthMarginRelativeTolerance_pos
```

and

```lean
theorem cfzp051EighthMarginRelativeTolerance_condition
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c) :
    Cfzp050RelativeDiscrepancyEighthMarginCondition
      epsilon (cfzp051EighthMarginRelativeTolerance epsilon W c) W c := by
  ...
```

Reason:

```text
32 * delta * exp(P) * C
= M * C/(C+1)
<= M.
```

Use `cfzp050CombinedSensitivityConstant_nonneg hε W`.

The `+1` is deliberate: no case split on `C = 0` is needed.

---

## 8. Gate F — eighth-margin theorem from the existing general share theorem

CFZP-050 exposed the eighth coefficient condition but may not have a dedicated debt theorem.

Close it in 051 without duplicating any coefficient algebra.

First prove:

```lean
theorem cfzp051EighthCondition_implies_marginShare
    ... :
    Cfzp050RelativeDiscrepancyMarginShareCondition
      epsilon delta (1 / 8 : ℝ) W c := by
  ...
```

Then:

```lean
theorem cfzp051CombinedDebt_le_eighth_explicitSmoothMargin
    {epsilon delta : ℝ} (hε : 0 < epsilon) (hdelta : 0 <= delta)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hU : 1 <= cfzp039CarrierCellLeft W c n)
    (hCondition : Cfzp050RelativeDiscrepancyEighthMarginCondition
      epsilon delta W c)
    (hDebt : cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n <=
      cfzp050RelativeCombinedDiscrepancyExplicitEnvelope epsilon delta W c n) :
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n <=
      cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  ...
```

Reuse

```text
cfzp050RelativeEnvelope_le_marginShare
```

with `theta = 1/8`.

---

## 9. Gate G — PNT provider gives eventually an eighth-margin cell discrepancy

The Green-facing theorem should no longer ask the caller for a cell-relative discrepancy predicate.

The finite analytic readiness inputs from CFZP-049/050 may remain explicit.

Define a convenience readiness predicate if useful:

```lean
def Cfzp051FiniteDiscrepancyAnalyticReadyAt
    (epsilon : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  IntegrableOn
    (fun x => |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|) ... ∧
  IntegrableOn
    (fun x => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
      cfzp040PrimeCountingDiscrepancy x) ... ∧
  IntegrableOn
    (fun x => |deriv (cfzp048PrimeAxisRemainderTestFunction W) x|) ... ∧
  IntegrableOn
    (fun x => deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
      cfzp040PrimeCountingDiscrepancy x) ...
```

This is finite readiness, not an asymptotic provider.

Then prove a theorem of the shape:

```lean
theorem cfzp051_pntRatio_eventually_combinedDebt_le_eighthMargin
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    (hReady : ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp051FiniteDiscrepancyAnalyticReadyAt epsilon W c n) :
    ∀ᶠ n : ℕ in Filter.atTop,
      cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n <=
        cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  ...
```

Synchronize:

```text
- eventual cell relative discrepancy at delta051
- eventual U >= 1
- eventual finite readiness
```

Then use

```text
cfzp050CombinedDebt_le_explicitRelativeEnvelope_auto
cfzp051EighthMarginRelativeTolerance_condition
cfzp051CombinedDebt_le_eighth_explicitSmoothMargin
```

No `Cfzp050CellSensitivityEnvelope` should appear in this Green-facing theorem.

---

## 10. Gate H — reserve the other eighth for the left radial deficit

Define the useful residual budget:

```lean
def Cfzp051LeftRadialEighthCreditBudgetAt
    (epsilon eta : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
      (cfzp040CarrierCellNaturalLeft W c n) <=
    cfzp044ExplicitSmoothMargin epsilon W c n / 8 + eta
```

Then prove:

```lean
theorem cfzp051_eighthDiscrepancy_and_leftEighthCredit_implies_combinedBudget
    {epsilon eta : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hDisc : cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n <=
      cfzp044ExplicitSmoothMargin epsilon W c n / 8)
    (hLeft : Cfzp051LeftRadialEighthCreditBudgetAt epsilon eta W c n) :
    Cfzp049CombinedRemainingQuarterBudgetAt epsilon eta W c n := by
  ...
```

This is just

```text
G_A <= Margin/8 + eta
D_comb <= Margin/8
---------------------------
G_A + D_comb <= Margin/4 + eta.
```

Do not claim the left radial condition automatically.

---

## 11. Optional Gate I — standard PNT provider equivalence form

If convenient, also expose an equivalent provider closer to textbook notation:

```lean
def Cfzp051PrimeCountingAsymptoticEquivalent : Prop :=
  Filter.Tendsto
    (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x)
    Filter.atTop (nhds 1)
```

and prove equivalence to `Cfzp051PrimeCountingPNTRatioAtTop` eventually on `x > 1`.

This is optional. Do not spend excessive effort if `cfzp040PrimeCountingSmoothModel` form is already a clean PNT interface.

---

## 12. What CFZP-051 must NOT claim

Do not claim:

- Mathlib itself proves PNT;
- `Cfzp051PrimeCountingPNTRatioAtTop` unconditionally from current DkMath imports;
- external `PrimeNumberTheoremAnd` is already a DkMath dependency;
- explicit PNT error terms;
- Mertens / Dirichlet / Bertrand / prime-log equidistribution;
- automatic finite derivative integrability if it remains an explicit premise;
- automatic interior-strip window;
- automatic SmoothAbel -> SmoothLogCell readiness;
- automatic left radial eighth-credit budget;
- CFZP-018 provider;
- global RH.

No new `axiom`, `sorry`, `admit`, or `native_decide`.

---

## 13. GAP / firewall

Introduce e.g.

```lean
inductive Cfzp051PrimeCountingPNTToRelativeDiscrepancyGap : Prop
  | noPrimeCountingPNTRatioProvider
  | noAutomaticFiniteDiscrepancyAnalyticReadinessProvider
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticLeadingSmoothAbelLogCellReadinessProvider
  | noAutomaticLeftRadialEighthCreditBudgetProvider
  | noCofinalFinalRadialBudgetProvider
```

After Green:

```text
custom relative cell discrepancy decay GAP: RETIRED
standard PNT ratio provider: OPEN / GAP
finite derivative-integrability readiness: OPEN / finite analytic readiness
left radial eighth-credit: OPEN / GAP
```

---

## 14. Roadmap update

Add CFZP-051 with at least:

```text
CFZP-050 actual finite sensitivity realization: CLOSED / Green-A
standard real/floor PNT ratio provider interface: DEFINED
PNT ratio -> normalized discrepancy ratio -> 0: CLOSED
PNT ratio -> eventual pointwise relative discrepancy: CLOSED
carrier exp-left tends to +infinity: CLOSED
pointwise eventual bound -> eventual cell-relative bound: CLOSED
explicit positive eighth-margin tolerance: CLOSED
PNT tolerance -> CFZP-050 eighth coefficient condition: CLOSED
eighth coefficient condition -> combined debt <= Margin/8: CLOSED
PNT provider -> eventual combined debt <= Margin/8: CLOSED modulo finite integrability readiness
left radial eighth-credit + discrepancy eighth -> remaining quarter budget: CLOSED
custom relative discrepancy decay provider: RETIRED
standard PNT ratio theorem itself: OPEN / external arithmetic provider
Mathlib PNT theorem: NOT AVAILABLE in current v4.32.2 dependency
external PNT+ dependency: NOT INTRODUCED in CFZP-051
CFZP-018 / global RH: OUT OF SCOPE
```

---

## 15. Green criterion

CFZP-051 is Green only if the following theorem-level chain exists:

```text
PNT ratio:
  primeCounting(floor x) / (x/log x) -> 1

=>

relative discrepancy ratio:
  (primeCounting(floor x) - x/log x) / (x/log x) -> 0

=> for every delta > 0:

  eventually for all large real x,
  |primeCounting(floor x) - x/log x|
    <= delta * x/log x

=> on every sufficiently late carrier cell:

  Cfzp049PrimeCountingRelativeDiscrepancyBoundAt W c n delta
```

Then for the explicit positive

```text
delta051
= M /
  (32 * exp(P) * (C_sens + 1))
```

close

```text
32 * delta051 * exp(P) * C_sens <= M
```

and therefore, with finite analytic readiness,

```text
eventually:
  CombinedDebt <= Margin/8.
```

Finally expose

```text
G_A <= Margin/8 + eta
CombinedDebt <= Margin/8
--------------------------------
G_A + CombinedDebt <= Margin/4 + eta.
```

There must be no remaining custom cell-local prime-distribution provider between the standard PNT ratio assumption and `CombinedDebt <= Margin/8`.

After CFZP-051, do not design CFZP-052 until the implementation is reviewed. The next branch depends on what remains more economical: importing/bridging an external formal PNT theorem, or attacking the left-radial eighth-credit budget first.
