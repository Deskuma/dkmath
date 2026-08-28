# CFZP-0078 / CFZP-049

## combined prime-counting discrepancy functional envelope — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-040: finite Abel / `primeCounting = smooth + discrepancy`
- CFZP-041: carrier discrepancy cell debt and radial reservoir
- CFZP-048: remainder discrepancy functional, structural smooth remainder `<= Margin/4`
- CFZP-047: higher-prime-power residual `<= Margin/2` eventually
- corrected CFZP-048: true remaining-quarter budget

CFZP-048 corrected Gate J は Green-A。

**CFZP-049 の目的は、現在別々に残っている carrier discrepancy functional と remainder discrepancy functional を、同一の pointwise prime-counting discrepancy `E(x)` から一括して支配する finite theorem layer を作ること。**

ここで

```text
E(x) := cfzp040PrimeCountingDiscrepancy x
      = primeCounting(floor x) - x/log x.
```

carrier functional も remainder functional も、同じ有限 Abel 形

```text
f(b) E(b) - f(a) E(a) - ∫_a^b f'(x) E(x) dx
```

である。違うのは test function `f` だけ。

したがって本段では generic finite Abel-discrepancy norm lemma を first-class にし、それを二つの test functionへ適用する。

**本段では PNT や discrepancy asymptotic を証明しない。**

049 で閉じる gap は

```text
pointwise discrepancy bound
    -> carrier discrepancy functional bound
    -> remainder discrepancy functional bound
    -> combined discrepancy debt bound
```

である。

PNT / relative-error decay provider は次段以降へ残す。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisCombinedDiscrepancyEnvelopeAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisCombinedDiscrepancyEnvelopeAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisRemainderAbelSmoothDiscrepancyAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に公開 import を追加する。

---

## 2. Canonical cell notation

以下を何度も使うので、必要なら local abbreviations / helper definitions を置いてよい。

```text
a := cfzp040CarrierCellExpLeft  W c n
b := cfzp040CarrierCellExpRight W c n
E := cfzp040PrimeCountingDiscrepancy
```

`a < b` は既存 theorem:

```text
cfzp040CarrierCellExpLeft_lt_right
```

から取る。

---

## 3. Gate A — generic finite Abel discrepancy functional

まず任意 test function `f` に対する finite discrepancy functional を定義する。

```lean
noncomputable def cfzp049FiniteAbelDiscrepancyFunctional
    (f : ℝ -> ℝ) (a b : ℝ) : ℝ :=
  f b * cfzp040PrimeCountingDiscrepancy b -
    f a * cfzp040PrimeCountingDiscrepancy a -
    ∫ x in Set.Ioc a b,
      deriv f x * cfzp040PrimeCountingDiscrepancy x
```

そして sensitivity norm:

```lean
noncomputable def cfzp049FiniteAbelSensitivity
    (f : ℝ -> ℝ) (a b : ℝ) : ℝ :=
  |f b| + |f a| +
    ∫ x in Set.Ioc a b, |deriv f x|
```

Green-required basic facts:

```lean
theorem cfzp049FiniteAbelSensitivity_nonneg ... :
  0 <= cfzp049FiniteAbelSensitivity f a b
```

under the finite integrability assumptions actually needed by Lean.

Do not introduce infinite integrals.

---

## 4. Gate B — generic pointwise-to-functional absolute bound

This is the mathematical core of CFZP-049.

Target:

```lean
theorem cfzp049FiniteAbelDiscrepancyFunctional_abs_le
    {a b Δ : ℝ}
    (hab : a <= b)
    (hΔ : 0 <= Δ)
    (hPoint : Cfzp040PrimeCountingDiscrepancyBoundOn a b Δ)
    (hDerivAbsInt : IntegrableOn
      (fun x => |deriv f x|) (Set.Ioc a b))
    (hDerivDiscInt : IntegrableOn
      (fun x => deriv f x * cfzp040PrimeCountingDiscrepancy x)
      (Set.Ioc a b)) :
    |cfzp049FiniteAbelDiscrepancyFunctional f a b| <=
      Δ * cfzp049FiniteAbelSensitivity f a b := by
  ...
```

Exact premise list may be adjusted to the interval-integral / set-integral API.

Proof spine:

```text
|f(b)E(b) - f(a)E(a) - ∫ f'E|
<= |f(b)||E(b)| + |f(a)||E(a)| + |∫ f'E|
<= Δ|f(b)| + Δ|f(a)| + ∫ Δ|f'|
= Δ (|f(b)| + |f(a)| + ∫ |f'|).
```

Use:

- endpoint membership in `Icc a b`;
- `hPoint` at `a`, `b`, and interior points;
- `abs_integral_le_integral_abs` / finite integral monotonicity APIs as available;
- `|f' E| = |f'| |E|`;
- `hΔ`.

Do not weaken this to an unexplained external functional bound. The purpose is to prove the pointwise-to-functional bridge.

---

## 5. Gate C — carrier discrepancy is the generic functional

Carrier test:

```text
f_carrier(x) := cfzp040PrimeAxisCarrierTestFunction ε W x
```

Green-required exact identity:

```lean
theorem cfzp049CarrierDiscrepancyFunctional_eq_generic
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) :
    cfzp040PrimeCountingDiscrepancyFunctional ε W a b =
      cfzp049FiniteAbelDiscrepancyFunctional
        (cfzp040PrimeAxisCarrierTestFunction ε W) a b := by
  rfl
```

Define canonical cell sensitivity:

```lean
noncomputable def cfzp049CarrierDiscrepancyCellSensitivity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp049FiniteAbelSensitivity
    (cfzp040PrimeAxisCarrierTestFunction ε W)
    (cfzp040CarrierCellExpLeft W c n)
    (cfzp040CarrierCellExpRight W c n)
```

Then:

```lean
theorem cfzp049CarrierDiscrepancyCellDebt_le
    {ε Δ : ℝ}
    ...
    (hPoint : Cfzp040PrimeCountingDiscrepancyBoundOn a b Δ)
    ... :
    cfzp041PrimeCountingDiscrepancyCellDebt ε W c n <=
      Δ * cfzp049CarrierDiscrepancyCellSensitivity ε W c n := by
  ...
```

This theorem should bound the actual existing 041 debt, not a duplicate definition.

---

## 6. Gate D — remainder discrepancy is the same generic functional

Remainder test:

```text
f_rem(x) := cfzp048PrimeAxisRemainderTestFunction W x
```

Green-required exact identity:

```lean
theorem cfzp049RemainderDiscrepancyFunctional_eq_generic
    (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) :
    cfzp048PrimeRemainderDiscrepancyFunctional W a b =
      cfzp049FiniteAbelDiscrepancyFunctional
        (cfzp048PrimeAxisRemainderTestFunction W) a b := by
  rfl
```

Define:

```lean
noncomputable def cfzp049RemainderDiscrepancyCellSensitivity
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp049FiniteAbelSensitivity
    (cfzp048PrimeAxisRemainderTestFunction W)
    (cfzp040CarrierCellExpLeft W c n)
    (cfzp040CarrierCellExpRight W c n)
```

Recall existing debt:

```text
cfzp048PrimeAxisRemainderDiscrepancyCellDebt
= K_rem * |remainder discrepancy functional|.
```

Prove:

```lean
theorem cfzp049RemainderDiscrepancyCellDebt_le
    {ε Δ : ℝ} (hε : 0 < ε)
    ...
    (hPoint : Cfzp040PrimeCountingDiscrepancyBoundOn a b Δ)
    ... :
    cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n <=
      cfzp036PrimeAxisRemainderConstant ε W *
        (Δ * cfzp049RemainderDiscrepancyCellSensitivity W c n) := by
  ...
```

Equivalent reassociation is fine.

Use positivity of `cfzp036PrimeAxisRemainderConstant`.

---

## 7. Gate E — combined discrepancy debt and combined sensitivity

Define the actual unpaid discrepancy debt:

```lean
noncomputable def cfzp049CombinedPrimeCountingDiscrepancyCellDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp041PrimeCountingDiscrepancyCellDebt ε W c n +
    cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n
```

Define combined sensitivity:

```lean
noncomputable def cfzp049CombinedPrimeCountingDiscrepancySensitivity
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp049CarrierDiscrepancyCellSensitivity ε W c n +
    cfzp036PrimeAxisRemainderConstant ε W *
      cfzp049RemainderDiscrepancyCellSensitivity W c n
```

Prove nonnegative under the minimal hypotheses.

Main theorem:

```lean
theorem cfzp049CombinedPrimeCountingDiscrepancyCellDebt_le
    {ε Δ : ℝ} (hε : 0 < ε)
    ...
    (hPoint : Cfzp040PrimeCountingDiscrepancyBoundOn a b Δ)
    ... :
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt ε W c n <=
      Δ * cfzp049CombinedPrimeCountingDiscrepancySensitivity ε W c n := by
  ...
```

This is Green-required.

At this point the old two-gap picture

```text
carrier discrepancy functional
remainder discrepancy functional
```

must be replaceable by one finite pointwise discrepancy provider plus one explicit sensitivity.

---

## 8. Gate F — pointwise cell provider interface

Create a canonical cell alias, e.g.

```lean
def Cfzp049PrimeCountingPointwiseDiscrepancyBoundAt
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) (Δ : ℝ) : Prop :=
  Cfzp040PrimeCountingDiscrepancyBoundOn
    (cfzp040CarrierCellExpLeft W c n)
    (cfzp040CarrierCellExpRight W c n)
    Δ
```

Provide exact wrapper theorem from Gate E using this predicate.

Also define relative version by reusing 040 rather than duplicating semantics:

```lean
def Cfzp049PrimeCountingRelativeDiscrepancyBoundAt
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) (δ : ℝ) : Prop :=
  Cfzp040PrimeCountingRelativeDiscrepancyBoundOn
    (cfzp040CarrierCellExpLeft W c n)
    (cfzp040CarrierCellExpRight W c n)
    δ
```

No asymptotic provider is asserted here.

---

## 9. Gate G — preserve the crucial `1/U` in relative-error conversion

This gate prepares the next checkpoint and is Green-required if it can be closed cleanly.

Let

```text
U := cfzp039CarrierCellLeft W c n
R := cfzp039CarrierCellRight W c n
b := exp R.
```

For a late cell with `1 <= U`, every `x ∈ [exp U, exp R]` has

```text
U <= log x
x <= exp R.
```

Hence

```text
x / log x <= exp(R) / U.
```

Prove a helper equivalent to:

```lean
theorem cfzp049PrimeCountingSmoothModel_le_cellScale
    (hU : 1 <= U)
    {x : ℝ}
    (hx : x ∈ Set.Icc (exp U) (exp R)) :
    cfzp040PrimeCountingSmoothModel x <=
      Real.exp R / U := by
  ...
```

Adapt exact endpoint definitions.

Then relative discrepancy bound

```text
|E(x)| <= δ * x/log x
```

implies the uniform pointwise bound

```text
|E(x)| <= δ * exp(R)/U
```

provided `0 <= δ`.

Target wrapper:

```lean
theorem cfzp049RelativeDiscrepancy_implies_pointwiseCellBound
    {δ : ℝ} (hδ : 0 <= δ)
    ... (hRel : Cfzp049PrimeCountingRelativeDiscrepancyBoundAt W c n δ) :
    Cfzp049PrimeCountingPointwiseDiscrepancyBoundAt W c n
      (δ * Real.exp (cfzp039CarrierCellRight W c n) /
        cfzp039CarrierCellLeft W c n) := by
  ...
```

Equivalent parenthesization is fine.

**Do not lose the `/ U`.**

A crude `Δ = δ * exp R` is mathematically true but strategically too weak; it destroys the scale needed for the margin comparison.

---

## 10. Gate H — combined relative-discrepancy envelope

Compose Gates E and G.

Define, if useful:

```lean
noncomputable def cfzp049RelativeCombinedDiscrepancyEnvelope
    (ε δ : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  (δ * Real.exp (cfzp039CarrierCellRight W c n) /
      cfzp039CarrierCellLeft W c n) *
    cfzp049CombinedPrimeCountingDiscrepancySensitivity ε W c n
```

Then prove:

```lean
theorem cfzp049CombinedDebt_le_relativeEnvelope
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 <= δ)
    ...
    (hRel : Cfzp049PrimeCountingRelativeDiscrepancyBoundAt W c n δ)
    ... :
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt ε W c n <=
      cfzp049RelativeCombinedDiscrepancyEnvelope ε δ W c n := by
  ...
```

This theorem is the desired public handoff to the next checkpoint.

---

## 11. Gate I — corrected CFZP-048 remaining-quarter adapter using one combined debt

The corrected 048 budget is currently

```text
G_A + CarrierDebt + RemainderDebt <= Margin/4 + eta
```

where the carrier part is represented by the external `D` satisfying the 041 functional bound.

Add a 049 convenience predicate that names the exact combined debt directly:

```lean
def Cfzp049CombinedRemainingQuarterBudgetAt
    (ε η : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt ε W c n <=
      cfzp044ExplicitSmoothMargin ε W c n / 4 + η
```

Then bridge this to corrected 048.

Use

```text
D := cfzp041PrimeCountingDiscrepancyCellDebt ε W c n
```

and prove the 041 bound trivially by reflexivity / abs equality.

Green target:

```lean
theorem cfzp049CombinedRemainingQuarterBudget_implies_radialContactDeficit_le
    ...
    (hHigher : HigherPower <= Margin/2)
    (hRemainderStructuralCertificates : ...)
    (hCombined : Cfzp049CombinedRemainingQuarterBudgetAt ε η W c n) :
    radialDeficit(right endpoint) <= eta := by
  ...
```

Prefer calling the corrected 048 structural wrapper rather than rebuilding 044 directly.

The point is that after 049 the final arithmetic budget visibly contains only:

```text
starting radial deficit + one combined discrepancy debt.
```

---

## 12. Optional Gate J — generic sensitivity facts

Useful but not required if they make the checkpoint too large:

```text
carrier sensitivity nonnegative
remainder sensitivity nonnegative
combined sensitivity nonnegative
relative envelope nonnegative
```

Also useful:

```text
combined sensitivity = carrier sensitivity + K * remainder sensitivity
```

by `rfl` / simplification.

Do not start a large trigonometric constant audit unless it is needed for the Green-required gates.

---

## 13. What remains OPEN after CFZP-049

Expected frontier:

```text
pointwise discrepancy -> carrier functional bound: CLOSED
pointwise discrepancy -> remainder functional bound: CLOSED
pointwise discrepancy -> combined discrepancy debt: CLOSED
relative discrepancy -> uniform cell discrepancy scale with /U: CLOSED
combined relative-discrepancy finite envelope: CLOSED
combined discrepancy budget -> radial endpoint: CLOSED with supplied structural/analytic certificates

explicit carrier/remainder sensitivity asymptotic envelope: OPEN
relative prime-counting discrepancy decay provider: OPEN
automatic PNT/relative-error hookup: OPEN
leading SmoothAbel -> SmoothLogCell readiness: OPEN
interior-strip provider: OPEN
starting radial deficit / cofinal final budget: OPEN
CFZP-018 provider / global RH: OUT OF SCOPE
```

The old separate gaps

```text
noPrimeCountingCarrierDiscrepancyFunctionalDecayProvider
noPrimeAxisRemainderDiscrepancyFunctionalDecayProvider
noPointwiseDiscrepancyToCombinedFunctionalBound
```

should be refined. After 049 the structural pointwise-to-functional gap is CLOSED; only the source of sufficiently small pointwise/relative discrepancy remains open.

---

## 14. Firewall

Forbidden in CFZP-049:

- proving or importing PNT as the closure step
- Mertens
- Dirichlet
- Bertrand as a distribution substitute
- prime-log equidistribution
- infinite prime sums
- summability / limit exchange
- automatic `σ < 1`
- unconditional discrepancy decay
- CFZP-018 provider
- global RH

Finite `Nat.primeCounting`, finite integrals, existing exact Abel identities, and abstract pointwise/relative discrepancy predicates are allowed.

---

## 15. Green criterion

CFZP-049 is Green only if the theorem-level chain is explicit:

```text
one pointwise discrepancy bound |E(x)| <= Δ on [a,b]
  |
  +--> |CarrierDiscrepancyFunctional|
  |      <= Δ * CarrierSensitivity
  |
  +--> K * |RemainderDiscrepancyFunctional|
         <= Δ * K * RemainderSensitivity

therefore

CombinedDebt
<= Δ * CombinedSensitivity.
```

And for a relative pointwise bound:

```text
|E(x)| <= δ * x/log x
        <= δ * exp(R)/U
```

so

```text
CombinedDebt
<= [δ * exp(R)/U] * CombinedSensitivity.
```

Finally this exact combined debt must feed a convenience version of the corrected 048 remaining-quarter radial adapter.

The essential mathematical gain of CFZP-049 is conceptual as well as formal:

**carrier discrepancy and remainder discrepancy are not two independent arithmetic enemies. They are two bounded linear finite Abel functionals of the same prime-counting error `E(x)`. After 049, the arithmetic frontier should be represented by one pointwise/relative discrepancy provider and an explicit finite sensitivity norm.**
