# CFZP-0076 / CFZP-048

## prime-axis remainder finite Abel / smooth-discrepancy reduction — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-039: prime-axis amplitude = leading periodic carrier + `K/u` remainder; finite remainder debt
- CFZP-040: finite Abel summation / prime-counting smooth model + discrepancy functional
- CFZP-043/044: positive-transform late cell and explicit smooth margin
- CFZP-047: higher-prime-power residual domination is CLOSED; eventually raw higher-power mass `<= explicitSmoothMargin / 2`

CFZP-047 は Green-A。

**CFZP-048 の目的は、044/047 の radial budget に残る `cfzp039PrimeAxisRemainderCellDebt` を、prime-counting の finite Abel decomposition に通し、smooth remainder と remainder-discrepancy に分離すること。smooth remainder は explicit smooth margin の `1/U` 下の次数であることを exact finite analysis で示し、eventually quarter-margin 以下まで閉じる。**

重要な診断:

prime-axis remainder term は概念的に

```text
sigmaWeight(p) * K / log p
= K * exp(-σ log p) / log p.
```

一周期 cell で全自然数を overcount すると項数が `~ exp(U)` となるため、

```text
all-natural overcount ~ exp((1-σ)U) / U
```

となり explicit smooth margin と同じ指数・同じ `1/U` 次数まで戻ってしまう。したがって 045–047 の higher-power counting trick を prime-axis remainder にそのまま再利用してはならない。

一方、finite Abel で prime-counting smooth model `x/log x` を入れると、density がさらに `1/log x` を供給し、log 座標で smooth remainder は

```text
exp((1-σ)u) * (1/u^2 - 1/u^3)
```

になる。よって一周期では

```text
SmoothRemainder(cell)
<= K * P * exp((1-σ)(U+P)) / U^2,
```

であり、explicit smooth margin

```text
exp((1-σ)U) * M(c) / (4U)
```

に対して比は `O(1/U)`。

この smooth 部は standard finite analysis だけで消せる。残る remainder-discrepancy は prime-counting discrepancy と同じ種類の有限 debt として次段へ渡す。

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、prime density theorem、infinite prime sums、summability、limit exchange、automatic `σ < 1`、pointwise discrepancy asymptotic、CFZP-018 provider、global RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisRemainderAbelSmoothDiscrepancyAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisRemainderAbelSmoothDiscrepancyAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerCompetitionDecayAudit
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic
```

`DkMath/RH.lean` に公開 import を追加する。

---

## 2. Gate A — canonical remainder test function

prime-axis remainder debt の scalar kernel を x 軸 test function として first-class にする。

```lean
noncomputable def cfzp048PrimeAxisRemainderTestFunction
    (W : PascalCenteredXiResidueTransportWindow)
    (x : ℝ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * Real.log x) / Real.log x
```

prime での exact specialization:

```lean
theorem cfzp048PrimeAxisRemainderTestFunction_natPrime
    (W : PascalCenteredXiResidueTransportWindow)
    {p : ℕ} (hp : Nat.Prime p) :
    cfzp048PrimeAxisRemainderTestFunction W (p : ℝ) =
      cfzp034PrimeAxisSigmaWeight W p / Real.log (p : ℝ) := by
  ...
```

### derivative

`x > 1` の下で derivative を exact に出す。

概念形:

```text
r(x) = exp(-σ log x) / log x
r'(x)
= - exp(-σ log x) / x *
    (σ / log x + 1 / (log x)^2).
```

定義を置いてよい:

```lean
noncomputable def cfzp048PrimeAxisRemainderTestDerivative
    (W : PascalCenteredXiResidueTransportWindow)
    (x : ℝ) : ℝ :=
  -(Real.exp (-(W.rectangle.σ) * Real.log x) / x) *
    (W.rectangle.σ / Real.log x + 1 / (Real.log x)^2)
```

Green-required:

```lean
theorem cfzp048PrimeAxisRemainderTestFunction_hasDerivAt
    (W : PascalCenteredXiResidueTransportWindow)
    {x : ℝ} (hx : 1 < x) :
    HasDerivAt (cfzp048PrimeAxisRemainderTestFunction W)
      (cfzp048PrimeAxisRemainderTestDerivative W x) x := by
  ...
```

`log x > 0` なので denominator nonzero は自動。

さらに finite compact interval `[a,b]`, `1 < a <= b` で derivative の differentiability / integrability を caller premise にせず自動 helper に圧縮することを推奨する。simple continuous function なのでこの段で readiness GAP を増やさない。

---

## 3. Gate B — finite prime remainder sum and Abel identity

040 と同じ prime indicator / primeCounting infrastructure をそのまま再利用する。

```lean
noncomputable def cfzp048PrimeRemainderSumIoc
    (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
    cfzp048PrimeAxisRemainderTestFunction W (k : ℝ) *
      cfzp040PrimeIndicator k
```

finite Abel theorem:

```lean
theorem cfzp048PrimeRemainderSumIoc_eq_abel
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzp048PrimeRemainderSumIoc W a b =
      cfzp048PrimeAxisRemainderTestFunction W b *
          (Nat.primeCounting ⌊b⌋₊ : ℝ) -
        cfzp048PrimeAxisRemainderTestFunction W a *
          (Nat.primeCounting ⌊a⌋₊ : ℝ) -
        ∫ t in Set.Ioc a b,
          deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
            (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  ...
```

`sum_mul_eq_sub_sub_integral_mul` と `cfzp040_sum_primeIndicator_eq_primeCounting` を使う。

ここは finite theorem。prime asymptotic は不要。

---

## 4. Gate C — exact bridge to the CFZP-039 remainder cell debt

natural carrier endpoints:

```text
A := cfzp040CarrierCellNaturalLeft W c n
B := cfzp040CarrierCellNaturalRight W c n
```

late cell では 044 により prime-axis block = eligible block、041/040 の current support bridge により natural prime cell と 039 carrier-cell pair support は exact に一致する。

まず scalar raw sum と pair sum の bridge を閉じる。

Green target:

```lean
theorem cfzp048PrimeAxisRemainderCellDebt_eq_constant_mul_primeRemainderSum
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp039PrimeAxisRemainderCellDebt ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
      cfzp036PrimeAxisRemainderConstant ε W *
        cfzp048PrimeRemainderSumIoc W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) := by
  ...
```

Use repository current exact support APIs; do not guess theorem names. Useful existing facts include conceptually:

```text
cfzp040RawPrimeCarrierCellSupport_mem_iff
cfzp041EligiblePrimeAxisBlockSupport_eq_carrierCellSupport
cfzp044PrimeAxisBlockSupport_eq_eligible
```

If direct pair/nat Finset reindex is awkward, introduce a small sum-reindex helper. Do not weaken equality to an unexplained inequality.

The factor extraction is exact:

```text
sigmaWeight(p) * (K / log p)
= K * (sigmaWeight(p) / log p).
```

`cfzp036PrimeAxisRemainderConstant_pos hε W` is already available.

---

## 5. Gate D — smooth model + remainder-discrepancy functional

Reuse 040's smooth model and discrepancy:

```text
cfzp040PrimeCountingSmoothModel x = x / log x
cfzp040PrimeCountingDiscrepancy x
  = primeCounting(floor x) - x/log x
```

Define the remainder smooth Abel model with exactly the same sign convention as 040:

```lean
noncomputable def cfzp048PrimeRemainderSmoothAbelModel
    (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  cfzp048PrimeAxisRemainderTestFunction W b *
      cfzp040PrimeCountingSmoothModel b -
    cfzp048PrimeAxisRemainderTestFunction W a *
      cfzp040PrimeCountingSmoothModel a -
    ∫ t in Set.Ioc a b,
      deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
        cfzp040PrimeCountingSmoothModel t
```

and discrepancy functional:

```lean
noncomputable def cfzp048PrimeRemainderDiscrepancyFunctional
    (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  cfzp048PrimeAxisRemainderTestFunction W b *
      cfzp040PrimeCountingDiscrepancy b -
    cfzp048PrimeAxisRemainderTestFunction W a *
      cfzp040PrimeCountingDiscrepancy a -
    ∫ t in Set.Ioc a b,
      deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
        cfzp040PrimeCountingDiscrepancy t
```

Then exact finite split:

```lean
theorem cfzp048PrimeRemainderSumIoc_eq_smooth_add_discrepancy
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzp048PrimeRemainderSumIoc W a b =
      cfzp048PrimeRemainderSmoothAbelModel W a b +
        cfzp048PrimeRemainderDiscrepancyFunctional W a b := by
  ...
```

Use only the exact identity

```text
primeCounting floor x = SmoothModel x + Discrepancy x.
```

No estimate yet.

---

## 6. Gate E — smooth remainder density integral

042 already proved the derivative of the smooth prime-counting model:

```text
cfzp042PrimeCountingSmoothDensity x
= 1/log x - 1/(log x)^2.
```

For the simple remainder test function, use finite integration by parts to prove:

```lean
theorem cfzp048PrimeRemainderSmoothAbelModel_eq_densityIntegral
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzp048PrimeRemainderSmoothAbelModel W a b =
      ∫ t in Set.Ioc a b,
        cfzp048PrimeAxisRemainderTestFunction W t *
          cfzp042PrimeCountingSmoothDensity t := by
  ...
```

Finite regularity should be proved automatically here from `1<a<=b`; do not create a new abstract readiness provider if continuity suffices.

---

## 7. Gate F — exact log-coordinate smooth remainder

Define the cell log integral:

```lean
noncomputable def cfzp048PrimeRemainderSmoothLogCell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  ∫ u in cfzp039CarrierCellLeft W c n..
      cfzp039CarrierCellRight W c n,
    Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
      (1 / u^2 - 1 / u^3)
```

Green target:

```lean
theorem cfzp048PrimeRemainderSmoothAbelCell_eq_logCell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 < cfzp039CarrierCellLeft W c n) :
    cfzp048PrimeRemainderSmoothAbelModel W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp048PrimeRemainderSmoothLogCell W c n := by
  ...
```

Under substitution `x = exp u`:

```text
r(exp u) = exp(-σu)/u
smoothDensity(exp u) = 1/u - 1/u^2
dx = exp(u) du
```

so exactly

```text
exp((1-σ)u) * (1/u^2 - 1/u^3).
```

Use `cfzp039PrimeAxisGrowthExponent W = 1 - W.rectangle.σ` definitionally/algebraically.

Orientation is `U < R`, so no sign reversal.

---

## 8. Gate G — smooth remainder is one inverse power smaller

Work under named interior strip:

```text
hstrip : Cfzp039PrimeAxisInteriorStrip W
```

which gives

```text
β := cfzp039PrimeAxisGrowthExponent W > 0.
```

Let

```text
U := cfzp039CarrierCellLeft W c n
R := cfzp039CarrierCellRight W c n = U + P
P := cfzp036PrimeAxisCarrierPeriod W > 0.
```

For `U >= 2`, prove pointwise on `[U,R]`:

```text
0 <= 1/u^2 - 1/u^3
1/u^2 - 1/u^3 <= 1/U^2
exp(βu) <= exp(βR).
```

Then finite interval bound:

```lean
theorem cfzp048PrimeRemainderSmoothLogCell_le
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp048PrimeRemainderSmoothLogCell W c n ≤
      cfzp036PrimeAxisCarrierPeriod W *
        Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellRight W c n) /
        (cfzp039CarrierCellLeft W c n)^2 := by
  ...
```

Also prove nonnegativity of the smooth log cell under `U>=2`.

Define the structural smooth remainder debt:

```lean
noncomputable def cfzp048PrimeAxisSmoothRemainderCellDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp036PrimeAxisRemainderConstant ε W *
    cfzp048PrimeRemainderSmoothLogCell W c n
```

and its explicit envelope:

```lean
noncomputable def cfzp048PrimeAxisSmoothRemainderEnvelope
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp036PrimeAxisRemainderConstant ε W *
    cfzp036PrimeAxisCarrierPeriod W *
    Real.exp (cfzp039PrimeAxisGrowthExponent W *
      cfzp039CarrierCellRight W c n) /
    (cfzp039CarrierCellLeft W c n)^2
```

Close:

```text
0 <= SmoothRemainderCellDebt
SmoothRemainderCellDebt <= SmoothRemainderEnvelope.
```

---

## 9. Gate H — explicit quarter-margin domination

Positive transform:

```text
M := cfzp039ExponentialCarrierPeriodTransform ε W c > 0.
```

Explicit smooth margin:

```text
Margin = exp(βU) * M / (4U).
```

Since `R=U+P`, Gate G envelope is

```text
Krem * P * exp(β(U+P)) / U^2
= exp(βU) * (Krem * P * exp(βP) / U^2).
```

To make this `<= Margin / 4`, it suffices that

```text
16 * Krem * P * exp(βP) <= M * U.
```

Define an explicit threshold, e.g.

```lean
noncomputable def cfzp048PrimeAxisRemainderQuarterMarginThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  max (cfzp044RadialLateThreshold ε W c)
    (16 * cfzp036PrimeAxisRemainderConstant ε W *
      cfzp036PrimeAxisCarrierPeriod W *
      Real.exp (cfzp039PrimeAxisGrowthExponent W *
        cfzp036PrimeAxisCarrierPeriod W) /
      cfzp039ExponentialCarrierPeriodTransform ε W c)
```

Then Green-required:

```lean
theorem cfzp048PrimeAxisSmoothRemainderEnvelope_le_quarter_explicitSmoothMargin
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp048PrimeAxisRemainderQuarterMarginThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp048PrimeAxisSmoothRemainderEnvelope ε W c n ≤
      cfzp044ExplicitSmoothMargin ε W c n / 4 := by
  ...
```

Use exact `R=U+P` and exponential addition. No asymptotic theorem is necessary; this can be finite algebra from the explicit threshold.

Then via Gate G:

```text
SmoothRemainderCellDebt <= Margin / 4.
```

Cofinal version should follow from `cfzp043_carrierCellLeft_eventually_ge`.

---

## 10. Gate I — remainder-discrepancy debt and full remainder bound

Define the cell discrepancy functional:

```lean
noncomputable def cfzp048PrimeRemainderCellDiscrepancyFunctional
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp048PrimeRemainderDiscrepancyFunctional W
    (cfzp040CarrierCellExpLeft W c n)
    (cfzp040CarrierCellExpRight W c n)
```

Define the positive scaled discrepancy debt:

```lean
noncomputable def cfzp048PrimeAxisRemainderDiscrepancyCellDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp036PrimeAxisRemainderConstant ε W *
    |cfzp048PrimeRemainderCellDiscrepancyFunctional W c n|
```

Prove nonnegative.

Using Gate C/D/E/F, close exact/one-sided cell decomposition:

```lean
theorem cfzp048PrimeAxisRemainderCellDebt_le_smooth_add_discrepancyDebt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp039PrimeAxisRemainderCellDebt ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp048PrimeAxisSmoothRemainderCellDebt ε W c n +
        cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n := by
  ...
```

The exact sum is `K * (Smooth + Discrepancy)`; only the final `Discrepancy <= |Discrepancy|` is an inequality.

Then combine Gate H:

```lean
theorem cfzp048PrimeAxisRemainderCellDebt_le_quarterMargin_add_discrepancyDebt
    ...
    (hLate048 : cfzp048PrimeAxisRemainderQuarterMarginThreshold ε W c ≤ U) :
    cfzp039PrimeAxisRemainderCellDebt ... ≤
      cfzp044ExplicitSmoothMargin ε W c n / 4 +
        cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n := by
  ...
```

This is the main structural remainder elimination theorem.

---

## 11. Gate J — combine with CFZP-047 higher-power half-margin

047 already gives eventually:

```text
HigherPowerReferenceMass <= Margin / 2.
```

048 gives eventually:

```text
PrimeAxisRemainderDebt <= Margin / 4 + RemainderDiscrepancyDebt.
```

Therefore define the remaining-quarter budget:

```lean
def Cfzp048RemainingQuarterMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    D + cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n ≤
      cfzp044ExplicitSmoothMargin ε W c n / 4 + η
```

Here `D` remains the existing CFZP-041 carrier discrepancy debt bound.

Green-required radial adapter:

```lean
theorem cfzp048RemainingQuarterMarginBudget_implies_radialContactDeficit_le
    {ε η D : ℝ} ...
    (hHigher : cfzp034HigherPowerReferenceMass ε W A B ≤
      cfzp044ExplicitSmoothMargin ε W c n / 2)
    (hRemainder : cfzp039PrimeAxisRemainderCellDebt ε W c n A B ≤
      cfzp044ExplicitSmoothMargin ε W c n / 4 +
        cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n)
    (hQuarter : Cfzp048RemainingQuarterMarginBudgetAt ε η D W c n)
    ... :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  ...
```

Use 044 exact exceptional mass = `0` and build `Cfzp044ExplicitSmoothMarginBudgetAt` by `linarith`, then apply 044 main theorem.

Also provide a cofinal/eventual wrapper combining:

- 047 eventual higher-power half-margin;
- 048 cofinal smooth-remainder quarter threshold;
- the quarter-budget provider supplied by later discrepancy work.

Do **not** claim the quarter budget itself automatically holds yet.

---

## 12. Gap / firewall

Introduce e.g.

```lean
inductive Cfzp048PrimeAxisRemainderAbelSmoothDiscrepancyGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticLeadingSmoothAbelLogCellReadinessProvider
  | noPrimeCountingCarrierDiscrepancyFunctionalDecayProvider
  | noPrimeAxisRemainderDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToCombinedFunctionalBound
  | noCofinalRemainingQuarterMarginBudgetProvider
```

Important change in frontier:

```text
prime-axis structural smooth remainder domination: CLOSED
prime-axis remainder discrepancy: OPEN / GAP
```

Do not retain a vague `noPrimeAxisRemainderCellDebtDecayProvider` if the raw remainder has now been exactly reduced to smooth + discrepancy and the smooth part is dominated. Name the actual remaining gap.

Forbidden in CFZP-048:

- PNT
- Mertens
- Dirichlet
- Bertrand
- prime-log equidistribution
- prime density theorem
- infinite prime sums
- summability / limit exchange
- automatic `σ < 1`
- pointwise prime-counting discrepancy asymptotic
- unconditional discrepancy decay
- CFZP-018 provider
- global RH

---

## 13. Roadmap update

Add CFZP-048 section with at least:

```text
remainder x-axis test function / derivative: CLOSED
finite prime remainder Abel identity: CLOSED
039 remainder-cell debt = K * raw prime remainder sum: CLOSED
prime remainder sum = smooth Abel + discrepancy functional: CLOSED
smooth Abel = smooth-density integral: CLOSED
smooth remainder log-coordinate transform: CLOSED
smooth remainder <= K*P*exp(βR)/U^2: CLOSED
smooth remainder eventual/threshold <= explicit margin / 4: CLOSED
remainder cell debt <= margin/4 + remainder-discrepancy debt: CLOSED
remaining-quarter budget -> radial endpoint: CLOSED
higher-prime-power residual domination: CLOSED (from 047)
prime-axis structural smooth remainder domination: CLOSED
prime-axis remainder discrepancy decay: OPEN / GAP
carrier discrepancy decay: OPEN / GAP
pointwise discrepancy -> combined functional debt: OPEN / GAP
leading SmoothAbel -> SmoothLogCell readiness: OPEN / GAP
actual cofinal remaining-quarter budget provider: OPEN / GAP
infinite prime distribution / global RH: OUT OF SCOPE
```

---

## 14. Green criterion

CFZP-048 is Green only if the theorem-level chain is explicit:

```text
039 prime-axis remainder cell debt
  = K * finite prime sum of exp(-σ log p)/log p
  = K * (smooth remainder Abel + remainder discrepancy)

smooth remainder Abel
  = integral on x-axis against d(x/log x)
  = integral_U^R exp((1-σ)u)*(1/u^2 - 1/u^3) du
  <= K-free P*exp((1-σ)R)/U^2

therefore, sufficiently late positive-transform cell:
  structural smooth remainder debt <= explicitSmoothMargin / 4

hence:
  full prime-axis remainder debt
    <= explicitSmoothMargin / 4 + remainderDiscrepancyDebt.
```

Together with CFZP-047:

```text
higher-power debt <= explicitSmoothMargin / 2
```

and a remaining-quarter budget for starting deficit + carrier discrepancy + remainder discrepancy, derive the radial endpoint.

The essential mathematical result of this checkpoint is that the `K/log p` remainder is **not** eliminated by distribution-free counting; instead, finite Abel exposes an additional smooth-density `1/log` factor, lowering the structural smooth remainder from `1/U` to `1/U^2`. The only genuinely arithmetic residue is then a prime-counting discrepancy functional.

After CFZP-048, the next checkpoint should attack the **combined carrier + remainder prime-counting discrepancy functionals**, preferably from one pointwise finite discrepancy envelope, while keeping the leading-carrier analytic readiness separate.