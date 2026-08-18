# CFZP-0074 / CFZP-046

## higher-prime-power deterministic cell counting / exponential envelope — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-039: prime-axis leading carrier / remainder / finite radial reservoir
- CFZP-043: late positive smooth cell
- CFZP-044: explicit smooth margin; late exceptional prime-axis mass = `0`
- CFZP-045: raw higher-prime-power reference mass `<= K(ε,W) * finite sigma tail`

CFZP-045 は Green-A。

current source で閉じた主要 API:

```text
cfzp045HigherPowerActualExponent_two_le
cfzp045HigherPower_basePrime
cfzp045HigherPowerReferenceMassConstant
cfzp045HigherPowerSigmaTail
cfzp045HigherPowerReferenceMass_le_sigmaTail
cfzp045CarrierCellHigherPowerBlockSafe
cfzp045CarrierCellHigherPowerReferenceMass_le_sigmaTail
Cfzp045SigmaTailExplicitSmoothMarginBudgetAt
cfzp045SigmaTailExplicitSmoothMarginBudget_implies_radialContactDeficit_le
```

CFZP-046 の目的は、045 に残った finite sigma tail を、prime distribution を一切使わず、**一周期 cell の幾何だけで explicit exponential envelope に置換すること**。

中心構造は次。

higher-power pair の actual exponent を `j >= 2`、cell 左右を

```text
U := cfzp039CarrierCellLeft W c n
R := cfzp039CarrierCellRight W c n
P := cfzp036PrimeAxisCarrierPeriod W
```

とする。cell support から exact に

```text
U < j * log p <= R
```

を回収する。

`j >= 2` より

```text
log p <= R / 2
p <= exp (R / 2)
```

また `p >= 2` より

```text
j * log 2 <= j * log p <= R
j <= R / log 2.
```

したがって higher-power support は、prime distribution を知らなくても有限 rectangular box に入る。

各 sigma-tail term は

```text
sigmaWeight(p)^j / j
= exp (-σ * (j log p)) / j
<= exp (-σ * U) / 2.
```

これを card bound と結合し、最終的に概念上

```text
HigherPowerSigmaTail(cell)
<= exp (R / 2) * (R / log 2 + 1) * exp (-σ U)
```

まで閉じる。

さらに `R = U + P` を用いて

```text
exp(R/2) * exp(-σ U)
= exp(P/2) * exp((1/2 - σ) U)
```

へ正規化する。

この段ではまだ `U -> ∞` の limit / eventual domination は証明しない。CFZP-047 が

```text
polynomial(U) * exp(-U/2) -> 0
```

を使って explicit smooth margin に対する eventual domination を閉じる。

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite prime sums、summability、limit exchange、automatic `σ < 1`、CFZP-018 provider、global RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerCellCountingEnvelopeAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaHigherPrimePowerCellCountingEnvelopeAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerSigmaTailEnvelopeAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に公開 import を追加する。

---

## 2. Gate A — expose exact higher-power cell log interval

045 の late-safety proof 内部では既に floor / exp / log bridge を通して cell lower bound を作っている。
046 ではこれを explicit public theorem とする。

cell natural endpoints:

```text
A := cfzp040CarrierCellNaturalLeft W c n
B := cfzp040CarrierCellNaturalRight W c n
```

higher pair `pk` の actual exponent:

```text
j := pk.2 + 1
```

target:

```lean
theorem cfzp046HigherPowerPairLogCoordinate_mem_carrierCell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)) :
    cfzp039CarrierCellLeft W c n <
        cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) ∧
      cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) ≤
        cfzp039CarrierCellRight W c n := by
  ...
```

これは distribution-free finite support theorem。

proof は 045 `cfzp045CarrierCellHigherPowerBlockSafe` の `hqgtA`, `hqleB`, `hqL`, `hqR`, `hlogL`, `hlogR`, `hcoord` の流れを再利用する。

重複が大きすぎる場合のみ、045 側から small public helper を抽出してよい。数学的内容を変更しないこと。

同時に cell geometry:

```lean
theorem cfzp046CarrierCellRight_eq_left_add_period
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp039CarrierCellRight W c n =
      cfzp039CarrierCellLeft W c n +
        cfzp036PrimeAxisCarrierPeriod W := by
  ...
```

を閉じる。

---

## 3. Gate B — base cap from `j >= 2`

base cap を first-class にする。

```lean
noncomputable def cfzp046HigherPowerBaseCap
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.exp (cfzp039CarrierCellRight W c n / 2)⌋₊
```

late cell で higher pair がこの cap 以下に入ることを証明する。

```lean
theorem cfzp046HigherPower_base_le_baseCap
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)) :
    pk.1 ≤ cfzp046HigherPowerBaseCap W c n := by
  ...
```

proof spine:

1. Gate A: `j log p <= R`;
2. 045: `2 <= j`;
3. `0 < log p` from base prime;
4. derive `2 * log p <= R`, hence `log p <= R/2`;
5. exponentiate: `(p : ℝ) <= exp(R/2)`;
6. `Nat.le_floor` bridge.

`hLate` is used only to provide convenient positivity/nonnegativity of `R`; do not smuggle distribution input into it.

---

## 4. Gate C — exponent cap from `p >= 2`

actual exponent cap:

```lean
noncomputable def cfzp046HigherPowerExponentCap
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℕ :=
  ⌊cfzp039CarrierCellRight W c n / Real.log 2⌋₊
```

prove:

```lean
theorem cfzp046HigherPower_actualExponent_le_exponentCap
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)) :
    pk.2 + 1 ≤ cfzp046HigherPowerExponentCap W c n := by
  ...
```

proof spine:

1. base prime gives `2 <= p`;
2. monotonicity of log gives `log 2 <= log p`;
3. multiply by positive actual exponent `j`;
4. Gate A gives `j log p <= R`;
5. conclude `(j:ℝ) <= R / log 2` using `Real.log_pos (by norm_num : 1 < (2:ℝ))`;
6. floor bridge.

Do not use prime-counting or number of primes.

---

## 5. Gate D — deterministic finite bounding box

Use a deliberately coarse `range × range` box so card arithmetic stays simple.

```lean
noncomputable def cfzp046HigherPowerBoundingBox
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (cfzp046HigherPowerBaseCap W c n + 1)).product
    (Finset.range (cfzp046HigherPowerExponentCap W c n + 1))
```

Then:

```lean
theorem cfzp046HigherPowerPairBlockSupport_subset_boundingBox
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp034HigherPowerPairBlockSupport
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ⊆
      cfzp046HigherPowerBoundingBox W c n := by
  ...
```

second coordinate is `pk.2`, while Gate C bounds `pk.2 + 1`; `omega` で十分。

cardinality:

```lean
theorem cfzp046HigherPowerPairBlockSupport_card_le
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    (cfzp034HigherPowerPairBlockSupport
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n)).card ≤
      (cfzp046HigherPowerBaseCap W c n + 1) *
        (cfzp046HigherPowerExponentCap W c n + 1) := by
  ...
```

`Finset.card_le_card` + `Finset.card_product` + `Finset.card_range` だけで閉じるのが望ましい。

これは **prime-counting theorem ではない**。全自然数 base / exponent の rectangular overcount。

---

## 6. Gate E — uniform sigma-tail term bound on one cell

cell lower endpointを `U` とする。

higher pair では:

```text
U < u := j log p
σ > 1/2 > 0
j >= 2
```

従って

```text
exp(-σ u) / j <= exp(-σ U) / 2.
```

034 power identity を使い target:

```lean
theorem cfzp046HigherPowerSigmaTailTerm_le_cellUniform
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)) :
    (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
        ((pk.2 + 1 : ℕ) : ℝ) ≤
      Real.exp (-(W.rectangle.σ) *
          cfzp039CarrierCellLeft W c n) / 2 := by
  ...
```

No late assumption should be necessary if Gate A gives strict `U < u`; `σ > 0` comes from `cfzp034_rectangleSigma_gt_half`.

Use:

```text
cfzp034PrimePowerSigmaWeight_eq_primeAxisWeight_pow
cfzp045HigherPowerActualExponent_two_le
```

Do not weaken to `<= exp(-σU)`; keep the useful `1/2` factor.

---

## 7. Gate F — finite sigma tail <= card envelope

Combine Gate D/E:

```lean
theorem cfzp046HigherPowerSigmaTail_le_cardEnvelope
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp045HigherPowerSigmaTail W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      (((cfzp046HigherPowerBaseCap W c n + 1) *
          (cfzp046HigherPowerExponentCap W c n + 1) : ℕ) : ℝ) *
        (Real.exp (-(W.rectangle.σ) *
          cfzp039CarrierCellLeft W c n) / 2) := by
  ...
```

Finite `Finset.sum` only。

---

## 8. Gate G — remove floors: explicit real exponential envelope

Define a real envelope with no finite-card object left.

```lean
noncomputable def cfzp046HigherPowerSigmaTailExponentialEnvelope
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (cfzp039CarrierCellRight W c n / 2) *
    (cfzp039CarrierCellRight W c n / Real.log 2 + 1) *
    Real.exp (-(W.rectangle.σ) *
      cfzp039CarrierCellLeft W c n)
```

under radial-late, prove floor-cap estimates:

```text
(baseCap : ℝ) + 1 <= exp(R/2) + 1 <= 2 * exp(R/2)
(exponentCap : ℝ) + 1 <= R/log 2 + 1
```

and therefore:

```lean
theorem cfzp046HigherPowerSigmaTail_le_exponentialEnvelope
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp045HigherPowerSigmaTail W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp046HigherPowerSigmaTailExponentialEnvelope W c n := by
  ...
```

ここで `/2` と `baseCap + 1 <= 2 exp(R/2)` を相殺する。

### canonical exponential normal form

`R = U + P` を使って:

```lean
theorem cfzp046HigherPowerSigmaTailExponentialEnvelope_eq_normalForm
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp046HigherPowerSigmaTailExponentialEnvelope W c n =
      Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
        (cfzp039CarrierCellRight W c n / Real.log 2 + 1) *
        Real.exp ((1 / 2 - W.rectangle.σ) *
          cfzp039CarrierCellLeft W c n) := by
  ...
```

これが 046 の数学的主結果。

`cfzp034_rectangleSigma_gt_half` より exponent coefficient は strict negative:

```lean
theorem cfzp046_half_sub_rectangleSigma_neg
    (W : PascalCenteredXiResidueTransportWindow) :
    (1 / 2 : ℝ) - W.rectangle.σ < 0 := by
  ...
```

ただし **この段では envelope -> 0 の Tendsto はまだ証明しない**。

---

## 9. Gate H — raw higher-power reference mass <= explicit envelope

045 と Gate G を合成する。

```lean
theorem cfzp046CarrierCellHigherPowerReferenceMass_le_exponentialEnvelope
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp034HigherPowerReferenceMass ε W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp045HigherPowerReferenceMassConstant ε W *
        cfzp046HigherPowerSigmaTailExponentialEnvelope W c n := by
  ...
```

No new arithmetic assumption.

---

## 10. Gate I — explicit-envelope radial budget

045 budget から finite sigma-tail object も消す。

```lean
def Cfzp046ExponentialEnvelopeExplicitSmoothMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp039PrimeAxisRemainderCellDebt ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) +
    cfzp045HigherPowerReferenceMassConstant ε W *
      cfzp046HigherPowerSigmaTailExponentialEnvelope W c n + D ≤
    cfzp044ExplicitSmoothMargin ε W c n + η
```

main adapter:

```lean
theorem cfzp046ExponentialEnvelopeExplicitSmoothMarginBudget_implies_radialContactDeficit_le
    ...
    (hbudget : Cfzp046ExponentialEnvelopeExplicitSmoothMarginBudgetAt
      ε η D W c n) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  ...
```

proof:

1. Gate G: sigma tail <= exponential envelope;
2. convert 046 budget -> 045 budget;
3. apply `cfzp045SigmaTailExplicitSmoothMarginBudget_implies_radialContactDeficit_le`.

Keep all 044/045 premises explicit; do not invent readiness providers.

---

## 11. Gate J — expose the higher-power vs smooth-margin competition kernel

This Gate is important because it identifies exactly what CFZP-047 must send to zero.

Define:

```lean
noncomputable def cfzp046HigherPowerMarginCompetitionKernel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  8 * cfzp039CarrierCellLeft W c n *
    cfzp045HigherPowerReferenceMassConstant ε W *
    Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
    (cfzp039CarrierCellRight W c n / Real.log 2 + 1) *
    Real.exp (-(cfzp039CarrierCellLeft W c n) / 2)
```

The key cancellation is

```text
(1/2 - σ)U - (1 - σ)U = -U/2.
```

Thus, under positive transform and radial-late cell, prove a sufficient-condition theorem:

```lean
theorem cfzp046HigherPowerEnvelope_le_half_explicitSmoothMargin_of_kernel
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hkernel : cfzp046HigherPowerMarginCompetitionKernel ε W c n ≤
      cfzp039ExponentialCarrierPeriodTransform ε W c) :
    cfzp045HigherPowerReferenceMassConstant ε W *
        cfzp046HigherPowerSigmaTailExponentialEnvelope W c n ≤
      cfzp044ExplicitSmoothMargin ε W c n / 2 := by
  ...
```

Use only exact definitions:

```text
cfzp044ExplicitSmoothMargin
cfzp039PrimeAxisGrowthExponent = 1 - σ
cfzp046...Envelope_eq_normalForm
```

This theorem is finite algebra. No limit theorem.

### Optional but preferred budget compression

Define remaining-half budget:

```lean
def Cfzp046RemainingHalfMarginBudgetAt
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

Then `hkernel` + remaining-half budget should imply the 046 full budget and radial endpoint.

If proof is short, close:

```text
cfzp046RemainingHalfMarginBudget_implies_radialContactDeficit_le
```

This adapter is preferred but may be omitted if it merely duplicates several pages of 044 regularity premises. Gate J's half-margin theorem itself is Green-required.

---

## 12. Gap / firewall

Introduce e.g.

```lean
inductive Cfzp046HigherPrimePowerCellCountingEnvelopeGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothAbelLogCellReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noHigherPowerCompetitionKernelEventualDecay
  | noPrimeAxisRemainderCellDebtDecayProvider
  | noCofinalExponentialEnvelopeBudgetProvider
```

The following are forbidden in CFZP-046:

- PNT
- Mertens
- Dirichlet
- Bertrand
- prime-log equidistribution
- any prime density lower/upper theorem
- infinite prime sums
- summability
- limit exchange
- automatic `σ < 1`
- unconditional discrepancy decay
- unconditional remainder elimination
- CFZP-018 provider
- global RH

Important: `baseCap` counts **all natural bases**, not primes. `exponentCap` counts all natural exponents. This deliberate overcount is the firewall that keeps 046 distribution-free.

---

## 13. Roadmap update

Add CFZP-046 section with at least:

```text
higher-power pair log-coordinate cell interval: CLOSED
j >= 2 -> base <= exp(R/2): CLOSED
p >= 2 -> j <= R/log 2: CLOSED
deterministic finite bounding box: CLOSED
higher-power support cardinality bound: CLOSED
uniform cell sigma-tail term <= exp(-σU)/2: CLOSED
finite sigma tail <= cardinality envelope: CLOSED
floor-free exponential envelope: CLOSED
normal form exp(P/2)*(R/log2+1)*exp((1/2-σ)U): CLOSED
raw higher-power mass <= K * exponential envelope: CLOSED
exponential-envelope budget -> radial endpoint: CLOSED
higher-power vs smooth-margin competition kernel: CLOSED
kernel condition -> higher debt <= half smooth margin: CLOSED
competition-kernel eventual decay: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
prime-axis remainder-cell debt decay: OPEN / GAP
actual cofinal budget provider: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

---

## 14. Green criterion

CFZP-046 is Green only if theorem-level chain is exact:

```text
higher pair in one natural carrier cell
  -> U < j log p <= R
  -> p <= floor(exp(R/2))
     and j <= floor(R/log 2)
  -> finite rectangular card bound
  -> sigma tail <= exp(R/2)*(R/log2+1)*exp(-σU)
  -> raw higher-power mass <= K * explicit exponential envelope
  -> explicit-envelope budget -> radial endpoint
```

and additionally the smooth-margin comparison is exposed as

```text
competitionKernel(U)
  = explicit constant * U * (R/log2+1) * exp(-U/2)

competitionKernel(U) <= positiveTransform
  -> higher-power envelope <= explicitSmoothMargin / 2.
```

The essential mathematical result of this checkpoint is that **the decay exponent competing against the smooth margin is `-U/2`, independent of the rectangle sigma exponent after cancellation**. The remaining task for CFZP-047 is then a standard eventual polynomial-times-exponential domination problem, not a prime-distribution problem.
