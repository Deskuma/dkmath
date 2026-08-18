# CFZP-0071 / CFZP-043

## smooth weight variation bound / eventual positive cell — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-039: prime-axis leading periodic carrier, exponential one-period transform, positive/negative transform phase
- CFZP-040: finite Abel / prime-counting discrepancy split
- CFZP-041: smooth/discrepancy cell reservoir -> radial endpoint
- CFZP-042: smooth Abel cell = exact transformed carrier main term + slowly-varying log-density weight error

CFZP-042 は Green-A。current source で特に次が CLOSED:

```text
cfzp042PrimeCountingSmoothDensity
cfzp042PrimeCountingSmoothModel_hasDerivAt
cfzp042SmoothAbelCarrierModel_eq_densityIntegral
cfzp042SmoothDensityIntegral_eq_logCellIntegral
cfzp042SmoothLogCellIntegral_eq_translated
cfzp042ExponentialCarrierMoment
cfzp042ExponentialCarrierMoment_eq_transform
cfzp042SmoothWeightVariationError
cfzp042SmoothAbelCell_eq_transform_add_weightError
```

**CFZP-043 の目的は、CFZP-042 で exact に隔離された `weight variation error` を有限一周期上で `O(1/U^2)` に抑え、positive exponential-transform phase では main term `q(U) * Transform(c)` の `O(1/U)` が必ず勝つことを quantitative theorem にすること。**

ここで

```text
β := cfzp039PrimeAxisGrowthExponent W
P := cfzp036PrimeAxisCarrierPeriod W
U := cfzp039CarrierCellLeft W c n
q(u) := cfzp042LogDensityWeight u = 1/u - 1/u^2
M(c) := cfzp039ExponentialCarrierPeriodTransform ε W c
```

と読む。

CFZP-042 の exact identity:

```text
SmoothCell(U)
=
exp(β U) * (q(U) * M(c) + WeightError(U,c))
```

に対して、本段では概念的に

```text
|WeightError(U,c)| <= C(c) / U^2
q(U) >= 1 / (2U)          (U >= 2)
M(c) > 0
```

を閉じる。従って十分大きい `U` では

```text
SmoothCell(U) >= exp(β U) * M(c) / (4U) > 0.
```

**prime-counting discrepancy は本段では触らない。** 041 側の named debt としてそのまま残す。

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite prime sums、summability、limit exchange、automatic `σ < 1`、exceptional/higher-power residual elimination、CFZP-018 provider、RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothWeightVariationEventualPositivityAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisSmoothWeightVariationEventualPositivityAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothDensityLogCoordinateTransformAudit
import Mathlib.Tactic
```

必要なら interval-integral inequality 用 import を追加してよい。

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — log-density weight quantitative facts

`q(u) = 1/u - 1/u^2` の late-coordinate 性質を first-class にする。

最低限次を閉じる。

### A1. positivity / lower bound

```lean
 theorem cfzp043LogDensityWeight_pos
    {u : ℝ} (hu : 1 < u) :
    0 < cfzp042LogDensityWeight u := by
  ...
```

さらに `2 ≤ u` で

```text
1 / (2 * u) <= cfzp042LogDensityWeight u
```

を証明する。

候補:

```lean
theorem cfzp043_half_inv_le_logDensityWeight
    {u : ℝ} (hu : 2 ≤ u) :
    1 / (2 * u) ≤ cfzp042LogDensityWeight u := by
  ...
```

数学的には

```text
q(u) = (u - 1) / u^2
u - 1 >= u/2
```

だけでよい。

### A2. variation bound

最重要 local lemma:

```lean
theorem cfzp043_logDensityWeight_variation_le
    {U t : ℝ} (hU : 2 ≤ U) (ht : 0 ≤ t) :
    |cfzp042LogDensityWeight (U + t) -
        cfzp042LogDensityWeight U| ≤
      t / U^2 := by
  ...
```

これは微分平均値定理でも direct rational algebra でもよい。

**direct algebra を優先してよい。** `U > 0`, `U+t > 0` の下で denominator を払えば、`q` は `u ≥ 2` で単調減少し、差は `t/U^2` 以下に直接落とせる。

MVT を使う場合は

```text
q'(u) = (2-u)/u^3
```

かつ `u ≥ U ≥ 2` で `|q'(u)| ≤ 1/U^2` を使う。

cell period 上の corollary:

```text
0 <= t <= P
--------------------------------
|q(U+t)-q(U)| <= P / U^2
```

も用意する。

---

## 3. Gate B — finite absolute exponential carrier moment

carrier を coefficient sup bound で潰さず、実際の一周期 absolute moment を有限定数として保持する。

```lean
noncomputable def cfzp043ExponentialCarrierAbsMoment
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
    |Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)|
```

最低限:

```text
0 <= cfzp043ExponentialCarrierAbsMoment ε W c
```

を閉じる。

`ε ≠ 0` なら integrand は continuous なので、必要な `IntervalIntegrable` helper も可能なら自動で閉じる。

この finite constant は prime distribution と無関係。

---

## 4. Gate C — weight variation error is `O(1/U^2)`

略記:

```text
P := cfzp036PrimeAxisCarrierPeriod W
U := cfzp039CarrierCellLeft W c n
Aabs := cfzp043ExponentialCarrierAbsMoment ε W c
```

`2 ≤ U` の下で target:

```lean
theorem cfzp043SmoothWeightVariationError_abs_le
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    |cfzp042SmoothWeightVariationError ε W c n| ≤
      (cfzp036PrimeAxisCarrierPeriod W /
          (cfzp039CarrierCellLeft W c n)^2) *
        cfzp043ExponentialCarrierAbsMoment ε W c := by
  ...
```

`P > 0` は既存 `cfzp036PrimeAxisCarrierPeriod_pos W`。

proof spine:

1. `intervalIntegral.abs_integral_le_integral_abs` 相当の current API;
2. Gate A の pointwise variation bound;
3. `0 ≤ t ≤ P` から `t/U^2 ≤ P/U^2`;
4. nonnegative integrand 上の interval integral monotonicity;
5. constant factor を integral 外へ出す。

必要なら RHS を

```text
(P * Aabs) / U^2
```

の normal form にしてもよい。

便利な finite constant:

```lean
noncomputable def cfzp043SmoothWeightVariationConstant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  cfzp036PrimeAxisCarrierPeriod W *
    cfzp043ExponentialCarrierAbsMoment ε W c
```

を定義し、

```text
|WeightError| <= Cvar / U^2
```

を canonical theorem にしてもよい。

---

## 5. Gate D — quantitative smooth-cell lower bound

CFZP-042 の exact decomposition を入力として使う。

実装 API の都合に応じ、以下のどちらかを選んでよい。

### preferred: 042 theorem の finite readiness data を直接受け取る

`cfzp042SmoothAbelCell_eq_transform_add_weightError` に必要な

```text
hcell : SmoothAbelCell = cfzp042SmoothLogCellIntegral ...
hA_int
hE_int
```

を受け取り内部で exact split を得る。

### acceptable: exact split equality を一つの hypothesis として受け取る

```text
hsplit :
  SmoothCell = exp(β U) * (q(U) * M(c) + WeightError)
```

ただしこの場合、042 の theorem からその `hsplit` を得る convenience theorem / specialization を同 module に必ず用意する。

まず general lower bound:

```text
SmoothCell
>=
exp(β U) *
  (q(U) * M(c) - Cvar / U^2)
```

を閉じる。

`exp(...) > 0` なので符号操作は単純。

---

## 6. Gate E — explicit positivity threshold

positive transform phase

```text
hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c
```

を仮定する。

略記:

```text
M := cfzp039ExponentialCarrierPeriodTransform ε W c
C := cfzp043SmoothWeightVariationConstant ε W c
```

threshold を first-class にしてよい。

```lean
noncomputable def cfzp043SmoothPositivityThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  max 2 (4 * cfzp043SmoothWeightVariationConstant ε W c /
    cfzp039ExponentialCarrierPeriodTransform ε W c)
```

`hM` と

```text
cfzp043SmoothPositivityThreshold ε W c <= U
```

の下で

```text
exp(β U) * (M / (4 * U)) <= SmoothCell
```

を target とする。

候補 theorem:

```lean
theorem cfzp043_exp_transform_div_four_le_smoothCell
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp043SmoothPositivityThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (...) :
    Real.exp (cfzp039PrimeAxisGrowthExponent W *
        cfzp039CarrierCellLeft W c n) *
      (cfzp039ExponentialCarrierPeriodTransform ε W c /
        (4 * cfzp039CarrierCellLeft W c n)) ≤
      cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) := by
  ...
```

proof arithmetic:

```text
q(U) >= 1/(2U)
C/U^2 <= M/(4U)       from U >= 4C/M
-------------------------------------
q(U)M - C/U^2 >= M/(4U)
```

さらに strict positivity:

```text
0 < SmoothCell
```

を corollary として閉じる。

**この Gate E が CFZP-043 の主要 completion target。**

---

## 7. Gate F — positive transform phase and cofinal late cells

CFZP-039 には既に

```text
cfzp039ExponentialCarrierPeriodTransform_exists_pos
```

がある。

`0 < ε` と

```text
hstrip : Cfzp039PrimeAxisInteriorStrip W
```

の下で positive phase `c` を選べる。

別に cell-left coordinate の cofinality を finite real arithmetic と Archimedean property だけで閉じる。

```lean
theorem cfzp043_carrierCellLeft_eventually_ge
    (W : PascalCenteredXiResidueTransportWindow)
    (c K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K ≤ cfzp039CarrierCellLeft W c n := by
  ...
```

`P > 0` と

```text
CellLeft(c,n) = c + n*P
```

だけを使う。

そこから

```text
∃ c N,
  0 < Transform(c) ∧
  ∀ n >= N,
    SmoothPositivityThreshold(c) <= CellLeft(c,n)
```

を閉じる。

**SmoothCell positivity そのものを `∀ n >= N` で言う場合、042 exact-split readiness が各 cell に必要ならそれを明示的 premise に残すこと。** readiness を暗黙に仮定しない。

---

## 8. Gate G — optional radial endpoint corollary with explicit smooth margin

041 main theorem の smooth reservoir に Gate E の explicit lower bound を差し込む。

略記:

```text
A := cfzp040CarrierCellNaturalLeft W c n
B := cfzp040CarrierCellNaturalRight W c n
U := cfzp039CarrierCellLeft W c n
M := Transform(c)
SmoothMargin := exp(βU) * M/(4U)
```

仮定:

```text
G_A
+ RemainderDebt_cell
+ ExceptionalDebt
+ HigherPowerDebt
+ D
<= SmoothMargin + η
```

および

- `hD : Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt ... D`
- 041 の finite Abel/discrepancy regularity data
- Gate E の smooth positivity readiness / threshold

から

```text
G_B <= η
```

を閉じる。

これは strongly preferred。証明は Gate E lower bound と
`cfzp041SmoothDiscrepancyCellReservoir_implies_radialContactDeficit_le`
の単純合成である。

---

## 9. Gap / firewall

候補:

```lean
inductive Cfzp043PrimeAxisSmoothWeightVariationEventualPositivityGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothCellAnalyticReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination
```

本段で variation error bound と quantitative smooth positivity を閉じたなら、

```text
noSmoothWeightVariationErrorBound
noEventualSmoothAbelCellPositiveLowerBound
```

は Gap に残さない。

本段では以下を導入しない:

- PNT / Mertens / Dirichlet / Bertrand
- infinite prime sums
- summability / limit exchange
- automatic `σ < 1`
- prime-log equidistribution
- prime-counting discrepancy decay の無条件 claim
- exceptional / higher-power residual elimination
- CFZP-018 provider
- RH

---

## 10. Roadmap

CFZP-043 entry を追加し、最低限:

```text
log-density positivity / 1/(2U) lower bound: CLOSED
log-density one-period variation <= P/U^2: CLOSED
finite exponential carrier absolute moment: CLOSED
weight-variation error <= C/U^2: CLOSED
positive-transform explicit smooth-cell lower bound: CLOSED
positive transform phase + cofinal late cell coordinates: CLOSED
explicit smooth-margin reservoir -> radial endpoint: CLOSED if Gate G completed
automatic smooth-cell analytic readiness: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
exceptional/higher-power residual elimination: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
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
no sorry / new axiom / native_decide
```

Gate G は strongly preferred だが、041 の regularity arguments を大量に再掲するだけになる場合は Green の必須条件にしない。

---

## Strategic target after CFZP-043

CFZP-043 が閉じると smooth side は、positive transform phase `c` と十分 late な cell で

```text
SmoothCell(U) >= exp(β U) * M(c)/(4U) > 0
```

という explicit finite margin を持つ。

その時点で prime-side endpoint の未解決予算は

```text
Prime-counting discrepancy debt
+ K/log(p) remainder debt
+ exceptional prime-axis residual
+ higher-prime-power residual
+ starting radial deficit

must be beaten by

exp(β U) * M(c)/(4U).
```

となる。

つまり 043 後の prime-distribution 問題は、carrier の符号を探す問題ではなく、**既に正である smooth margin に対して discrepancy / residual が相対的に小さいことを示す問題**へ移る。