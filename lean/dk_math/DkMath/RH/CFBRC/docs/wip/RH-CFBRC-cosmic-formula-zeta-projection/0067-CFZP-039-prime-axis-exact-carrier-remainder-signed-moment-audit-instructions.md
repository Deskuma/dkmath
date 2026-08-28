# CFZP-0067 / CFZP-039

## prime-axis exact carrier/remainder signed moment — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-035: exact signed efficiency / exact signed block / radial recurrence
- CFZP-036: prime-axis sigma-stripped amplitude = periodic carrier + finite `K/u` remainder
- CFZP-037: periodic positive/negative carrier arcs and prime-log target intervals
- CFZP-038: positive carrier Good/Bad weighted-mass reduction into the exact signed ledger

CFZP-038 は Green-A。current source で特に次が CLOSED:

```text
cfzp038PositiveArcGoodPairSupportAt
cfzp038PositiveArcGoodPairSupport
cfzp038GoodSigmaWeight_credit_le_signedMass
cfzp038SignedMass_ge_neg_referenceMass
cfzp038ExceptionalSignedMass_ge_neg_referenceMass
cfzp038HigherPowerSignedMass_ge_neg_referenceMass
cfzp038PositiveArcEligibleSignedMass_eq_good_add_bad
cfzp038PositiveCarrierExactReservoir_implies_radialContactDeficit_le
cfzp038PositiveCarrierSigmaReservoir_implies_radialContactDeficit_le
cfzp038PositiveCarrierTotalWeightReservoir_implies_radialContactDeficit_le
cfzp038PositiveArcRightSigmaWeight_le_primeWeight
cfzp038_card_mul_rightSigmaWeight_le_goodWeightAt
```

また CFZP-036 では prime-axis actual amplitude の exact 分解が CLOSED:

```text
cfzp035PrimeAxisSignedAmplitude_eq_cfzp036CoordinateAmplitude_log
cfzp036PrimeAxisCoordinateAmplitude_eq_leading_add_remainder
cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair
cfzp036LeadingCoeff_pair_ne_zero
cfzp036PrimeAxisCarrierPeriod
cfzp036PrimeAxisCarrierPeriod_pos
cfzp036PrimeAxisLeadingPeriodicCarrier_periodic
cfzp036PrimeAxisAmplitudeRemainder_abs_le_constant_div
cfzp036PrimeAxisRemainderConstant_pos
```

**CFZP-039 の目的は、CFZP-038 の Good/Bad worst-case reduction を closure の main route にせず、eligible prime-axis の actual signed mass 全体を CFZP-036 の `periodic carrier + K/u remainder` として exact に有限和へ持ち上げること。prime-axis の未知部分を `Bad >= -referenceMass` に潰さず、signed periodic carrier mass と明示的な remainder debt に分離する。さらに、後段の prime-distribution / Abel-summation bridge が狙うべき exponential one-period transform を有限代数として first-class にする。**

CFZP-038 の Good/Bad theorem は正しい finite sufficient criterion として保持する。039 はそれを否定・削除せず、より情報損失の少ない route を追加する。

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite prime sums、summability、limit exchange、automatic `σ < 1`、exceptional/higher-power residual elimination、CFZP-018 provider、RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisExactCarrierRemainderSignedMomentAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisExactCarrierRemainderSignedMomentAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisPositiveCarrierWeightedMassAudit
import Mathlib.Tactic
```

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — exact finite carrier/remainder prime-axis sums

eligible prime-axis pair support 上では `pk.2 = 0`、したがって exponent は `1`。

まず arbitrary finite pair support 用に次を定義する。

```lean
noncomputable def cfzp039PrimeAxisLeadingCarrierMassOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S,
    cfzp034PrimeAxisSigmaWeight W pk.1 *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W
        (Real.log (pk.1 : ℝ))

noncomputable def cfzp039PrimeAxisRemainderMassOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S,
    cfzp034PrimeAxisSigmaWeight W pk.1 *
      cfzp036PrimeAxisAmplitudeRemainder ε W
        (Real.log (pk.1 : ℝ))
```

`S ⊆ cfzp034EligiblePrimeAxisPairBlockSupport ε A B` の下で exact theorem:

```text
cfzp035SignedEfficiencyMassOn ε W S
=
cfzp039PrimeAxisLeadingCarrierMassOn ε W S
+ cfzp039PrimeAxisRemainderMassOn ε W S
```

を閉じる。

per-term proof spine:

1. eligible membership から prime base と `pk.2 = 0` を回収
2. `cfzp035PrimePowerBranchFreeTrigEvent_eq_referenceMass_mul`
3. `cfzp035PrimeAxisEvent_eq_sigmaWeight_mul_signedAmplitude`
4. `cfzp035PrimeAxisSignedAmplitude_eq_cfzp036CoordinateAmplitude_log`
5. eligibility から `1 ≤ log p`, `2 ε ≤ log p` を得て denominator nonzero を閉じる
6. `cfzp036PrimeAxisCoordinateAmplitude_eq_leading_add_remainder`
7. ring / sum distribution

full eligible support specializationも用意する。

重要: ここでは positive arc / Good / Bad を使わない。

---

## 3. Gate B — finite `K / log p` remainder debt

定義:

```lean
noncomputable def cfzp039PrimeAxisRemainderDebtOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S,
    cfzp034PrimeAxisSigmaWeight W pk.1 *
      (cfzp036PrimeAxisRemainderConstant ε W /
        Real.log (pk.1 : ℝ))
```

`S ⊆ eligible`、safe `0 < ε`, `ε < log 2` の下で、少なくとも次を閉じる。

```text
0 <= cfzp039PrimeAxisRemainderDebtOn ε W S

|cfzp039PrimeAxisRemainderMassOn ε W S|
<= cfzp039PrimeAxisRemainderDebtOn ε W S

-cfzp039PrimeAxisRemainderDebtOn ε W S
<= cfzp039PrimeAxisRemainderMassOn ε W S
```

各項は

```text
sigmaWeight(p) > 0
|remainder(log p)| <= K / log p
```

から出す。`cfzp036PrimeAxisAmplitudeRemainder_abs_le_constant_div` に eligibility の

```text
1 <= log p
2 * ε <= log p
```

を渡す。

finite `abs_sum` / `Finset.sum_le_sum` だけで閉じること。infinite sum は導入しない。

---

## 4. Gate C — exact leading-carrier reservoir -> radial endpoint

これが CFZP-039 の main completion target。

eligible prime-axis signed mass は Gate A で

```text
LeadingCarrierMass + RemainderMass
```

に exact 分解され、Gate B で

```text
RemainderMass >= -RemainderDebt
```

となる。

exceptional prime-axis と higher-power は CFZP-038 の named finite debt envelope をそのまま使う。

候補 theorem:

```lean
theorem cfzp039LeadingCarrierReservoir_implies_radialContactDeficit_le
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (hreservoir :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp039PrimeAxisRemainderDebtOn ε W
          (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) +
        cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
        cfzp034HigherPowerReferenceMass ε W A B ≤
      cfzp039PrimeAxisLeadingCarrierMassOn ε W
          (cfzp034EligiblePrimeAxisPairBlockSupport ε A B) + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  ...
```

proof spine:

1. `cfzp035SignedEfficiencyBlock_eq_three_way_split`
2. Gate A eligible exact carrier/remainder split
3. Gate B remainder lower bound
4. `cfzp038ExceptionalSignedMass_ge_neg_referenceMass`
5. `cfzp038HigherPowerSignedMass_ge_neg_referenceMass`
6. `cfzp035SignedEfficiencyBlock_bound_implies_radialContactDeficit_le`

この theorem の prime-axis main termには `Good`, `Bad`, `ReadyThirdQuadrantHit`, `subcritical`, `C_up` を一切要求しない。

---

## 5. Gate D — explicit interior-strip growth exponent

後段の prime-density transport では prime density の `e^u/u` と sigma weight `e^{-σu}` が組み合わさるため、

```text
β := 1 - σ
```

を first-class にする。

```lean
noncomputable def cfzp039PrimeAxisGrowthExponent
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  1 - W.rectangle.σ

def Cfzp039PrimeAxisInteriorStrip
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  W.rectangle.σ < 1
```

**`σ < 1` を自動導出してはいけない。** named hypothesis / predicate のまま保持する。

`hstrip : Cfzp039PrimeAxisInteriorStrip W` の下で:

```text
0 < cfzp039PrimeAxisGrowthExponent W
cfzp039PrimeAxisGrowthExponent W < 1 / 2
```

を閉じる。後者は既存 `cfzp034_rectangleSigma_gt_half` と合わせる。

さらに `P = cfzp036PrimeAxisCarrierPeriod W > 0` より:

```text
0 < exp (β * P) - 1
```

を閉じる。

---

## 6. Gate E — exponential one-period transformed coefficients

CFZP-036 の leading carrier coefficient を

```text
S := cfzp036LeadingSinCoeffNumerator ε W
C := cfzp036LeadingCosCoeffNumerator ε W
T := W.rectangle.T
β := cfzp039PrimeAxisGrowthExponent W
```

と読む。

次を定義する。

```lean
noncomputable def cfzp039ExponentialCarrierSinCoeff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzp039PrimeAxisGrowthExponent W *
      cfzp036LeadingSinCoeffNumerator ε W +
    W.rectangle.T * cfzp036LeadingCosCoeffNumerator ε W

noncomputable def cfzp039ExponentialCarrierCosCoeff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzp039PrimeAxisGrowthExponent W *
      cfzp036LeadingCosCoeffNumerator ε W -
    W.rectangle.T * cfzp036LeadingSinCoeffNumerator ε W
```

これは weighted one-period transform で現れる coefficient pair。

まず finite algebra identities:

```text
β * Sβ - T * Cβ = (β^2 + T^2) * S
T * Sβ + β * Cβ = (β^2 + T^2) * C
```

を証明する。

そこから `0 < ε` と `T > 0`、既存 `cfzp036LeadingCoeff_pair_ne_zero` を使い、

```text
Sβ ≠ 0 ∨ Cβ ≠ 0
```

を閉じる。

この nontriviality 自体には `σ < 1` は本質的に不要。Lean が簡潔なら hstrip を外す。

---

## 7. Gate F — positive exponential period-transform model

scale を定義する。

```lean
noncomputable def cfzp039ExponentialCarrierPeriodScale
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (Real.exp
      (cfzp039PrimeAxisGrowthExponent W *
        cfzp036PrimeAxisCarrierPeriod W) - 1) /
    (ε *
      (cfzp039PrimeAxisGrowthExponent W ^ 2 + W.rectangle.T ^ 2))
```

`0 < ε` と `hstrip` の下で scale strict positive を証明する。

transform:

```lean
noncomputable def cfzp039ExponentialCarrierPeriodTransform
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  cfzp039ExponentialCarrierPeriodScale ε W *
    (cfzp039ExponentialCarrierSinCoeff ε W *
        Real.sin (W.rectangle.T * c) +
      cfzp039ExponentialCarrierCosCoeff ε W *
        Real.cos (W.rectangle.T * c))
```

最低限次を閉じる。

```text
transform(c + P) = transform(c)
transform(c + P/2) = - transform(c)
∃ c, 0 < transform(c)
∃ c, transform(c) < 0
```

positive point は CFZP-037 と同じ `Sβ/Cβ` case split でよい。phase angle / atan2 は不要。

この transform は後段の PNT / Abel bridge が狙う **closed-form model**。Gate G の integral identity を証明しない場合、docstring で「integral」と断定しないこと。

---

## 8. Gate G — optional exact interval-integral identification

Mathlib の current integral API で短く堅く閉じられる場合のみ、次を追加してよい。

```text
∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
  Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)
=
cfzp039ExponentialCarrierPeriodTransform ε W c
```

必要なら appropriate Mathlib integral import を追加する。

ただし、この証明が長大・fragile になる場合は本段の Green 条件にしない。定義した transform を「closed-form transform model」として保持し、次の Gap を追加する:

```text
noIntervalIntegralIdentification
```

**定義で equality を捏造しない。**

---

## 9. Gate H — finite period-cell support interface

後段が prime distribution を接続できるよう、一周期の log cell を有限 support 上に固定する。

例えば:

```lean
noncomputable def cfzp039CarrierCellLeft
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  c + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W

noncomputable def cfzp039CarrierCellRight
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  c + ((n + 1 : ℕ) : ℝ) * cfzp036PrimeAxisCarrierPeriod W
```

eligible prime-axis support を `log p` が cell に属する条件で filter する。

境界 prime の二重計数を避けるため `Ioc` または `Ico` のどちらか一方を一貫して使う。

```text
cfzp039PrimeAxisCarrierCellPairSupport
cfzp039PrimeAxisLeadingCarrierCellMass
cfzp039PrimeAxisRemainderCellDebt
```

を Gate A/B の specialization として作る。

この段では cell 内 prime count / weighted asymptotic を証明しない。

必要なら next-provider predicate を型だけ固定する。例えば「finite cell carrier mass が所定 lower bound を満たす」形でよい。

重要: main route に CFZP-038 Good/Bad positive-arc partition を再導入しない。

---

## 10. Firewall / Gap

本段で禁止:

- Prime Number Theorem の導入・証明
- Mertens / Dirichlet / prime-log equidistribution
- Bertrand だけで arbitrary fixed-ratio cell density が出るという主張
- infinite prime sums / summability / limit exchange
- `W.rectangle.σ < 1` の自動導出
- prime-axis periodic carrier sum の符号を distribution theorem なしで断定
- exceptional prime-axis residual の消去
- higher-power residual の消去
- CFZP-018 provider / RH

Gap 候補:

```lean
inductive Cfzp039PrimeAxisExactCarrierRemainderSignedMomentGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noPrimeAxisCarrierCellDistributionProvider
  | noPrimeAxisCarrierAsymptoticProvider
  | noIntervalIntegralIdentification
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination
```

Gate G を実際に閉じた場合は `noIntervalIntegralIdentification` を削除してよい。

---

## 11. Completion condition

CFZP-039 を Green とする最低条件:

1. eligible prime-axis signed mass = exact leading carrier mass + exact remainder mass
2. finite remainder debt `Σ sigmaWeight * K/log p`
3. `|remainderMass| <= remainderDebt` と lower bound
4. exact leading-carrier reservoir -> radial endpoint
5. named interior-strip predicate `σ < 1` と `β = 1-σ`
6. transformed coefficient pair の nontriviality
7. positive scale を持つ exponential one-period transform model
8. transform の period / half-period sign reversal / positive-negative existence
9. finite period-cell support interface
10. unresolved arithmetic / residual issues are explicit Gap
11. roadmap を次 section として更新
12. `DkMath/RH.lean` 公開 import を追加

Gate G の interval-integral identity は optional。

---

## 12. 数学的意味

CFZP-038 では positive arcs を Good として抽出し、残りを worst-case debt とした。この route は finite theorem として正しいが、closure 用には情報を落とし得る。

CFZP-039 では prime-axis 全体を

```text
actual signed prime-axis mass
= sigma-weighted periodic carrier mass
+ explicit K/log(p) remainder mass
```

のまま保持する。

さらに `σ < 1` を明示的に仮定した interior strip では

```text
prime density scale    ~ exp(u) / u
sigma weight           = exp(-σ u)
combined growth scale  ~ exp((1-σ)u) / u
```

となるため、後段で prime counting / Abel summation を接続する際の自然な growth exponent は `β = 1 - σ > 0` となる。

039 ではこの asymptotic 自体は証明せず、そこへ接続するための exact finite carrier algebra を先に完成させること。
