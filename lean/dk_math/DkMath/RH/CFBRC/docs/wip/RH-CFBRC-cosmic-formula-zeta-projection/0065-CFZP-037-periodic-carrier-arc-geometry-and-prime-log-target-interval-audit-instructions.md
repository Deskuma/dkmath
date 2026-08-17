# CFZP-0065 / CFZP-037

## periodic carrier arc geometry and prime-log target intervals — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-035: actual branch-free event の exact signed-efficiency normalization
- CFZP-036: prime-axis sigma-stripped amplitude = nontrivial periodic carrier + finite `K/u` remainder

CFZP-036 は Green-A。特に current source で次が CLOSED:

```text
cfzp036PrimeAxisCoordinateAmplitude
cfzp035PrimeAxisSignedAmplitude_eq_cfzp036CoordinateAmplitude_log
cfzp036PrimeAxisCoordinateAmplitude_eq_leading_add_remainder
cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair
cfzp036LeadingCoeff_sq_add_sq_pos
cfzp036LeadingCoeff_pair_ne_zero
cfzp036PrimeAxisCarrierPeriod
cfzp036PrimeAxisLeadingPeriodicCarrier_periodic
cfzp036PrimeAxisAmplitudeRemainder_abs_le_constant_div
cfzp036PrimeAxisCoordinateAmplitude_ge_half_of_le_leading
cfzp036PrimeAxisCoordinateAmplitude_le_neg_half_of_le_leading
```

leading carrier は

```text
(S₀ * sin(T*u) + C₀ * cos(T*u)) / ε
```

で、`ε > 0` の下で `(S₀,C₀) ≠ (0,0)` は内部証明済み。period は `P = 2π/T > 0`。

**CFZP-037 の目的は、非零周期 carrier から各周期に同じ幅・同じ margin を持つ positive / negative arc を構成し、large coordinate では `K/u` remainder を吸収して actual prime-axis coordinate amplitude の符号を固定すること。さらにこの log-coordinate arc を real multiplicative interval へ exact に移し、次段の prime arithmetic provider の入力を明示する。**

この段階では prime がその interval に存在することを証明しない。

本段では Bertrand、PNT、Mertens、Dirichlet、prime-log equidistribution、positive density、infinite sums、summability、limit exchange、`σ < 1`、exceptional/higher-power residual elimination、CFZP-018 provider、RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisPeriodicCarrierArcGeometryAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisPeriodicCarrierArcGeometryAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSigmaStrippedPeriodicCarrierAudit
import Mathlib.Tactic
```

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — half-period sign reversal

まず full period だけでなく half period で carrier が符号反転することを exact に閉じる。

候補 theorem:

```lean
theorem cfzp037LeadingCarrier_add_halfPeriod
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W
        (u + cfzp036PrimeAxisCarrierPeriod W / 2) =
      -cfzp036PrimeAxisLeadingPeriodicCarrier ε W u := by
  ...
```

`cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair` と

```text
T * (P/2) = π
sin(x+π) = -sin x
cos(x+π) = -cos x
```

を使う。

これにより positive arc だけ構成すれば negative arc は half-period shift で得られる。

---

## 3. Gate B — explicit positive carrier point

`atan2` / phase-angle 正規化へ行く必要はない。

既存

```lean
cfzp036LeadingCoeff_pair_ne_zero hε W
```

を使い、`S₀` / `C₀` の case split で carrier が strictly positive となる点を一つ explicit に構成する。

推奨:

- `C₀ > 0` なら `u₊ = 0`
- `C₀ < 0` なら `u₊ = π / T`
- `C₀ = 0`, `S₀ > 0` なら `u₊ = π / (2T)`
- `C₀ = 0`, `S₀ < 0` なら `u₊ = 3π / (2T)`

`T = W.rectangle.T > 0`, `ε > 0` なので division は safe。

API は existential でもよい:

```lean
theorem cfzp037_exists_positive_carrier_point
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    ∃ u₊ : ℝ,
      0 < cfzp036PrimeAxisLeadingPeriodicCarrier ε W u₊ := by
  ...
```

half-period reversal から negative point も得る:

```lean
theorem cfzp037_exists_negative_carrier_point ... :
    ∃ u₋ : ℝ,
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W u₋ < 0
```

ここで「非零 carrier だからどこか positive」と一般論だけで済ませず、sin/cos pair と coefficient nontriviality の source fact から閉じること。

---

## 4. Gate C — uniform positive / negative arc data

carrier は continuous。strictly positive point の continuity から、**固定 half-width と固定 positive margin** を持つ arc を一つ取る。

構造体候補:

```lean
structure Cfzp037CarrierPositiveArcData
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) where
  center : ℝ
  halfWidth : ℝ
  margin : ℝ
  hhalfWidth : 0 < halfWidth
  hmargin : 0 < margin
  hcarrier : ∀ u ∈ Set.Icc (center - halfWidth) (center + halfWidth),
    2 * margin ≤ cfzp036PrimeAxisLeadingPeriodicCarrier ε W u
```

negative 側:

```lean
structure Cfzp037CarrierNegativeArcData ... where
  center : ℝ
  halfWidth : ℝ
  margin : ℝ
  hhalfWidth : 0 < halfWidth
  hmargin : 0 < margin
  hcarrier : ∀ u ∈ Set.Icc (center - halfWidth) (center + halfWidth),
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W u ≤ -2 * margin
```

positive data existence を証明し、negative data は half-period shift から同じ width / margin で構築するのを優先。

continuity の neighborhood が open の場合、最初に得た radius の半分を closed `Icc` 用 halfWidth に取ればよい。

margin は center value の `1/4` 等でよい。定数最適化は不要。

---

## 5. Gate D — periodic translation of the arc

period

```lean
P := cfzp036PrimeAxisCarrierPeriod W
```

について natural translate を first-class にする。

```lean
noncomputable def cfzp037PositiveArcLeft
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) : ℝ :=
  arc.center + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W - arc.halfWidth

noncomputable def cfzp037PositiveArcRight ... :=
  arc.center + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W + arc.halfWidth
```

まず periodicity を natural multiple へ延長:

```lean
theorem cfzp037LeadingCarrier_add_nat_mul_period ... :
  carrier (u + (n : ℝ) * P) = carrier u
```

その後、全 `n` で translated arc に同じ carrier margin が成立すること:

```lean
theorem cfzp037_positive_arc_margin_on_translate ...
    (hu : u ∈ Set.Icc (cfzp037PositiveArcLeft arc n)
                       (cfzp037PositiveArcRight arc n)) :
    2 * arc.margin ≤ cfzp036PrimeAxisLeadingPeriodicCarrier ε W u
```

negative arc も同様。

---

## 6. Gate E — finite late-cell threshold absorbing `K/u`

CFZP-036 では

```text
|remainder(u)| <= K / u
```

が `1 ≤ u`, `2ε ≤ u` で CLOSED。

positive arc `arc` に対して explicit finite threshold を定義する。

候補:

```lean
noncomputable def cfzp037RemainderAbsorptionThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (κ : ℝ) : ℝ :=
  max 1 (max (2 * ε)
    (2 * cfzp036PrimeAxisRemainderConstant ε W / κ))
```

`κ > 0` の下で `u ≥ threshold` なら

```text
K / u <= κ / 2
```

を finite algebra で証明する。

さらに `P > 0` なので translated arc の left endpoint は eventually threshold を越える。limit theorem は不要で、Archimedean / `exists_nat_gt` などから finite `N₀` を構成する。

```lean
theorem cfzp037_exists_late_positive_arc_index ... :
  ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
    cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
      cfzp037PositiveArcLeft arc n
```

同様に negative arc も閉じる。

---

## 7. Gate F — late arc gives actual amplitude sign with uniform margin

Gate D/E と CFZP-036 の既存 sign transport:

```lean
cfzp036PrimeAxisCoordinateAmplitude_ge_half_of_le_leading
cfzp036PrimeAxisCoordinateAmplitude_le_neg_half_of_le_leading
```

を使い、late positive arc 全体で

```text
arc.margin <= carrier    -- 2*margin があるので余裕あり
K/u <= arc.margin/2
```

から

```lean
arc.margin / 2 ≤ cfzp036PrimeAxisCoordinateAmplitude ε W u
```

を得る。

実際には `hcarrier` が `2*margin ≤ carrier` なので、transport theorem に `κ := 2*margin` を渡して stronger bound を取ってもよい。Lean が簡潔な方を選ぶ。

negative arc でも uniform negative margin を得る。

重要: この theorem は **prime を仮定しない coordinate-level theorem** として閉じること。解析波形と素数算術を分離する。

---

## 8. Gate G — log arc -> multiplicative real interval

prime arithmetic の入力を明瞭化するため、translated log arc を real exponential interval へ写す。

```lean
noncomputable def cfzp037PositivePrimeIntervalLeft
    (arc : Cfzp037CarrierPositiveArcData ε W) (n : ℕ) : ℝ :=
  Real.exp (cfzp037PositiveArcLeft arc n)

noncomputable def cfzp037PositivePrimeIntervalRight ... :=
  Real.exp (cfzp037PositiveArcRight arc n)
```

fixed multiplicative width factor:

```lean
noncomputable def cfzp037PositiveArcMultiplicativeRatio
    (arc : Cfzp037CarrierPositiveArcData ε W) : ℝ :=
  Real.exp (2 * arc.halfWidth)
```

証明:

```lean
theorem cfzp037PositiveArcMultiplicativeRatio_gt_one ... :
  1 < cfzp037PositiveArcMultiplicativeRatio arc

theorem cfzp037PositivePrimeIntervalRight_eq_ratio_mul_left ... :
  cfzp037PositivePrimeIntervalRight arc n =
    cfzp037PositiveArcMultiplicativeRatio arc *
      cfzp037PositivePrimeIntervalLeft arc n
```

この ratio は `n` に依存しない。

positive real `x` について log/exp membership adapter:

```lean
theorem cfzp037_log_mem_positive_arc_iff_mem_exp_interval
    {x : ℝ} (hx : 0 < x) :
    Real.log x ∈ Set.Icc (cfzp037PositiveArcLeft arc n)
      (cfzp037PositiveArcRight arc n) ↔
    x ∈ Set.Icc (cfzp037PositivePrimeIntervalLeft arc n)
      (cfzp037PositivePrimeIntervalRight arc n)
```

prime `p : ℕ` specialization も作る。

---

## 9. Gate H — prime hit transports to quantitative positive event

ここで初めて prime を戻す。

safe hypotheses:

```text
0 < ε
ε < log 2
Nat.Prime p
late translated positive arc
log p ∈ that arc
```

から 036 coordinate theorem と 035/036 exact prime specialization を使い、

```lean
arc.margin / 2 ≤ cfzp035PrimeAxisSignedAmplitude ε W p
```

または coordinate theorem から直接 amplitude lower bound を得る。

さらに sigma weight positivity を掛けて actual event:

```lean
theorem cfzp037PrimeAxisEvent_ge_sigmaWeight_mul_margin_of_positiveArcHit ... :
  cfzp034PrimeAxisSigmaWeight W p * (arc.margin / 2) ≤
    cfzpPrimePowerBranchFreeTrigEvent ε W p 1
```

従って strict positivity:

```lean
0 < cfzpPrimePowerBranchFreeTrigEvent ε W p 1
```

negative arc についても symmetric theorem を作るとよい:

```text
event(p,1) <= - sigmaWeight(p) * margin/2 < 0
```

ただし prime が各 arc に存在することは本段では証明しない。

---

## 10. Gate I — next arithmetic provider を exact に定義する

この段の最後は theorem ではなく、次段が解くべき arithmetic target を型として固定する。

最低限:

```lean
def Cfzp037PrimeAxisPositiveArcHitAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n p : ℕ) : Prop :=
  Nat.Prime p ∧
  Real.log (p : ℝ) ∈
    Set.Icc (cfzp037PositiveArcLeft arc n)
      (cfzp037PositiveArcRight arc n)
```

さらに必要なら finite weighted hit mass を定義:

```lean
noncomputable def cfzp037PositiveArcPrimeSigmaWeightMass
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S.filter (fun p => Cfzp037PrimeAxisPositiveArcHitAt ε W arc n p),
    cfzp034PrimeAxisSigmaWeight W p
```

ただし **positive density / lower bound / cofinal mass growth は assert しない**。

次の frontier は明示的に:

```text
fixed multiplicative prime intervals
[exp(L_n), exp(R_n)]
with R_n-L_n = 2δ and exp(R_n)/exp(L_n) = exp(2δ) > 1
```

に、どの程度の prime mass が入るか、である。

---

## 11. Firewall / prohibited shortcuts

`Cfzp037PrimeAxisPeriodicCarrierArcGeometryGap` などを置き、少なくとも:

```text
noPrimeInEveryPositiveArcProvider
noPrimeAxisPositiveArcWeightedMassLowerBound
noPrimeLogEquidistributionProvider
noExceptionalHigherPowerResidualElimination
noAutomaticSubcriticalWindowProvider
```

を明示する。

この段で禁止:

```text
Bertrand as an automatic interval-hit theorem
PNT
Mertens
Dirichlet AP theorem
prime reciprocal divergence
positive density
infinite sums
summability
limit exchange
σ < 1 unless an existing source theorem is explicitly imported and used
exceptional/higher-power residual = 0
CFZP-018 provider
RH conclusion
```

特に Bertrand は interval ratio が `> 2` と証明されない限り、この arbitrary fixed multiplicative arc に自動適用できない。存在を仮定・暗黙化しないこと。

---

## 12. Completion target

CFZP-037 は次が CLOSED なら Green:

```text
carrier half-period sign reversal
explicit positive / negative carrier point
uniform positive / negative carrier arc data
natural-period translated arcs
finite late-cell threshold for K/u absorption
late positive/negative arc -> coordinate amplitude uniform sign margin
log arc -> exact multiplicative real interval
fixed interval ratio exp(2δ) > 1
prime hit -> quantitative signed event transport
prime-arc hit predicate / finite arithmetic frontier
```

最終解釈:

```text
analytic waveform problem: CLOSED
prime target interval geometry: CLOSED
prime occupancy / weighted prime mass in those intervals: OPEN / GAP
```

ここまで閉じれば、次段 CFZP-038 は初めて arithmetic side を選択する。
その際も「各 arc に prime が一個ある」だけで signed mass dominance が出るとは扱わない。必要なのは最終的に sigma-weighted signed mass の finite lower bound である。

roadmap の CFZP-037 節も実装事実に合わせて更新すること。