# CFZP-0068 / CFZP-040

## prime-axis finite Abel / prime-counting discrepancy bridge — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-035: exact signed ledger / radial recurrence
- CFZP-036: prime-axis sigma-stripped amplitude = periodic carrier + finite `K/u` remainder
- CFZP-039: eligible prime-axis signed mass = exact leading carrier mass + exact remainder mass; finite remainder debt; exponential carrier transform; finite `Ioc` period-cell support

CFZP-039 は Green-A。current source で特に次が CLOSED:

```text
cfzp039PrimeAxisLeadingCarrierMassOn
cfzp039PrimeAxisRemainderMassOn
cfzp039PrimeAxisRemainderDebtOn
cfzp039PrimeAxisSignedMassOn_eq_leading_add_remainder
cfzp039EligiblePrimeAxisSignedMass_eq_leading_add_remainder
cfzp039PrimeAxisRemainderMassOn_abs_le_debt
cfzp039LeadingCarrierReservoir_implies_radialContactDeficit_le
cfzp039PrimeAxisGrowthExponent
Cfzp039PrimeAxisInteriorStrip
cfzp039ExponentialCarrierPeriodTransform
cfzp039ExponentialCarrierPeriodTransform_exists_pos
cfzp039CarrierCellLeft
cfzp039CarrierCellRight
cfzp039PrimeAxisCarrierCellPairSupport
cfzp039PrimeAxisLeadingCarrierCellMass
cfzp039PrimeAxisRemainderCellDebt
```

**CFZP-040 の目的は、039 の finite prime-axis leading-carrier sum を Mathlib の finite Abel summation に接続し、prime distribution の未知部分を exact な prime-counting discrepancy functional に隔離すること。PNT や asymptotic をまだ仮定せず、actual prime sum = smooth model + discrepancy を finite identity として閉じる。**

重要:

- Good/Bad binary partition へ戻らない。
- prime density / PNT を theorem として仮定しない。
- `π(x)` の近似誤差を隠さず named discrepancy として残す。
- infinite prime sums / summability / limit exchange / RH は本段に入れない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisFiniteAbelPrimeCountingDiscrepancyAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisFiniteAbelPrimeCountingDiscrepancyAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisExactCarrierRemainderSignedMomentAudit
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
```

必要 import は current Mathlib 4.33 API に合わせて最小化してよい。

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — x-axis carrier test function

039 の prime-axis leading term

```text
sigmaWeight(p) * carrier(log p)
```

を real `x > 0` 上の test function として first-class にする。

```lean
noncomputable def cfzp040PrimeAxisCarrierTestFunction
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (x : ℝ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * Real.log x) *
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W (Real.log x)
```

prime specialization:

```text
cfzp040PrimeAxisCarrierTestFunction ε W (p : ℝ)
=
cfzp034PrimeAxisSigmaWeight W p *
  cfzp036PrimeAxisLeadingPeriodicCarrier ε W (log p)
```

を exact に閉じる。

### coordinate carrier derivative

後の Abel discrepancy bound 用に、可能なら coordinate carrier derivative も first-class にする。

```lean
noncomputable def cfzp040LeadingCarrierDerivative
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (W.rectangle.T / ε) *
    (cfzp036LeadingSinCoeffNumerator ε W * Real.cos (W.rectangle.T * u) -
      cfzp036LeadingCosCoeffNumerator ε W * Real.sin (W.rectangle.T * u))
```

`ε ≠ 0` の下で

```text
HasDerivAt (carrier ε W) (cfzp040LeadingCarrierDerivative ε W u) u
```

を閉じる。

さらに `x > 0` で test function derivative:

```text
F'(x)
=
exp (-σ log x) / x *
  (-σ * carrier(log x) + carrierDerivative(log x))
```

を `HasDerivAt` theorem として閉じるのを優先する。

`deriv F x = ...` specialization も便利なら追加する。

---

## 3. Gate B — prime indicator cumulative sum = primeCounting

finite Abel formula の coefficient sequence:

```lean
def cfzp040PrimeIndicator (n : ℕ) : ℝ :=
  if Nat.Prime n then 1 else 0
```

まず exact cumulative theorem:

```lean
theorem cfzp040_sum_primeIndicator_eq_primeCounting (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, cfzp040PrimeIndicator k) =
      (Nat.primeCounting n : ℝ) := by
  ...
```

`Nat.primesLE`, `Nat.primesLE_card_eq_primeCounting` 等 current API を使ってよい。

prime indicator は `0`, `1` で zero であることも simp API として追加してよい。

---

## 4. Gate C — finite real-endpoint prime carrier sum

real endpoints `a b : ℝ` 用に:

```lean
noncomputable def cfzp040PrimeCarrierSumIoc
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
    cfzp040PrimeAxisCarrierTestFunction ε W (k : ℝ) *
      cfzp040PrimeIndicator k
```

`0 ≤ a`, `a ≤ b` と test function の finite-interval differentiability / derivative integrability を供給して、Mathlib

```text
sum_mul_eq_sub_sub_integral_mul
```

へ exact 接続する。

completion target:

```lean
theorem cfzp040PrimeCarrierSumIoc_eq_abel
    {ε a b : ℝ} ... :
    cfzp040PrimeCarrierSumIoc ε W a b =
      cfzp040PrimeAxisCarrierTestFunction ε W b *
          (Nat.primeCounting ⌊b⌋₊ : ℝ) -
      cfzp040PrimeAxisCarrierTestFunction ε W a *
          (Nat.primeCounting ⌊a⌋₊ : ℝ) -
      ∫ t in Set.Ioc a b,
        deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
          (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  ...
```

integral notation / measure syntax は current `AbelSummation` theorem の RHS と exact に合わせる。

ここが本段の第一 main target。

---

## 5. Gate D — period-cell exponential endpoints and raw prime support

039 log-cell:

```text
L_n = cfzp039CarrierCellLeft  W c n
R_n = cfzp039CarrierCellRight W c n
```

から x-axis endpoints:

```lean
noncomputable def cfzp040CarrierCellExpLeft
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (cfzp039CarrierCellLeft W c n)

noncomputable def cfzp040CarrierCellExpRight ... :=
  Real.exp (cfzp039CarrierCellRight W c n)
```

を定義する。

証明:

```text
0 < ExpLeft
ExpLeft < ExpRight
log ExpLeft = CellLeft
log ExpRight = CellRight
```

period positivity だけで閉じる。

raw prime cell support:

```lean
def cfzp040RawPrimeCarrierCellSupport
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Ioc
      ⌊cfzp040CarrierCellExpLeft W c n⌋₊
      ⌊cfzp040CarrierCellExpRight W c n⌋₊).filter Nat.Prime
```

membership を exact に:

```text
p ∈ raw support
↔ Nat.Prime p ∧ CellLeft < log p ∧ log p ≤ CellRight
```

へ落とす。floor / exp / log の端点処理は current Mathlib theorem を使用する。

raw cell leading sum:

```lean
noncomputable def cfzp040RawPrimeCarrierCellMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ cfzp040RawPrimeCarrierCellSupport W c n,
    cfzp034PrimeAxisSigmaWeight W p *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (Real.log (p : ℝ))
```

`cfzp040PrimeCarrierSumIoc` at exponential endpoints と exact equality を閉じる。

---

## 6. Gate E — raw cell ↔ CFZP-039 finite block adapter

039 の cell support は

```text
eligible prime-axis block support ∩ log-cell
```

である。

十分 late な cell では cell 内 prime 全てが eligibility

```text
3 * ε ≤ log p
1 ≤ log p
```

を満たす。

まず coordinate condition:

```text
max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n
```

から raw cell prime `p` の eligibility を証明する theorem を作る。

次に natural block endpoints を

```text
A_n := ⌊ExpLeft⌋₊
B_n := ⌊ExpRight⌋₊
```

としたとき、current `pascalPrimePowerPairSupportUpTo` membership API を使って、prime-axis pair `(p,0)` が block `(A_n,B_n]` に入ることを閉じる。

目標は image equality または sum equality:

```text
cfzp039PrimeAxisLeadingCarrierCellMass ε W c n A_n B_n
=
cfzp040RawPrimeCarrierCellMass ε W c n
```

を late-cell hypothesis の下で証明すること。

pair-finset equality が面倒なら、`Finset.sum_bij` による sum equality でもよい。

**この adapter を単なる仮定で置かないこと。** 既存 finite support membership theorem と floor/log facts から証明する。

---

## 7. Gate F — exact prime-counting discrepancy split

smooth counting model を有限に定義する。

本段では logarithmic integralを新規導入せず、まず elementary model

```lean
noncomputable def cfzp040PrimeCountingSmoothModel (x : ℝ) : ℝ :=
  x / Real.log x
```

を使う。

exact discrepancy:

```lean
noncomputable def cfzp040PrimeCountingDiscrepancy (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ) -
    cfzp040PrimeCountingSmoothModel x
```

当然ながらこれは theorem ではなく定義なので、PNT を仮定していない。

Abel RHS を smooth part と discrepancy part に分ける。

```lean
noncomputable def cfzp040SmoothAbelCarrierModel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  F b * M b - F a * M a -
    ∫ t in Set.Ioc a b, deriv F t * M t

noncomputable def cfzp040PrimeCountingDiscrepancyFunctional
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  F b * Δ b - F a * Δ a -
    ∫ t in Set.Ioc a b, deriv F t * Δ t
```

where `F = cfzp040PrimeAxisCarrierTestFunction ε W`,
`M = cfzp040PrimeCountingSmoothModel`,
`Δ = cfzp040PrimeCountingDiscrepancy`.

completion target:

```text
cfzp040PrimeCarrierSumIoc ε W a b
=
cfzp040SmoothAbelCarrierModel ε W a b
+ cfzp040PrimeCountingDiscrepancyFunctional ε W a b
```

under the same safe Abel hypotheses.

これは algebraic substitution

```text
primeCounting = smoothModel + discrepancy
```

だけで exact に閉じる。

**ここが CFZP-040 の第二 main target。**

---

## 8. Gate G — smooth Abel model -> density integral

`a,b > 1` では

```text
M(x) = x / log x
M'(x) = 1 / log x - 1 / (log x)^2
```

である。

current interval-integral integration-by-parts API で堅く閉じられるなら、

```text
cfzp040SmoothAbelCarrierModel ε W a b
=
∫ t in Set.Ioc a b,
  F t * (1 / log t - 1 / (log t)^2)
```

を exact に証明する。

これにより main density term

```text
F(t) / log t
```

と一段 lower-order correction

```text
-F(t) / (log t)^2
```

が明示される。

この proof が current interval-integral API で長大・fragile になる場合は CFZP-040 Green 条件にはしない。その場合は Gap:

```text
noSmoothAbelModelIntegralReduction
```

を追加する。

ただし Gate C/F の finite Abel / discrepancy exact split は必須。

---

## 9. Gate H — optional log-coordinate density model adapter

Gate G が閉じ、change-of-variables が簡潔なら cell endpoints `a = exp L`, `b = exp R` でさらに

```text
∫ F(t) / log t dt
=
∫ exp (β*u) * carrier(u) / u du
```

および

```text
∫ F(t) / (log t)^2 dt
=
∫ exp (β*u) * carrier(u) / u^2 du
```

を exact に閉じてよい。

ここで

```text
β = cfzp039PrimeAxisGrowthExponent W = 1 - σ
```

を使う。

ただし change-of-variables proof が重い場合、これも CFZP-040 Green 条件にはしない。Gap:

```text
noLogCoordinateDensityIntegralAdapter
```

を残す。

次段で dedicated calculus module として閉じてもよい。

---

## 10. Gate I — discrepancy provider interface

prime distribution の次段 target を型として固定する。

例えば finite interval pointwise provider:

```lean
def Cfzp040PrimeCountingDiscrepancyBoundOn
    (a b D : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b,
    |cfzp040PrimeCountingDiscrepancy x| ≤ D
```

または relative form:

```lean
def Cfzp040PrimeCountingRelativeDiscrepancyBoundOn
    (a b δ : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b,
    |cfzp040PrimeCountingDiscrepancy x| ≤
      δ * cfzp040PrimeCountingSmoothModel x
```

`δ ≥ 0` 等 necessary hypotheses を theorem 側で明示する。

可能なら generic discrepancy-functional envelope:

```text
pointwise |Δ| <= D
→
|DiscrepancyFunctional|
<= D * (|F(a)| + |F(b)| + integral |F'|)
```

を有限積分不等式として閉じる。

ただし PNT から `δ → 0` を供給する theorem は本段では作らない。

---

## 11. Firewall

CFZP-040 では次を禁止する。

- PNT を未証明仮定で theorem 化
- prime-log equidistribution の導入
- infinite prime sums / summability
- limit exchange
- Good/Bad worst-case route への main spine の逆戻り
- `σ < 1` の自動導出
- exceptional / higher-power residual の消去
- CFZP-018 provider
- RH

Mathlib の `AbelSummation` / `PrimeCounting` は finite exact bridge のために使ってよい。

---

## 12. Gap enum

候補:

```lean
inductive Cfzp040PrimeAxisFiniteAbelPrimeCountingDiscrepancyGap : Prop
  | noPrimeCountingDiscrepancyDecayProvider
  | noPrimeCountingRelativeErrorProvider
  | noSmoothAbelModelIntegralReduction
  | noLogCoordinateDensityIntegralAdapter
  | noCarrierCellAsymptoticDominanceProvider
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination
```

Gate G/H が閉じた場合、その Gap constructor は省いてよい。

---

## 13. Roadmap / public import

`DkMath/RH.lean` に公開 import を追加する。

`0000-CFZP-roadmap.md` に CFZP-040 section を追加し、最低限:

```text
x-axis carrier test function and derivative: CLOSED / status
prime indicator cumulative sum = primeCounting: CLOSED
finite Abel prime carrier identity: CLOSED
period-cell exponential endpoint / raw prime support: CLOSED
raw cell <-> CFZP-039 cell adapter: CLOSED
prime-counting smooth/discrepancy exact split: CLOSED
smooth Abel model -> density integral: CLOSED or GAP
log-coordinate density integral adapter: CLOSED or GAP
prime-counting discrepancy decay: OPEN / GAP
carrier-cell asymptotic dominance: OPEN / GAP
exceptional / higher-power residual elimination: OPEN / GAP
```

を明記する。

---

## 14. 完了条件

Green 条件:

1. target module build 成功
2. `lake build DkMath.RH` 成功
3. `git diff --check` 成功
4. 新規 `sorry` / `axiom` / `native_decide` なし
5. finite Abel identity が actual prime indicator / `Nat.primeCounting` と exact に接続
6. actual finite prime carrier sum = smooth Abel model + named discrepancy functional が exact
7. prime distribution theorem を捏造していない
8. raw period-cell sum と CFZP-039 cell mass の finite adapter を実証している
9. optional Gate G/H が閉じない場合は明示 Gap として保持

実装完了後、対象 commit SHA と build 結果を報告すること。
