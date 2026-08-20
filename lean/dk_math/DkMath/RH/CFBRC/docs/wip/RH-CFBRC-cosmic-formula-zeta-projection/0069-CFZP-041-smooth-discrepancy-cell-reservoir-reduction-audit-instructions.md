# CFZP-0069 / CFZP-041

## prime-axis smooth/discrepancy cell reservoir reduction — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-039: eligible prime-axis signed mass = exact leading carrier + exact remainder; finite remainder debt; radial reservoir
- CFZP-040: finite Abel prime carrier identity; raw prime cell -> CFZP-039 carrier cell; smooth model + named prime-counting discrepancy exact split

CFZP-040 は correction 0068A を含め Green-A。current source で特に次が CLOSED:

```text
cfzp040PrimeCarrierSumIoc_eq_abel
cfzp040PrimeCarrierSumIoc_cellEndpoints_eq_rawCellMass
cfzp040RawPrimeCarrierCellMass_eq_cfzp039CellMass
cfzp040PrimeCarrierSumIoc_cellEndpoints_eq_cfzp039CellMass
cfzp040PrimeCarrierCellAbel_eq_cfzp039CellMass
cfzp040PrimeCarrierSumIoc_eq_smooth_add_discrepancy
cfzp040PrimeCountingDiscrepancyFunctional
Cfzp040PrimeCountingDiscrepancyBoundOn
Cfzp040PrimeCountingRelativeDiscrepancyBoundOn
```

**CFZP-041 の目的は、CFZP-040 の `smooth Abel model + prime-counting discrepancy functional` を CFZP-039 の one-cell leading carrier mass と radial reservoir に直接接続すること。PNT をまだ証明・仮定せず、残る prime-distribution 入力を「smooth cell main term を上回れない finite discrepancy debt」として明示する。**

本段の main closure shape:

```text
CellCarrierMass = SmoothCell + DiscrepancyCell
DiscrepancyCell >= -D

G_A
+ RemainderDebt_cell
+ ExceptionalDebt
+ HigherPowerDebt
+ D
<= SmoothCell + η

--------------------------------
G_B <= η
```

ここで `A,B` は一つの exponential carrier cell の natural floor endpoints。

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite prime sums、summability、limit exchange、automatic `σ < 1`、exceptional/higher-power residual elimination、CFZP-018 provider、RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothDiscrepancyCellReservoirAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisSmoothDiscrepancyCellReservoirAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisFiniteAbelPrimeCountingDiscrepancyAudit
import Mathlib.Tactic
```

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — natural cell block is ordered

略記:

```text
A_n := cfzp040CarrierCellNaturalLeft W c n
B_n := cfzp040CarrierCellNaturalRight W c n
```

`ExpLeft < ExpRight` と floor monotonicity から

```lean
theorem cfzp041CarrierCellNaturalLeft_le_right
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp040CarrierCellNaturalLeft W c n ≤
      cfzp040CarrierCellNaturalRight W c n := by
  ...
```

を閉じる。

これは後の 039 reservoir に渡す `hAB`。

---

## 3. Gate B — full eligible axis block = one carrier-cell support

一周期の natural block `(A_n,B_n]` は、定義上 exactly exponential cell `(exp L_n, exp R_n]` に対応する。

従って prime-axis eligible block 全体について、cell filter は冗長であることを finite に証明する。

目標:

```lean
theorem cfzp041EligiblePrimeAxisBlockSupport_eq_carrierCellSupport
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp034EligiblePrimeAxisPairBlockSupport ε
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
      cfzp039PrimeAxisCarrierCellPairSupport ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  ...
```

proof direction:

- `cell support ⊆ eligible` は既存 `cfzp039PrimeAxisCarrierCellPairSupport_subset_eligible`。
- `eligible ⊆ cell support` は pair block membership から `(A_n,B_n]` の prime base coordinate を回収し、floor/exp/log で
  `CellLeft < log p ∧ log p ≤ CellRight` を示す。
- prime-axis support 内の `pk.2 = 0` を必要に応じて使う。

**この theorem は prime distribution を使わない。**

この exact support equality から convenience theorem:

```text
cfzp041EligibleLeadingCarrierMass_eq_cellMass
cfzp041EligibleRemainderDebt_eq_cellDebt
```

を閉じる。

すなわち cell endpoints block では 039 global reservoir の eligible main/debt を cell API だけで書けるようにする。

---

## 4. Gate C — CFZP-039 cell mass = smooth cell + discrepancy cell

endpoints:

```text
a := cfzp040CarrierCellExpLeft W c n
b := cfzp040CarrierCellExpRight W c n
```

十分 late な cell:

```text
hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n
```

と CFZP-040 の Abel/split に必要な finite analytic hypotheses を受け取り、

```lean
theorem cfzp041CellMass_eq_smooth_add_discrepancy
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n)
    (hf_diff : ...)
    (hf_int : ...)
    (hM_int : ...)
    (hD_int : ...) :
    cfzp039PrimeAxisLeadingCarrierCellMass ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) +
        cfzp040PrimeCountingDiscrepancyFunctional ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) := by
  ...
```

proof:

1. `cfzp040PrimeCarrierSumIoc_eq_smooth_add_discrepancy`
2. `cfzp040PrimeCarrierSumIoc_cellEndpoints_eq_cfzp039CellMass`
3. rewrite only

ここで PNT は不要。

もし `hf_diff`, `hf_int`, `hM_int`, `hD_int` を cell positivity から current Mathlib API で短く自動供給できるなら helper theorem を追加してよい。ただし長大化するなら本段 Green 条件にしない。

---

## 5. Gate D — discrepancy functional debt

まず exact functional そのものの absolute debt を first-class にする。

```lean
noncomputable def cfzp041PrimeCountingDiscrepancyCellDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  |cfzp040PrimeCountingDiscrepancyFunctional ε W
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)|
```

証明:

```text
0 <= CellDiscrepancyDebt
-CellDiscrepancyDebt <= DiscrepancyFunctional(cell)
```

さらに external arithmetic provider が直接 finite bound `D` を渡せる predicate:

```lean
def Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) (D : ℝ) : Prop :=
  |cfzp040PrimeCountingDiscrepancyFunctional ε W
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)| ≤ D
```

を定義する。

そこから

```text
-D <= discrepancy functional(cell)
```

を閉じる。

---

## 6. Gate E — smooth-minus-discrepancy lower bound for actual carrier cell

Gate C + Gate D から:

```lean
theorem cfzp041SmoothSubDiscrepancy_le_cellMass
    ...
    (hD : Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt ε W c n D) :
    cfzp040SmoothAbelCarrierModel ε W ExpLeft ExpRight - D ≤
      cfzp039PrimeAxisLeadingCarrierCellMass ε W c n A_n B_n := by
  ...
```

を閉じる。

これは次段以降の prime-distribution theorem が最終的に使われる唯一の形に近い。

---

## 7. Gate F — main cell smooth/discrepancy reservoir -> radial endpoint

これが CFZP-041 の main completion target。

仮定:

```text
0 < ε
ε < log 2
hcell : max (3 ε) 1 <= CellLeft
finite Abel/split regularity hypotheses
hD : |DiscrepancyFunctional(cell)| <= D
```

および reservoir:

```text
G_A
+ cfzp039PrimeAxisRemainderCellDebt ε W c n A B
+ cfzp034ExceptionalPrimeAxisReferenceMass ε W A B
+ cfzp034HigherPowerReferenceMass ε W A B
+ D
<= cfzp040SmoothAbelCarrierModel ε W ExpLeft ExpRight + η
```

なら:

```lean
theorem cfzp041SmoothDiscrepancyCellReservoir_implies_radialContactDeficit_le
    {ε η D : ℝ} ... :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  ...
```

proof spine:

1. Gate A: `A ≤ B`
2. Gate B: eligible leading mass = cell leading mass
3. Gate B: eligible remainder debt = cell remainder debt
4. Gate E: `Smooth - D ≤ cell leading mass`
5. rearrange reservoir into CFZP-039 main reservoir hypothesis
6. `cfzp039LeadingCarrierReservoir_implies_radialContactDeficit_le`

この theorem に PNT / asymptotic / `σ < 1` は不要。

---

## 8. Gate G — optional pointwise discrepancy -> functional discrepancy adapter

CFZP-040 には既に

```text
Cfzp040PrimeCountingDiscrepancyBoundOn a b D
Cfzp040PrimeCountingRelativeDiscrepancyBoundOn a b δ
```

がある。

current Mathlib integral inequality API で短く閉じられるなら、pointwise bound から functional bound を出す finite theorem を追加する。

absolute variant の自然な envelope:

```text
V_F(a,b)
:= |F(b)| + |F(a)| + ∫ x in Ioc a b, |F'(x)|
```

に対して

```text
|Δπ(x)| <= D on [a,b]
--------------------------------
|DiscrepancyFunctional(a,b)| <= D * V_F(a,b)
```

を目標にする。

候補 definition:

```lean
noncomputable def cfzp041CarrierVariationEnvelope ... : ℝ :=
  |F b| + |F a| + ∫ x in Set.Ioc a b, |deriv F x|
```

必要な integrability / `0 ≤ D` を明示的 hypothesis にしてよい。

**この Gate G は strongly preferred だが、current interval-integral API で証明が長大・fragile になる場合は CFZP-041 Green 条件から外してよい。** その場合 Gap に明示する。

relative discrepancy variant はさらに後段でもよい。

---

## 9. Gap / firewall

候補:

```lean
inductive Cfzp041PrimeAxisSmoothDiscrepancyCellReservoirGap : Prop
  | noSmoothAbelCellPositiveLowerBound
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noSmoothAbelDensityIntegralReduction
  | noLogCoordinateDensityIntegralAdapter
  | noCarrierCellAsymptoticDominanceProvider
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination
```

Gate G を閉じた場合は `noPointwiseDiscrepancyToFunctionalBound` を削除してよい。

本段では以下を導入しない:

- PNT / Mertens / Dirichlet / Bertrand
- infinite prime sums
- summability / limit exchange
- automatic `σ < 1`
- prime-log equidistribution
- smooth model の無条件 positive claim
- discrepancy decay の無条件 claim
- exceptional / higher-power residual elimination
- CFZP-018 provider
- RH

---

## 10. Roadmap

CFZP-041 entry を追加し、最低限:

```text
cell natural block order: CLOSED
eligible axis block = carrier-cell support: CLOSED
CFZP-039 cell mass = smooth Abel + discrepancy: CLOSED
functional discrepancy debt: CLOSED
smooth - discrepancy <= actual carrier cell: CLOSED
smooth/discrepancy cell reservoir -> radial endpoint: CLOSED
smooth Abel positive cell lower bound: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
smooth density/log-coordinate reduction: OPEN / GAP
exceptional/higher-power residual elimination: OPEN / GAP
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
no new sorry / axiom / native_decide
```

Gate G は閉じれば非常に有用だが optional。
