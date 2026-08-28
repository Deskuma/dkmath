# CFZP-0072 / CFZP-044

## explicit smooth-margin radial budget / late exceptional-axis elimination — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-039: exact leading carrier + `K/log p` remainder; radial reservoir
- CFZP-040: finite Abel / prime-counting discrepancy split
- CFZP-041: smooth/discrepancy cell reservoir -> radial endpoint
- CFZP-042: smooth cell = exponential transform main + weight-variation error
- CFZP-043: `|WeightError| = O(U^-2)` and explicit positive smooth margin `exp(βU) M/(4U)`

CFZP-043 は Green-A。特に current source で:

```text
cfzp043LogDensityWeight_pos
cfzp043_half_inv_le_logDensityWeight
cfzp043_logDensityWeight_variation_le
cfzp043ExponentialCarrierAbsMoment
cfzp043SmoothWeightVariationError_abs_le
cfzp043SmoothPositivityThreshold
cfzp043_exp_transform_div_four_le_smoothCell
cfzp043_smoothCell_pos
cfzp043_carrierCellLeft_eventually_ge
cfzp043_exists_positive_transform_cofinal_cells
```

が CLOSED。

**CFZP-044 の目的は、043 の explicit smooth lower margin を 041 の radial reservoir に正式接続し、同時に sufficiently-late cell では prime-axis exceptional residual が実は空であることを finite support arithmetic だけで消去すること。**

prime-counting discrepancy decay と higher-prime-power residual はまだ解かない。

本段の main budget は概念的に:

```text
G_A
+ RemainderDebt_cell
+ HigherPowerDebt
+ DiscrepancyDebt D
<= ExplicitSmoothMargin + η

ExplicitSmoothMargin
:= exp(β U) * Transform(c) / (4 U)

-----------------------------------------
G_B <= η
```

ここでは late-cell theorem により `ExceptionalPrimeAxisReferenceMass = 0` を exact に使う。

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite prime sums、summability、limit exchange、automatic `σ < 1`、higher-power residual の無条件消去、CFZP-018 provider、global RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisExplicitSmoothMarginRadialBudgetAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisExplicitSmoothMarginRadialBudgetAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothWeightVariationEventualPositivityAudit
import Mathlib.Tactic
```

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — combined late threshold for radial use

043 positivity threshold は `U >= 2` を保証するが、041 / 040 の eligible-cell bridge は

```text
max (3 * ε) 1 <= U
```

も必要とする。

これを一つにまとめる。

```lean
noncomputable def cfzp044RadialLateThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  max (cfzp043SmoothPositivityThreshold ε W c) (max (3 * ε) 1)
```

証明 helper:

```text
RadialLateThreshold <= U
-> SmoothPositivityThreshold <= U

RadialLateThreshold <= U
-> max (3*ε) 1 <= U

RadialLateThreshold <= U
-> 2 <= U
```

最後の `2 <= U` は 043 threshold 内の `max 2 ...` を通して得る。

positive phase と cofinality から:

```lean
∃ c N,
  0 < Transform(c) ∧
  ∀ n >= N, RadialLateThreshold ε W c <= CellLeft W c n
```

も閉じる。

これは prime distribution を一切使わない。

---

## 3. Gate B — late cell has no exceptional prime-axis pair

略記:

```text
A := cfzp040CarrierCellNaturalLeft  W c n
B := cfzp040CarrierCellNaturalRight W c n
U := cfzp039CarrierCellLeft W c n
```

仮定:

```text
hcell : max (3 * ε) 1 <= U
```

の下では `(A,B]` にある prime-axis point `(p,0)` は全て

```text
3 * ε <= log p
1 <= log p
```

を満たす。

040 / 041 の finite adapter を使い、まず:

```lean
theorem cfzp044PrimeAxisBlockSupport_eq_eligible
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 <= cfzp039CarrierCellLeft W c n) :
    cfzp034PrimeAxisPairBlockSupport
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
      cfzp034EligiblePrimeAxisPairBlockSupport ε
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  ...
```

を閉じる。

proof は prime-axis block membership から base prime `p` と natural `Ioc` membership を回収し、

```text
cfzp040RawPrimeCarrierCellSupport_mem_iff
```

または同等の floor/exp/log bridge で

```text
CellLeft < log p <= CellRight
```

へ落とし、`hcell` から eligibility を得る。

そこから:

```lean
theorem cfzp044ExceptionalPrimeAxisPairBlockSupport_eq_empty ... :
    cfzp034ExceptionalPrimeAxisPairBlockSupport ε A B = ∅ := by
  ...
```

さらに canonical mass theorem:

```lean
theorem cfzp044ExceptionalPrimeAxisReferenceMass_eq_zero ... :
    cfzp034ExceptionalPrimeAxisReferenceMass ε W A B = 0 := by
  ...
```

を閉じる。

**これは asymptotic residual elimination ではない。one late cell における exact finite support elimination である。**

この Gate が本段の重要 closure の一つ。

---

## 4. Gate C — compress the purely one-period integrability premises

043 main lower-bound theorem は

```text
hA_int
hE_int
```

を caller premise に残しているが、これらは `ε != 0`, `U >= 2` の下で finite compact interval 上の連続性だけから供給可能。

public helper を追加する。

### carrier integrability

```lean
theorem cfzp044ExponentialCarrier_intervalIntegrable
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    IntervalIntegrable
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t))
      volume 0 (cfzp036PrimeAxisCarrierPeriod W) := by
  ...
```

### variation-error integrability

```lean
theorem cfzp044WeightVariationError_intervalIntegrable
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 <= cfzp039CarrierCellLeft W c n) :
    IntervalIntegrable
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
        (cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n + t) -
          cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n)))
      volume 0 (cfzp036PrimeAxisCarrierPeriod W) := by
  ...
```

043 private proof pattern を再利用してよい。新しい analytic input は不要。

これにより 043 lower bound の convenience wrapper:

```lean
theorem cfzp044_exp_transform_div_four_le_smoothCell
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp043SmoothPositivityThreshold ε W c <=
      cfzp039CarrierCellLeft W c n)
    (hSmoothLog :
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp042SmoothLogCellIntegral ε W c n) :
    cfzp044ExplicitSmoothMargin ε W c n <=
      cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) := by
  ...
```

を Gate D の margin definition 後に置いてよい。

---

## 5. Gate D — explicit smooth margin as first-class object

```lean
noncomputable def cfzp044ExplicitSmoothMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (cfzp039PrimeAxisGrowthExponent W *
      cfzp039CarrierCellLeft W c n) *
    (cfzp039ExponentialCarrierPeriodTransform ε W c /
      (4 * cfzp039CarrierCellLeft W c n))
```

positive transform + radial-late hypothesis から:

```text
0 < cfzp044ExplicitSmoothMargin ε W c n
```

を閉じる。

そして Gate C helper を使って:

```text
cfzp044ExplicitSmoothMargin <= SmoothAbelCell
```

を `hSmoothLog` だけを外部 bridge premise として残す形に圧縮する。

**`hSmoothLog` 自体をこの段で自動化することは strongly preferred だが必須ではない。**

もし 042 の integration-by-parts / substitution readiness を elementary continuity だけで短く自動供給できるなら:

```text
cfzp044SmoothAbelCell_eq_logCell_of_radialLate
```

のような theorem を追加して `hSmoothLog` も消してよい。

長大・fragile になる場合は Gap に残す。

---

## 6. Gate E — finite explicit-margin budget predicate

one-cell radial budget を first-class にする。

```lean
def Cfzp044ExplicitSmoothMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp039PrimeAxisRemainderCellDebt ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) +
    cfzp034HigherPowerReferenceMass ε W
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) + D <=
    cfzp044ExplicitSmoothMargin ε W c n + η
```

**Exceptional prime-axis term は Gate B により late cell では zero なので、この canonical budget には含めない。**

ここで `D` は 041 の discrepancy-functional bound 用 finite debt。

---

## 7. Gate F — main explicit smooth-margin reservoir -> radial endpoint

これが CFZP-044 の main completion target。

仮定:

```text
0 < ε
ε < log 2
hM : 0 < Transform(c)
hLate : RadialLateThreshold ε W c <= U
hSmoothLog : SmoothAbelCell = SmoothLogCell
hD : Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt ε W c n D
041 finite Abel/discrepancy regularity data
hbudget : Cfzp044ExplicitSmoothMarginBudgetAt ε η D W c n
```

結論:

```lean
theorem cfzp044ExplicitSmoothMarginBudget_implies_radialContactDeficit_le
    ... :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) <= η := by
  ...
```

proof spine:

1. Gate A から `SmoothPositivityThreshold <= U` と `max (3ε) 1 <= U`。
2. Gate D から `ExplicitSmoothMargin <= SmoothAbelCell`。
3. Gate B から `ExceptionalPrimeAxisReferenceMass = 0`。
4. `hbudget` を 041 が要求する smooth-reservoir inequality へ変形。
5. `cfzp041SmoothDiscrepancyCellReservoir_implies_radialContactDeficit_le`。

この theorem は PNT や discrepancy decay を使わない。`D` は caller-supplied finite bound のまま。

この Gate により CFZP-043 の optional Gate G を正式に CLOSED とする。

---

## 8. Gate G — cofinal explicit-margin budget interface

043 + Gate A から positive phase `c` と arbitrarily late cell coordinates は deterministic に得られる。

この事実と Gate F を繋ぎやすくするため、provider interface を一つ作ってよい。

候補:

```lean
def Cfzp044CofinalExplicitSmoothMarginBudget
    (ε η : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N <= n ∧
    ∃ D : ℝ,
      Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt ε W c n D ∧
      Cfzp044ExplicitSmoothMarginBudgetAt ε η D W c n
```

ただし regularity/readiness を predicate に含める場合は named structure/predicate に分けてもよい。

この Gate は interface only。provider を無条件に証明しない。

---

## 9. Higher-power residual: inspect, do not smuggle

`cfzp034HigherPowerReferenceMass` は本段では原則 named finite debt のまま残す。

ただし current support API だけで短く次が言える場合:

```text
higher-power coordinate in (A,B]
-> base prime <= sqrt(B)  または同等の finite coordinate restriction
```

のような deterministic support lemma を追加してよい。

**prime-counting theoremを使わずに higher-power mass の消去・negligibility を主張しない。**

この residual の quantitative reduction は次段候補。

---

## 10. Gap / firewall

候補:

```lean
inductive Cfzp044PrimeAxisExplicitSmoothMarginRadialBudgetGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothAbelLogCellReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noHigherPrimePowerResidualDomination
  | noCofinalExplicitMarginBudgetProvider
```

Gate D で `hSmoothLog` まで自動化できた場合は

```text
noAutomaticSmoothAbelLogCellReadinessProvider
```

を削除してよい。

**`noExceptionalPrimeAxisResidualElimination` は Gate B が閉じたなら残さない。**

本段では以下を導入しない:

- PNT / Mertens / Dirichlet / Bertrand
- infinite prime sums
- summability / limit exchange
- prime-log equidistribution
- automatic `σ < 1`
- discrepancy decay の無条件 claim
- higher-power residual の無条件 elimination
- CFZP-018 provider
- global RH

---

## 11. Roadmap

CFZP-044 entry を追加し、最低限:

```text
combined radial-late threshold: CLOSED
late prime-axis block = eligible prime-axis block: CLOSED
late exceptional prime-axis support/mass = 0: CLOSED
finite one-period carrier/error integrability compression: CLOSED
explicit smooth margin first-class and <= SmoothAbelCell: CLOSED
explicit smooth-margin budget -> radial endpoint: CLOSED
positive phase + cofinal radial-late cells: CLOSED
prime-counting discrepancy decay: OPEN / GAP
higher-prime-power residual domination: OPEN / GAP
cofinal explicit-margin budget provider: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

`hSmoothLog` readiness を自動化しなかった場合:

```text
automatic SmoothAbel -> SmoothLogCell readiness: OPEN / GAP
```

も記録する。

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

Gate G は interface only なので provider proof は不要。

---

## Strategic target after CFZP-044

044 が閉じると、one late positive-phase cell の endpoint budget は:

```text
starting radial deficit
+ K/log(p) prime-axis remainder debt
+ higher-prime-power residual
+ prime-counting discrepancy functional debt

must be beaten by

exp(β U) * Transform(c)/(4U).
```

となり、prime-axis exceptional residual は消える。

次の deterministic 候補は higher-prime-power residual。prime powers `p^j`, `j >= 2` は prime-axis points より疎であり、support geometry だけでどこまで explicit に圧縮できるかを先に調べる。

それが閉じれば、残る本丸は prime-counting discrepancy functional と starting radial deficit の budget comparison になる。