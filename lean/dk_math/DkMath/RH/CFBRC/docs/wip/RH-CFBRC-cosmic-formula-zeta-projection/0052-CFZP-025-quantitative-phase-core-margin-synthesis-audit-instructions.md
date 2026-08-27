# CFZP-0052 / CFZP-025

## quantitative phase-core margin synthesis audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-006X: negative-frequency profile exact derivative — Green-A
- CFZP-006Y: dimensionless phase-core / centered phase-cell transport — Green-A
- CFZP-023: quantitative prime-power pulse margin — Green-A
- CFZP-024: certified finite block credit/debt dominance — Green-A

CFZP-024 により closure frontier は、finite block の `Good` prime-power pair が certified credit を供給し、`Bad` complement の debt envelope と現在 deficit を支払えるか、という有限定量条件まで圧縮された。

ただし `Good` certificate の主要 field はまだ

```text
Cfzp023CenteredProfileDerivativeDropMargin ε W p j κ
```

すなわち centered frequency interval 全体で

```text
Profile'(u) ≤ -κ
```

という derivative-level hypothesis である。

本段ではこれを、既存 CFZP-006X/Y の exact formula

```text
Profile'(u)
  = exp(-a*u) / u^3 * DerivativeCore(a,T,u)

DerivativeCore(a,T,u)
  = PhaseDerivativeCore(a/T, u*T)
```

から **phase-core quantitative margin** へ分解する。

中心は、safe-frequency prime-power interval `(l,r)` 上で positive prefactor

```text
exp(-a*u) / u^3
```

を right endpoint の explicit positive floor で下から抑え、phase core が

```text
PhaseDerivativeCore(α,θ) ≤ -δ
```

なら

```text
Profile'(u) ≤ -(PrefactorFloor * δ)
```

を得ることである。

さらに 006Y の sign cell を quantitative 化し、third-quadrant 型の explicit bounds

```text
A0 ≤ PhaseDerivativeSinCoeff α θ
sin θ ≤ -s
B0 ≤ 2 * θ * (α*θ + 1)
cos θ ≤ -c
```

から

```text
PhaseDerivativeCore α θ ≤ -(A0*s + B0*c)
```

を finite real algebra として閉じる。

これにより `Good` pair の `κ` は abstract derivative hypothesis ではなく、

```text
κ = PrefactorFloor * PhaseCoreMargin
```

として phase geometry から合成可能になる。

本段では prime-power phase center が自動的に good cell に入ること、good cell の density、equidistribution、cofinal block dominance、RH は証明しない。残すべき frontier は **quantitative phase-cell coverage provider** である。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaQuantitativePhaseCoreMarginSynthesisAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaQuantitativePhaseCoreMarginSynthesisAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaCertifiedBlockCreditDebtDominanceAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit
import Mathlib.Tactic
```

transitive import で十分なら重複 import は減らしてよい。

---

## 2. Gate A — centered derivative prefactor floor

profile derivative の positive prefactor

```text
exp(-a*u) / u^3
```

について、`0 ≤ a`, `0 < l ≤ u ≤ r` のとき right endpoint が lower floor になることを証明する。

概念形:

```text
exp(-a*r) / r^3 ≤ exp(-a*u) / u^3
```

Mathlib の `Real.exp_le_exp`、正数上の `pow` / inverse monotonicity等を使ってよい。

prime-power centered interval に特化した first-class quantityを定義する。

推奨:

```lean
noncomputable def cfzp025CenteredDerivativePrefactorFloor
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  let r := cfzpPrimePowerPhaseMagnitudeRight ε p j
  Real.exp (-(cfzpModePhaseAbscissa W) * r) / r ^ 3
```

safe-frequency regime `0 < ε < log 2`, `p` prime, `0 < j` では

```text
0 < PrefactorFloor
```

を証明する。

また centered interval の任意 `u` について

```text
PrefactorFloor ≤ exp(-a*u)/u^3
```

を public theorem にする。

ここは asymptotic estimate ではなく exact finite interval bound である。

---

## 3. Gate B — quantitative phase-core negative margin

phase-angle interval 全体で core が一定量だけ負である property を first-class にする。

推奨 shape:

```lean
def Cfzp025CenteredPhaseCoreNegativeMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) (δ : ℝ) : Prop :=
  ∀ θ ∈ Set.Ioo
      (cfzpPrimePowerPhaseAngleLeft ε W p j)
      (cfzpPrimePowerPhaseAngleRight ε W p j),
    cfzpPhaseDerivativeCore (cfzpModePhaseAspectRatio W) θ ≤ -δ
```

`δ = 0` は既存 006Y の sign-level phase-core coverage と整合する。

新しい別 phase coordinate は作らない。

---

## 4. Gate C — phase-core margin → frequency derivative-core margin

006Y の exact coordinate theorem

```text
cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
```

および angle/magnitude endpoint identity を使い、

```text
PhaseCore ≤ -δ on centered angle interval
```

から

```text
NegativeFrequencyDerivativeCore ≤ -δ
```

を centered magnitude intervalへ transportする。

目標概念:

```lean
theorem cfzp025DerivativeCore_le_neg_of_phaseCoreMargin
    ...
    (hδ : 0 ≤ δ)
    (hphase : Cfzp025CenteredPhaseCoreNegativeMargin ε W p j δ) :
    ∀ u ∈ Set.Ioo
        (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
        (cfzpPrimePowerPhaseMagnitudeRight ε p j),
      cfzpNegativeFrequencyBoundaryProfileDerivativeCore
        (cfzpModePhaseAbscissa W) W.rectangle.T u ≤ -δ := by
  ...
```

`hδ` が proof 上不要なら theorem hypothesis から外してよい。

---

## 5. Gate D — phase-core margin × prefactor floor → CFZP-023 derivative margin

CFZP-006X の exact derivative

```text
Profile'(u)
  = exp(-a*u)/u^3 * DerivativeCore(a,T,u)
```

を使う。

`0 ≤ δ` と Gate A/C から

```text
Profile'(u)
  ≤ -(PrefactorFloor * δ)
```

を centered interval 全体で証明する。

最重要 adapter:

```lean
theorem cfzp025CenteredProfileDerivativeDropMargin_of_phaseCoreMargin
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hphase : Cfzp025CenteredPhaseCoreNegativeMargin ε W p j δ) :
    Cfzp023CenteredProfileDerivativeDropMargin ε W p j
      (cfzp025CenteredDerivativePrefactorFloor ε W p j * δ) := by
  ...
```

符号には注意すること。

`prefactor ≥ floor ≥ 0` かつ `core ≤ -δ ≤ 0` なので、負数との積により係数比較の向きが反転する箇所がある。`nlinarith` に丸投げせず、必要なら `mul_le_mul_of_nonpos_right` / `mul_le_mul_of_nonneg_left` 等で明示する。

---

## 6. Gate E — phase-core margin → event / pulse quantitative credit

Gate D と CFZP-023 を合成し、one-event credit を phase-core marginだけで記述する。

概念形:

```text
2 * log(p) * CriticalScale(p^j)
  * PrefactorFloor(ε,W,p,j) * δ
≤ Event(p,j)
```

および prime-power von Mangoldt pulse 版を追加する。

`δ > 0` なら prefactor floor は strict positive なので event / pulse の strict positivityも得られる。既存 theorem の単純合成で短く閉じるなら追加してよい。

---

## 7. Gate F — quantitative third-quadrant phase cell

006Y の qualitative theorem

```text
sinCoeff ≥ 0
sin ≤ 0
cos ≤ 0
  -> PhaseDerivativeCore ≤ 0
```

を quantitative 化する。

まず純粋な real algebra theorem として、例えば

```text
0 ≤ A0
0 ≤ B0
0 ≤ s
0 ≤ c
A0 ≤ cfzpPhaseDerivativeSinCoeff α θ
Real.sin θ ≤ -s
B0 ≤ 2 * θ * (α * θ + 1)
Real.cos θ ≤ -c
```

なら

```text
cfzpPhaseDerivativeCore α θ ≤ -(A0 * s + B0 * c)
```

を証明する。

推奨 theorem 名:

```text
cfzp025PhaseDerivativeCore_le_neg_of_quantitativeThirdQuadrantCell
```

`α ≥ 0`, `θ > 0` は coefficient positivityを使う場合だけ要求する。

次に centered angle interval 全体で同じ constants `A0 B0 s c` が成立する coverage property / theoremを作り、

```text
δ = A0*s + B0*c
```

として `Cfzp025CenteredPhaseCoreNegativeMargin` を構成する。

ここで重要なのは **phase-cell membership 自体を証明したことにしない** こと。`sin θ ≤ -s`, `cos θ ≤ -c`, sinCoeff lower bound 等は explicit hypotheses のまま残す。

---

## 8. Gate G — optional explicit cos-coefficient floor

実装が自然なら

```text
B(α,θ) = 2 * θ * (α*θ + 1)
```

について `0 ≤ α`, `0 < θL ≤ θ` から

```text
2 * θL * (α*θL + 1) ≤ B(α,θ)
```

を証明してよい。

これにより quantitative third-quadrant certificate の `B0` を centered angle left endpoint から自動供給できる。

ただしこの補助 gate が Lean friction を増やすなら Green の必須条件にはしない。

`cfzpPhaseDerivativeSinCoeff` の global monotonicityは勝手に主張しない。必要なら別途 explicit lower-bound hypothesis とする。

---

## 9. Gate H — CFZP-024 Good certificate constructor

CFZP-024 の `Good` subset に対し derivative-level `κ` を人手で直接渡す代わりに、pair ごとの phase-core margin `δ pk` から certificate を組み立てられる constructor を作る。

概念入力:

```text
Good ⊆ BlockSupport(A,B)
∀ pk ∈ Good, 0 ≤ δ(pk)
∀ pk ∈ Good, CenteredPhaseCoreNegativeMargin(..., δ(pk))
Bad 側の K / absolute envelope data
```

そして

```text
κ(pk)
  := PrefactorFloor(ε,W,pk.1,pk.2+1) * δ(pk)
```

として

```text
Cfzp024FiniteBlockCertificate ε W A B
```

を構成する。

推奨 theorem/def:

```text
cfzp025FiniteBlockCertificate_of_phaseCoreMargins
```

この constructor により CFZP-024 の Good certificate source が

```text
profile derivative margin
```

から

```text
phase-core margin + explicit positive prefactor floor
```

へ降りる。

Bad 側 envelope は本段では既存 CFZP-023 data のままでよい。無理に phase-core absolute envelopeまで同時に一般化しない。

---

## 10. Gate I — phase-certified finite dominance adapter

Gate H で構成した certificate と CFZP-024 の dominance theorem を合成し、phase-core margin data + Bad envelope + explicit dominance inequalityから

```text
G_B ≤ η
```

へ直接進める adapter を追加してよい。

ただし新しい cofinal providerを仮定なしで導入してはならない。

---

## 11. Gate J — provider firewall

本段で閉じてよいもの:

```text
phase-core negative margin
  -> frequency derivative-core negative margin
  -> profile derivative margin with explicit prefactor floor
  -> event / pulse quantitative credit

quantitative third-quadrant cell bounds
  -> phase-core quantitative margin

finite Good phase-core data
  -> CFZP-024 finite block certificate
```

本段で閉じてはならないもの:

```text
all / eventually / frequently prime powers enter a good phase cell
automatic Good subset density
uniform positive δ over all large prime powers
uniform positive κ over all large prime powers
phase equidistribution / density
cofinal certified block dominance
CFZP-018 provider without explicit hypothesis
joint limit / limit exchange
RH
```

Gap marker例:

```lean
inductive Cfzp025QuantitativePhaseCoreMarginSynthesisGap : Prop
  | noIndependentQuantitativePrimePowerPhaseCellCoverageProvider
```

---

## 12. Public import / roadmap

Green の場合:

1. `DkMath/RH.lean` に新 module を import。
2. `0000-CFZP-roadmap.md` に CFZP-025 section を追加。
3. classification を例えば

```text
centered derivative prefactor floor: CLOSED
phase-core quantitative margin interface: CLOSED
phase-core -> derivative-core transport: CLOSED
phase-core margin -> CFZP-023 derivative margin: CLOSED
phase-core margin -> event/pulse credit: CLOSED
quantitative third-quadrant algebra: CLOSED
phase-core Good-data -> CFZP-024 certificate: CLOSED
independent quantitative phase-cell coverage provider: OPEN / GAP
```

とする。

---

## 13. 実装上の優先順位

最優先は次の spine:

```text
PhaseCore ≤ -δ
  -> DerivativeCore ≤ -δ
  -> Profile' ≤ -(PrefactorFloor*δ)
  -> CFZP023 margin
  -> one-event quantitative credit
  -> CFZP024 Good certificate
```

この spine が閉じれば Green-A としてよい。

quantitative third-quadrant helper は、その spine に自然に接続できる範囲で実装する。

本段は **Good certificate の解析的中身を phase geometry へ露出する段**であり、まだ prime-power phase distribution theorem を要求しない。
