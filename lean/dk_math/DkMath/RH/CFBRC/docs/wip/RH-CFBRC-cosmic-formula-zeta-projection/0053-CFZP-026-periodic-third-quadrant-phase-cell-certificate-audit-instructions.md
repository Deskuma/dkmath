# CFZP-0053 / CFZP-026

## periodic third-quadrant phase-cell certificate audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-006Y: dimensionless phase-core / qualitative phase-cell transport — Green-A
- CFZP-023: quantitative prime-power pulse margin — Green-A
- CFZP-024: certified finite block credit/debt dominance — Green-A
- CFZP-025: quantitative phase-core margin synthesis — Green-A

CFZP-025 により Good pair の derivative-level margin は

```text
PhaseCore ≤ -δ
  -> Profile' ≤ -(PrefactorFloor * δ)
  -> event / pulse quantitative credit
  -> CFZP-024 Good certificate
```

へ分解された。

残る Good-side hypothesis は centered phase-angle interval 全体に対する

```text
PhaseDerivativeCore(α, θ) ≤ -δ
```

である。

本段ではこれをさらに、**周期的な第三象限 interior cell への有限包含**から構成する。

prime-power centered angle は

```text
center = W.rectangle.T * (j * log p)
halfWidth = W.rectangle.T * ε
left  = center - halfWidth
right = center + halfWidth
```

である。

整数 cell index `k : ℕ` と interior margin `τ` に対し、第三象限の安全セルを

```text
ThirdQuadrantLeft(k,τ)  = π + 2πk + τ
ThirdQuadrantRight(k,τ) = 3π/2 + 2πk - τ
```

とする。

`0 < τ ≤ π/4` の下で centered interval がこの cell に含まれるなら、区間全体で

```text
sin θ ≤ -sin τ
cos θ ≤ -sin τ
```

を得る。

さらに `α = cfzpModePhaseAspectRatio W` に対し `0 ≤ α ≤ 1` を明示仮定し、cell の lower/upper endpoint `L,R` から

```text
A0 = L^2 * (1 - α^2) - 2 * (α * R + 1)
B0 = 2 * L * (α * L + 1)
```

を定義する。

`0 ≤ A0` なら、cell 内の任意 `θ` について

```text
A0 ≤ PhaseDerivativeSinCoeff α θ
B0 ≤ 2 * θ * (α*θ + 1)
```

となるため、CFZP-025 の quantitative third-quadrant algebraから

```text
PhaseDerivativeCore α θ
  ≤ -(A0 * sin τ + B0 * sin τ)
```

を得る。

つまり

```text
δ = (A0 + B0) * sin τ
```

型の explicit phase-core margin が cell containment から構成される。

最終的には prime-power Good 条件を

```text
π + 2πk + τ + halfWidth
  ≤ W.rectangle.T * (j * log p)

W.rectangle.T * (j * log p) + halfWidth
  ≤ 3π/2 + 2πk - τ
```

という有限な phase arithmetic へ落とす。

本段では、そのような `k` が cofinally 存在すること、prime-power phase の density / equidistribution、automatic block dominance、RH は証明しない。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPeriodicThirdQuadrantPhaseCellCertificateAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPeriodicThirdQuadrantPhaseCellCertificateAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaQuantitativePhaseCoreMarginSynthesisAudit
import Mathlib.Tactic
```

trigonometric monotonicity lemma が別 import を要求する場合のみ追加する。

---

## 2. Gate A — periodic third-quadrant interior cell

第三象限 cell endpoint を first-class にする。

推奨 shape:

```lean
noncomputable def cfzp026ThirdQuadrantCellLeft (k : ℕ) (τ : ℝ) : ℝ :=
  Real.pi + 2 * Real.pi * k + τ

noncomputable def cfzp026ThirdQuadrantCellRight (k : ℕ) (τ : ℝ) : ℝ :=
  3 * Real.pi / 2 + 2 * Real.pi * k - τ
```

cast / ring normal form は Lean が扱いやすい形へ調整してよい。

`0 ≤ τ`, `τ ≤ π/4` から

```text
CellLeft ≤ CellRight
```

を証明する。

`0 < τ` 版なら strict `<` でもよい。

新しい phase coordinate は作らない。

---

## 3. Gate B — quantitative trigonometric interior margin

`0 ≤ τ ≤ π/4` かつ

```text
θ ∈ Icc (CellLeft k τ) (CellRight k τ)
```

から

```text
Real.sin θ ≤ -Real.sin τ
Real.cos θ ≤ -Real.sin τ
```

を証明する。

周期 `2πk` を除いた後、基本区間

```text
π + τ ≤ θ0 ≤ 3π/2 - τ
```

へ還元する。

Mathlib の既存 `sin` / `cos` periodicity と monotonicity theorem を検索して使うこと。lemma 名を推測して固定しない。

`τ ≤ π/4` により basic cell の右側でも `cos τ ≥ sin τ` を使える。

この Gate は phase arithmetic の前に必要な純粋 trig geometry であり、数値近似や `native_decide` を使わない。

もし `sin τ` 一本への統一が Mathlib proof ergonomics 上かなり重い場合は、まず

```text
sin θ ≤ -sτ
cos θ ≤ -cτ
```

という explicit positive quantities `sτ`,`cτ` を basic trig functions から定義し、最終的に nonnegative/positive lower margin が得られる形でもよい。ただし単なる仮定へ戻してはならず、cell membership から trig bound を theorem として供給すること。

---

## 4. Gate C — prime-power centered interval containment

prime-power pair `(p,j)` が cell `k,τ` に入る property を first-class にする。

推奨:

```lean
def Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : Prop :=
  cfzp026ThirdQuadrantCellLeft k τ ≤
      cfzpPrimePowerPhaseAngleLeft ε W p j ∧
    cfzpPrimePowerPhaseAngleRight ε W p j ≤
      cfzp026ThirdQuadrantCellRight k τ
```

containment から centered angle interval 内の任意 `θ` が cell に入る theorem を作る。

既存

```text
cfzpPrimePowerCenteredAngle_Icc_subset_of_cell_bounds
```

が使えるなら再利用する。

---

## 5. Gate D — containment の center arithmetic 表示

cell containment を angle center / half-width で書き換える。

概念形:

```text
CellLeft + halfWidth ≤ PhaseAngleCenter
PhaseAngleCenter + halfWidth ≤ CellRight
```

さらに既存 theorem

```text
cfzpPrimePowerPhaseAngle_center_eq_T_mul_primePowerCenter
```

を使い、

```text
CellLeft + W.rectangle.T*ε
  ≤ W.rectangle.T * ((j:ℝ) * log p)

W.rectangle.T * ((j:ℝ) * log p) + W.rectangle.T*ε
  ≤ CellRight
```

へ落とす。

この equivalence / adapter は重要。次段で prime-power arithmetic を直接攻める入口になる。

---

## 6. Gate E — phase coefficient floors on a cell

`α : ℝ`, `L R θ : ℝ` について

```text
0 ≤ α
α ≤ 1
0 ≤ L
L ≤ θ
θ ≤ R
```

の下で、

```lean
noncomputable def cfzp026PhaseSinCoeffFloor (α L R : ℝ) : ℝ :=
  L^2 * (1 - α^2) - 2 * (α*R + 1)

noncomputable def cfzp026PhaseCosCoeffFloor (α L : ℝ) : ℝ :=
  2 * L * (α*L + 1)
```

を定義し、

```text
PhaseSinCoeffFloor α L R ≤ cfzpPhaseDerivativeSinCoeff α θ
PhaseCosCoeffFloor α L ≤ 2*θ*(α*θ+1)
```

を pure real algebra で証明する。

第一式では `1 - α^2 ≥ 0`、`θ^2 ≥ L^2`、`α*θ ≤ α*R` を使う。

第二式は `α ≥ 0`, `L ≥ 0`, `L ≤ θ` から閉じる。

---

## 7. Gate F — explicit phase-core margin from cell containment

`α := cfzpModePhaseAspectRatio W` とする。

必要な仮定は明示する:

```text
α ≤ 1
0 < τ
τ ≤ π/4
0 ≤ A0
cell containment
```

`α > 0` は既存 `cfzpModePhaseAspectRatio_pos W` を使う。

`L = CellLeft k τ`, `R = CellRight k τ`、

```text
A0 = cfzp026PhaseSinCoeffFloor α L R
B0 = cfzp026PhaseCosCoeffFloor α L
s = Real.sin τ
δ = A0*s + B0*s
```

とする。

cell 内で trig margins と coefficient floors を組み合わせ、CFZP-025

```text
cfzp025PhaseDerivativeCore_le_neg_of_quantitativeThirdQuadrantCell
```

を使って

```text
Cfzp025CenteredPhaseCoreNegativeMargin ε W p j δ
```

を構成する。

`0 < τ ≤ π/4` から `0 < sin τ`、`B0 > 0` が取れるなら

```text
0 < δ
```

も公開する。proof が過度に膨らむ場合でも `0 ≤ δ` は必須、strict positivity は強く推奨。

---

## 8. Gate G — direct event / pulse quantitative credit

Gate F の cell certificate を CFZP-025 へ直接流し、

```text
cell containment + coefficient-floor condition
  -> explicit event lower bound
```

を first-class theorem にする。

概念形:

```text
2 * log(p) * CriticalScale(p^j) *
  (PrefactorFloor * δ)
≤ Event(p,j)
```

同じものを von Mangoldt pulse に transportする adapter も追加する。

ここでは新しい credit formula を再定義せず、CFZP-025 の theorem を再利用する。

---

## 9. Gate H — CFZP-024 certificate constructor from periodic cell hits

Good pair ごとに

```text
k : (ℕ × ℕ) → ℕ
τ : (ℕ × ℕ) → ℝ
```

または proof ergonomics がよければ共通 `τ` と pair ごとの `k` を与える。

各 Good pair に対し

```text
0 < τ pk
τ pk ≤ π/4
aspectRatio ≤ 1
0 ≤ A0(pk)
Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell ...
```

があれば、Gate F から `δ pk` を構成し、CFZP-025

```text
cfzp025FiniteBlockCertificate_of_phaseCoreMargins
```

を使って `Cfzp024FiniteBlockCertificate` を生成する constructor を追加する。

Bad-side `K` / absolute derivative envelope は引き続き明示入力でよい。

重要: constructor の中で phase-core margin を仮定として再入力しない。periodic cell containment から自動構成すること。

---

## 10. Gate I — explicit arithmetic frontier

本段の最後に、Good pair の残存 provider が何かを theorem/docstring で明示する。

概念的には

```text
∃ k : ℕ,
  π + 2πk + τ + Tε
    ≤ T * j * log p
  ∧
  T * j * log p + Tε
    ≤ 3π/2 + 2πk - τ
```

である。

可能ならこれを dedicated Prop として公開する:

```lean
def Cfzp026PrimePowerQuantitativeThirdQuadrantHit ... : Prop := ...
```

そして cell-containment Prop と iff / two-way adapters を作る。

この Prop が次段の arithmetic / distribution target になる。

---

## 11. Gate J — firewall

証明してはいけないもの:

- 全 prime-power pair が Good cell に入ること
- 任意 block に Good pair が存在すること
- positive density / equidistribution
- `j * log p` modulo `2π/T` の無条件稠密性
- uniform positive `τ`, `δ`, `κ`
- automatic cofinal certified dominance
- CFZP-018 の無条件 provider
- infinite sum / joint limit / limit exchange
- RH

Gap marker 例:

```lean
inductive Cfzp026PeriodicThirdQuadrantPhaseCellCertificateGap : Prop
  | noIndependentCofinalPrimePowerQuantitativeThirdQuadrantHitProvider
```

---

## 12. roadmap / public import

- `DkMath/RH.lean` に新 module を追加。
- `0000-CFZP-roadmap.md` に CFZP-026 section を追加。

Green 条件:

```text
periodic third-quadrant cell geometry: CLOSED
cell membership -> quantitative sin/cos margins: CLOSED
prime-power centered interval containment: CLOSED
containment <-> explicit T*j*log(p) inequalities: CLOSED
phase coefficient endpoint floors: CLOSED
cell containment -> explicit phase-core δ: CLOSED
cell certificate -> event/pulse quantitative credit: CLOSED
periodic-cell Good data -> CFZP-024 certificate constructor: CLOSED
cofinal quantitative third-quadrant hit provider: OPEN / GAP
```

---

## 13. 実装姿勢

この段は新しい closure interface を増やすためのものではない。

CFZP-025 の abstract `PhaseCore ≤ -δ` を、既知の periodic trigonometric geometry と prime-power center `T*j*log p` の有限区間条件まで下ろす。

最優先 spine:

```text
T*j*log p lands inside a strict QIII cell
        ↓
explicit sin/cos negative margins
        ↓
endpoint coefficient floors
        ↓
explicit δ > 0
        ↓
CFZP-025 prefactorFloor * δ
        ↓
CFZP-023 event credit
        ↓
CFZP-024 Good certificate
```

ここで閉じれば、次段の未解決問題はほぼ純粋に

```text
prime-power phases T*j*log p が
どれだけ頻繁に strict QIII target windows を hit するか
```

へ露出する。