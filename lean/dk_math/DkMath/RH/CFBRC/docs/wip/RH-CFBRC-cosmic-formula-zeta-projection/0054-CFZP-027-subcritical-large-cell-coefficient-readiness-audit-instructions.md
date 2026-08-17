# CFZP-0054 / CFZP-027

## subcritical large-cell coefficient readiness audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-024: certified finite block credit/debt dominance — Green-A
- CFZP-025: quantitative phase-core margin synthesis — Green-A
- CFZP-026: periodic third-quadrant phase-cell certificate — Green-A

CFZP-026 により Good-side phase geometry は、prime-power center

```text
T * j * log p
```

が周期第三象限 cell の中心許容窓へ入る有限不等式まで落ちた。

ただし CFZP-026 の cell certificate にはまだ pair ごとに

```text
0 ≤ A0
```

すなわち

```text
0 ≤ PhaseSinCoeffFloor α L R
```

を与える必要がある。

ここで

```text
α = cfzpModePhaseAspectRatio W
```

とすると、`0 ≤ α < 1` では

```text
1 - α^2 > 0
```

であるため、

```text
A0 = L^2 * (1 - α^2) - 2 * (α*R + 1)
```

は cell index `k` が大きくなると quadratic positive term が linear negative term を支配する。

本段ではこの事実を exact finite algebra と Archimedean growth だけで first-class theorem にする。

目的は、Good pair ごとの `A0 ≥ 0` input を消して、十分大きな cell では

```text
subcritical aspect ratio α < 1
+ large-cell readiness
+ quantitative T*j*log p hit
```

だけから CFZP-026/025/024 certificate を生成できるようにすることである。

さらに次段の irrational-rotation / additive-circle provider のため、center target の有効幅

```text
π/2 - 2*τ - 2*T*ε
```

と、その正値条件

```text
τ + T*ε < π/4
```

も明示する。

本段では irrational rotation、density/equidistribution、prime hit の存在、cofinal block dominance、RH は証明しない。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSubcriticalLargeCellCoefficientReadinessAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaSubcriticalLargeCellCoefficientReadinessAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPeriodicThirdQuadrantPhaseCellCertificateAudit
import Mathlib.Tactic
```

Archimedean / atTop API が追加 import を要求する場合のみ追加する。

---

## 2. Gate A — subcritical aspect ratio

`α < 1` を単なる局所仮定のまま散在させず first-class にする。

推奨:

```lean
def Cfzp027SubcriticalPhaseAspect
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  cfzpModePhaseAspectRatio W < 1
```

既存

```text
0 < cfzpModePhaseAspectRatio W
```

と合わせて

```text
0 < 1 - α^2
```

を証明する。

また `W.rectangle.T > 0` を使って、可能なら

```text
cfzpModePhaseAspectRatio W < 1
  <->
cfzpModePhaseAbscissa W < W.rectangle.T
```

も公開する。

これは解析上の意味を明確にする adapter であり、新しい仮定を増やすものではない。

---

## 3. Gate B — untrimmed cell is the worst coefficient floor

固定 `α`, `k` について `τ = 0` の baseline floor を定義する。

推奨:

```lean
noncomputable def cfzp027UntrimmedPhaseSinCoeffFloor
    (α : ℝ) (k : ℕ) : ℝ :=
  cfzp026PhaseSinCoeffFloor α
    (cfzp026ThirdQuadrantCellLeft k 0)
    (cfzp026ThirdQuadrantCellRight k 0)
```

`0 ≤ α ≤ 1`, `0 ≤ τ` の下で、trim を増やすと

```text
CellLeft(k,0) ≤ CellLeft(k,τ)
CellRight(k,τ) ≤ CellRight(k,0)
```

となる。

これを用いて

```text
UntrimmedFloor α k
  ≤ PhaseSinCoeffFloor α (CellLeft k τ) (CellRight k τ)
```

を証明する。

`τ ≤ π/4` は cell 自体の非空性には必要だが、この floor monotonicity に不要なら仮定しない。

重要: これにより `τ` ごとの coefficient positivity を追う必要がなくなる。worst case は `τ = 0`。

---

## 4. Gate C — explicit large-cell readiness contract

asymptotic notationだけで済ませず、Lean が扱いやすい explicit finite sufficient condition を置く。

`x_k := 2 * π * k`, `d := 1 - α^2` として、例えば

```lean
def Cfzp027PhaseSinCoefficientReady
    (α : ℝ) (k : ℕ) : Prop :=
  4 ≤ (1 - α^2) * (2 * Real.pi * (k : ℝ)) ∧
  3 * Real.pi + 2 ≤ 2 * (2 * Real.pi * (k : ℝ))
```

を候補とする。

定数は proof ergonomics に応じてより大きい安全定数へ変更してよい。ただし contract は explicit finite inequalities のままにする。

`0 ≤ α < 1` と readiness から

```text
0 ≤ cfzp027UntrimmedPhaseSinCoeffFloor α k
```

を証明する。

証明の intended algebra は以下。

```text
L0 = π + x_k ≥ x_k
R0 = 3π/2 + x_k
α ≤ 1

d * L0^2 ≥ d * x_k^2
2*(α*R0 + 1) ≤ 2*x_k + 3π + 2

d*x_k ≥ 4  ->  d*x_k^2 ≥ 4*x_k
2*x_k ≥ 3π + 2  ->  4*x_k ≥ 2*x_k + 3π + 2
```

よって `A0 ≥ 0`。

`nlinarith` を使ってよいが、各符号条件を明示すること。

---

## 5. Gate D — readiness gives every trimmed-cell coefficient condition

Gate B/C を合成し、

```text
0 ≤ α < 1
Cfzp027PhaseSinCoefficientReady α k
0 ≤ τ
```

から

```text
0 ≤ cfzp026PhaseSinCoeffFloor α
  (cfzp026ThirdQuadrantCellLeft k τ)
  (cfzp026ThirdQuadrantCellRight k τ)
```

を first-class theorem にする。

これが CFZP-026 の `hA` input を自動生成する adapter となる。

---

## 6. Gate E — sufficiently large cells are automatically ready

`0 ≤ α < 1` のとき readiness cell index が cofinal に存在することを証明する。

最低限:

```lean
theorem cfzp027_exists_ready_cellIndex_ge
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ Cfzp027PhaseSinCoefficientReady α k := ...
```

可能なら stronger shape:

```lean
∃ K0 : ℕ, ∀ k : ℕ, K0 ≤ k ->
  Cfzp027PhaseSinCoefficientReady α k
```

を証明する。

Mathlib の Archimedean theorem / `Nat.cast` atTop API を使ってよい。

ここは phase distribution theorem ではない。単に `2πk -> ∞` により explicit readiness inequalities を満たすことを閉じる。

---

## 7. Gate F — center-target effective width

CFZP-026 arithmetic hit の center 許容区間を整理する。

固定 `k,τ` に対し center target は

```text
CellLeft(k,τ) + T*ε
  ≤ center
center
  ≤ CellRight(k,τ) - T*ε
```

である。

その width が exact に

```text
(CellRight(k,τ) - T*ε)
  - (CellLeft(k,τ) + T*ε)
= π/2 - 2*τ - 2*T*ε
```

となる theorem を追加する。

さらに `T > 0`, `ε > 0` のもとで

```text
0 < π/2 - 2*τ - 2*T*ε
  <->
τ + T*ε < π/4
```

または一方向 sufficient adapter を証明する。

次段の dense rotation で必要なのは **nonempty open target** である。ここを first-class にしておく。

推奨 property:

```lean
def Cfzp027ThirdQuadrantTargetHasInterior
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (τ : ℝ) : Prop :=
  τ + W.rectangle.T * ε < Real.pi / 4
```

---

## 8. Gate G — ready arithmetic hit

CFZP-026 の arithmetic hit と coefficient readiness を一つの finite Good contract にまとめる。

推奨:

```lean
def Cfzp027PrimePowerReadyThirdQuadrantHit
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : Prop :=
  Cfzp026PrimePowerQuantitativeThirdQuadrantHit ε W p j k τ ∧
  Cfzp027PhaseSinCoefficientReady (cfzpModePhaseAspectRatio W) k
```

`Cfzp027SubcriticalPhaseAspect W`, `0 < τ ≤ π/4` と ready hit から

- CFZP-026 cell containment
- `0 ≤ A0`
- `0 < cfzp026PhaseCoreMargin ...`

を自動生成する adapters を追加する。

`A0` を再び theorem hypothesis として要求してはならない。

---

## 9. Gate H — direct event/pulse credit from ready hit

Gate G を CFZP-026 の direct credit theorem へ流し、`hA` を外した wrapper を作る。

概念形:

```text
subcritical aspect
+ ready arithmetic hit
+ 0 < τ ≤ π/4
  ->
explicit positive event credit
```

lower bound 自体は CFZP-026 の既存 formula を再利用する。

同じものを von Mangoldt pulse へ transportする。

可能なら explicit lower-bound quantityの positivityも公開する。

---

## 10. Gate I — CFZP-024 finite certificate constructor without per-pair `hA`

Good pair ごとに

```text
k pk
τ pk
Cfzp027PrimePowerReadyThirdQuadrantHit ...
```

を与えれば、`Cfzp027SubcriticalPhaseAspect W` から `aspectRatio ≤ 1` と各 `hA` を自動生成し、CFZP-026

```text
cfzp026FiniteBlockCertificate_of_periodicThirdQuadrantCellHits
```

へ流して

```text
Cfzp024FiniteBlockCertificate ε W A B
```

を作る constructor を追加する。

Bad-side `K` / absolute derivative envelope はこの段では引き続き明示入力でよい。

この constructor の Good-side input に `hA` や phase-core margin `δ` を再導入しないこと。

---

## 11. Gate J — next arithmetic/dynamical frontier

固定 prime `p` と固定 trim `τ` に対する cofinal hit target を first-class Prop にしてよい。

候補:

```lean
def Cfzp027CofinalReadyThirdQuadrantHitsForPrime
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p : ℕ) (τ : ℝ) : Prop :=
  ∀ J K : ℕ, ∃ j k : ℕ,
    J ≤ j ∧ K ≤ k ∧
    Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ
```

proof ergonomics 上 `K` が readiness から後で吸収できるなら、hit と readiness の provider を分離してもよい。

本段ではこの cofinal hit provider 自体は証明しない。

次段は `AddCircle (2π)` 上の rotation

```text
j • (T * log p mod 2π)
```

と `Cfzp026PrimePowerQuantitativeThirdQuadrantHit` を接続する予定である。

Mathlib には irrational rotation の dense-range theorem が存在するので、独自 density theory を再実装しないこと。

---

## 12. firewall

証明してはいけないもの:

- `cfzpModePhaseAspectRatio W < 1` が全 window で自動成立すること
- prime-power phase hit の存在そのもの
- irrationality of `T * log p / (2π)`
- 全 prime / 全 prime-power の Good membership
- positive density / equidistribution
- automatic Bad debt control
- automatic cofinal certified dominance
- CFZP-018 の無条件 provider
- infinite sum / joint limit / limit exchange
- finite-window criticality の無条件化
- RH

Gap marker 例:

```lean
inductive Cfzp027SubcriticalLargeCellCoefficientReadinessGap : Prop
  | noIndependentCofinalReadyPrimePowerThirdQuadrantHitProvider
```

`aspectRatio < 1` は本段では explicit structural hypothesis であり、Gap と phase-hit Gap を混同しない。

---

## 13. roadmap / public import

- `DkMath/RH.lean` に新 module を追加。
- `0000-CFZP-roadmap.md` に CFZP-027 section を追加。

Green 条件:

```text
subcritical aspect gap positivity: CLOSED
subcritical aspect <-> a<T adapter: CLOSED if practical
untrimmed floor is worst trimmed floor: CLOSED
explicit large-cell readiness -> A0≥0: CLOSED
cofinally/even eventually large cells are ready: CLOSED
center target exact width: CLOSED
target interior condition: CLOSED
ready arithmetic hit -> CFZP-026 hA: CLOSED
ready hit -> event/pulse credit: CLOSED
ready-hit Good data -> CFZP-024 certificate: CLOSED
cofinal ready phase-hit provider: OPEN / GAP
```

---

## 14. 実装姿勢

この段の目的は新しい closure interface を増やすことではない。

CFZP-026 に残った `A0 ≥ 0` を **large-cell geometry の自動事実**へ降格させる。

最優先 spine:

```text
aspectRatio < 1
        ↓
1 - aspectRatio^2 > 0
        ↓
large k makes quadratic coefficient floor positive
        ↓
A0(k,τ) ≥ A0(k,0) ≥ 0
        ↓
ready T*j*log p hit
        ↓
CFZP-026 explicit δ > 0
        ↓
CFZP-025 / 023 event credit
        ↓
CFZP-024 Good certificate
```

この段が Green なら、Good-side の残存 provider はほぼ

```text
T*j*log p modulo 2π が
nonempty strict QIII center target を cofinally hit するか
```

へ純化される。
