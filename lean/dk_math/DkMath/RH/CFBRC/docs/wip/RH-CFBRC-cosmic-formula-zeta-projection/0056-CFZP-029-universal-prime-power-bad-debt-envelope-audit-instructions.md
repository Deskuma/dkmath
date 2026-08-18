# CFZP-0056 / CFZP-029

## universal prime-power bad-debt envelope audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-023: quantitative prime-power pulse margin / absolute derivative envelope interface — Green-A
- CFZP-024: certified finite block credit/debt dominance — Green-A
- CFZP-025: phase-core margin -> derivative margin / Good credit — Green-A
- CFZP-027: ready Good hit -> CFZP-024 certificate, but Bad-side `K / henvelope` remains explicit — Green-A
- CFZP-028: irrational fixed-prime rotation -> cofinal ready Good hits — Green-A (conditional)

CFZP-028 により、明示仮定

```text
subcritical aspect ratio
Irrational ((T * log p) / (2π))
nonempty trimmed QIII target
```

の下では fixed prime の ready Good hit 自体は cofinally 供給できるようになった。

しかし CFZP-024/027 の finite certificate には Bad pair ごとにまだ

```text
K pk ≥ 0
Cfzp023CenteredProfileDerivativeAbsEnvelope ... (K pk)
```

を外部入力する必要がある。

本段ではこの **Bad-side analytic input を完全に自動化**する。

Good 側で CFZP-025 が centered interval の右端から derivative prefactor floor を作ったのと双対に、Bad 側では左端から derivative prefactor ceiling を作る。
さらに dimensionless phase derivative core に対して `|sin| ≤ 1`, `|cos| ≤ 1` と右端 angle を使う universal polynomial envelope を構成し、任意 safe prime-power pair に対して explicit な absolute derivative envelope を与える。

最終的に

```text
Bad pair
  -> automatic derivative envelope K_auto
  -> automatic event absolute bound
  -> automatic negative-debt bound
  -> automatic finite Bad-debt sum
```

を閉じ、CFZP-027 certificate constructor から per-Bad `K / henvelope` input を消す。

ここで block dominance 自体を証明してはいけない。CFZP-029 の到達点は、Good credit と Bad debt の双方を **explicit finite sums** として同じ土俵に置くことである。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaUniversalPrimePowerBadDebtEnvelopeAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaUniversalPrimePowerBadDebtEnvelopeAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaAdditiveCircleIrrationalRotationCofinalHitAudit
import Mathlib.Tactic
```

必要に応じて最小の analysis import を追加してよい。

---

## 2. Gate A — centered derivative prefactor ceiling

CFZP-025 の right-endpoint floor の双対として、left endpoint で ceiling を定義する。

推奨 shape:

```lean
noncomputable def cfzp029CenteredDerivativePrefactorCeiling
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  let l := cfzpPrimePowerPhaseMagnitudeLeft ε p j
  Real.exp (-(cfzpModePhaseAbscissa W) * l) / l ^ 3
```

safe-frequency assumptions

```text
0 < ε < log 2
Nat.Prime p
0 < j
```

の下で:

```text
0 < cfzp029CenteredDerivativePrefactorCeiling ε W p j
```

を証明する。

さらに任意

```text
u ∈ Ioo (PhaseMagnitudeLeft ε p j) (PhaseMagnitudeRight ε p j)
```

について

```text
exp(-a*u) / u^3 ≤ cfzp029CenteredDerivativePrefactorCeiling ε W p j
```

を証明する。

ここで `a = cfzpModePhaseAbscissa W > 0`。

証明の向き:

- `left ≤ u` なので `exp(-a*u) ≤ exp(-a*left)`。
- `0 < left ≤ u` なので `left^3 ≤ u^3`。
- 分子・分母の正値を明示して quotient inequality を閉じる。

数値近似は使わない。

---

## 3. Gate B — universal dimensionless phase-core absolute envelope

CFZP-006Y の

```text
PhaseDerivativeCore α θ
  = PhaseDerivativeSinCoeff α θ * sin θ
    + 2*θ*(α*θ+1)*cos θ
```

に対し、右端 `R` だけで全 interior point を抑える universal envelope を定義する。

推奨:

```lean
noncomputable def cfzp029PhaseDerivativeCoreAbsEnvelope
    (α R : ℝ) : ℝ :=
  R ^ 2 * |1 - α ^ 2| +
    2 * (α * R + 1) +
    2 * R * (α * R + 1)
```

`0 ≤ α`, `0 ≤ θ ≤ R` の下で:

```text
0 ≤ cfzp029PhaseDerivativeCoreAbsEnvelope α R
```

および

```text
|cfzpPhaseDerivativeCore α θ|
  ≤ cfzp029PhaseDerivativeCoreAbsEnvelope α R
```

を証明する。

中間補題として次を分離するとよい:

```text
|cfzpPhaseDerivativeSinCoeff α θ|
  ≤ θ^2 * |1 - α^2| + 2 * (α*θ + 1)
```

その後 `θ ≤ R` と `α ≥ 0` から右端へ押し上げる。

重要:

- Bad envelope には `α ≤ 1` / subcriticality を要求しない。
- `abs (1 - α^2)` を使うことで任意 `α ≥ 0` に対して成立させる。
- `|sin θ| ≤ 1`, `|cos θ| ≤ 1` の標準定理を使う。

この Gate は Good-cell geometry とは独立な universal upper bound である。

---

## 4. Gate C — centered prime-power derivative-core envelope

safe prime-power interval 上で

```text
θ = u * W.rectangle.T
Rθ = cfzpPrimePowerPhaseAngleRight ε W p j
α = cfzpModePhaseAspectRatio W
```

とする。

既存 exact coordinate theorem

```text
cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
```

および angle/magnitude endpoint identity を使い、任意 centered `u` について

```text
|cfzpNegativeFrequencyBoundaryProfileDerivativeCore
    (cfzpModePhaseAbscissa W) W.rectangle.T u|
  ≤ cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (cfzpPrimePowerPhaseAngleRight ε W p j)
```

を証明する。

必要な facts:

```text
0 < u
0 < u*T
u*T ≤ rightMagnitude*T = rightAngle
0 < aspectRatio
```

は既存 safe-frequency / rectangle API から取る。

---

## 5. Gate D — automatic centered profile derivative envelope

per-pair automatic derivative bound を first-class にする。

推奨:

```lean
noncomputable def cfzp029CenteredProfileDerivativeAbsBound
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzp029CenteredDerivativePrefactorCeiling ε W p j *
    cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (cfzpPrimePowerPhaseAngleRight ε W p j)
```

safe prime-power assumptions の下で:

```text
0 ≤ cfzp029CenteredProfileDerivativeAbsBound ε W p j
```

を証明する。

CFZP-006X exact derivative formula

```text
deriv Profile(u)
  = exp(-a*u)/u^3 * DerivativeCore(u)
```

と Gate A/C を組み合わせて:

```lean
Cfzp023CenteredProfileDerivativeAbsEnvelope ε W p j
  (cfzp029CenteredProfileDerivativeAbsBound ε W p j)
```

を **無条件に（safe prime-power facts 以外の外部 envelope hypothesis なしで）** 構成する。

積の absolute value と nonnegative factor の管理を明示する。

---

## 6. Gate E — automatic event / pulse / negative-debt envelope

per-prime-power debt ceiling を first-class にする。

推奨:

```lean
noncomputable def cfzp029PrimePowerBadDebtEnvelope
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) *
    cfzpModeCriticalScale (p ^ j) *
    cfzp029CenteredProfileDerivativeAbsBound ε W p j
```

safe prime-power assumptions の下で:

```text
0 ≤ cfzp029PrimePowerBadDebtEnvelope ε W p j
```

を証明する。

CFZP-023 の既存 theorem を再利用して:

```text
|cfzpPrimePowerBranchFreeTrigEvent ε W p j|
  ≤ cfzp029PrimePowerBadDebtEnvelope ε W p j
```

```text
cfzp019PrimePowerEventNegativeDebt ε W p j
  ≤ cfzp029PrimePowerBadDebtEnvelope ε W p j
```

および prime-power pulse について

```text
|cfzp021VonMangoldtPulse ε W (p^j)|
  ≤ cfzp029PrimePowerBadDebtEnvelope ε W p j
```

を公開する。

新しい MVT argument を重複実装せず、必ず CFZP-023 の

```text
cfzp023PrimePowerBranchFreeTrigEvent_abs_le_quantitativeEnvelope
cfzp023PrimePowerEventNegativeDebt_le_quantitativeEnvelope
cfzp023VonMangoldtPulse_abs_le_quantitativeEnvelope_of_eq_prime_pow
```

を再利用する。

---

## 7. Gate F — automatic finite Bad-debt sum

Bad support に対する explicit finite sum を定義する。

```lean
noncomputable def cfzp029AutomaticBadDebtEnvelope
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (Bad : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ Bad,
    cfzp029PrimePowerBadDebtEnvelope ε W pk.1 (pk.2 + 1)
```

`Bad ⊆ cfzp024PrimePowerPairBlockSupport A B`, `A ≤ B`, safe ε の下で

```text
∑ pk ∈ Bad,
    cfzp019PrimePowerEventNegativeDebt ε W pk.1 (pk.2+1)
  ≤ cfzp029AutomaticBadDebtEnvelope ε W Bad
```

を証明する。

さらに `Good ⊆ blockSupport A B` と Good events が nonnegative である certificate context があれば、既存 CFZP-024 split を使って

```text
cfzp022BlockNegativeEventDebt ε W A B
  ≤ cfzp029AutomaticBadDebtEnvelope ε W
      (cfzp024BadPrimePowerPairBlockSupport A B Good)
```

へ接続できる形を作る。

この段階では Good の sign を再証明せず、次 Gate の automatic certificate を経由してもよい。

---

## 8. Gate G — CFZP-024 certificate without per-Bad `K / henvelope`

CFZP-027

```text
cfzp027FiniteBlockCertificate_of_subcriticalReadyHits
```

を wrap し、Bad 側に

```text
K pk := cfzp029CenteredProfileDerivativeAbsBound
  ε W pk.1 (pk.2+1)
```

を自動投入する constructor を追加する。

推奨 shape:

```lean
noncomputable def cfzp029FiniteBlockCertificate_of_subcriticalReadyHits
    ...
    (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ)
    (τ : ℕ × ℕ → ℝ)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : ...)
    (hτ4 : ...)
    (hready : ∀ pk ∈ Good,
      Cfzp027PrimePowerReadyThirdQuadrantHit ...)
    : Cfzp024FiniteBlockCertificate ε W A B
```

**この constructor には `K`, `hK`, `henvelope` argument を残さない。**

Bad pair が canonical block support に属することから

```text
Nat.Prime pk.1
0 < pk.2 + 1
```

を回収し、Gate D で自動的に envelope を埋める。

これが本段の主要 API endpoint。

---

## 9. Gate H — expose the final finite quantitative balance

可能なら、Good/Bad の両側が explicit になったことを first-class finite inequality として露出する。

Good pair `pk` の certified credit は既存 spine から

```text
2 * log(pk.1) * CriticalScale(pk.1^(pk.2+1)) *
  (CenteredDerivativePrefactorFloor * PhaseCoreMargin)
```

Bad pair の automatic debt ceiling は Gate E の

```text
cfzp029PrimePowerBadDebtEnvelope
```

である。

この二つの finite sums と start deficit を並べた theorem / Prop を作ってよい。
概念形:

```text
G_A + Σ BadEnvelope
  ≤ Σ GoodCertifiedCredit + η
  -> G_B ≤ η
```

ただし実装 ergonomics 上、constructed `Cfzp024FiniteBlockCertificate` の
`cfzp024CertifiedGoodCredit` / `cfzp024CertifiedBadDebtEnvelope` をそのまま利用した方が短い場合は、それでよい。

重要なのは **新しい abstract provider wrapper を一個増やすことではなく**、
029 で `BadEnvelope` が外部 hypothesis ではなく explicit expression になったことを theorem surface に出すことである。

---

## 10. Critical-scale sanity record

本段の docstring / roadmap には、既存定義

```text
cfzpModeCriticalScale n = exp(-(1/2) * log n)
```

を記録する。

prime-power では critical scale が exponent とともに減衰するため、

```text
cofinally many Good hits
```

だけから

```text
unbounded total Good credit
```

を推論してはいけない。

同様に automatic Bad envelope が得られても、その finite sum が Good credit より小さいことは本段では主張しない。

次段は **hit-count ではなく explicit weighted credit/debt sums の比較**を攻める。

---

## 11. Firewall / Gap

証明してはいけないもの:

- cofinally many Good hits だけから certified dominance が出ること
- fixed-prime Good credit の総和が発散すること
- automatic Bad-debt sum が自動的に小さいこと
- positive density / equidistribution だけから weighted dominance が出ること
- arbitrary window の subcriticality
- arbitrary prime/window の rotation irrationality
- CFZP-024 cofinal dominance provider
- CFZP-018 unconditional provider
- infinite sum / joint limit / limit exchange
- RH

Gap marker 例:

```lean
inductive Cfzp029UniversalPrimePowerBadDebtEnvelopeGap : Prop
  | noIndependentWeightedCreditDebtDominanceProvider
  | noAutomaticSubcriticalWindowProvider
  | noIndependentPrimePhaseRotationIrrationalityProvider
```

---

## 12. roadmap / public import

- `DkMath/RH.lean` に新 module を追加。
- `0000-CFZP-roadmap.md` に CFZP-029 section を追加。

Green 条件:

```text
left-endpoint derivative prefactor ceiling: CLOSED
universal phase-core absolute envelope: CLOSED
centered derivative-core absolute envelope: CLOSED
automatic CFZP-023 derivative envelope for every safe prime power: CLOSED
automatic event/pulse absolute envelope: CLOSED
automatic one-event negative-debt bound: CLOSED
automatic finite Bad-debt sum: CLOSED
CFZP-024 certificate constructor without per-Bad K/henvelope: CLOSED
weighted Good-credit vs Bad-debt dominance: OPEN / GAP
```

---

## 13. 実装姿勢

CFZP-029 は新しい phase distribution theorem を作る段ではない。

028 までで Good の存在側は conditional にかなり進んだ。
029 ではその反対側、すなわち **Bad が最大でどれだけ借金を作れるか**を universal analytic envelope で閉じる。

最優先 spine:

```text
safe prime-power interval
        ↓
left-endpoint prefactor ceiling
        +
right-angle universal phase-core envelope
        ↓
automatic derivative |.| envelope
        ↓
automatic event |.| / negative-debt bound
        ↓
finite automatic Bad-debt sum
        ↓
CFZP-024 certificate with no Bad analytic inputs
```

ここで閉じれば、次の魔核は明確に

```text
Σ weighted Good credit
    vs
start deficit + Σ weighted Bad debt envelope
```

という有限・定量的な収支比較になる。