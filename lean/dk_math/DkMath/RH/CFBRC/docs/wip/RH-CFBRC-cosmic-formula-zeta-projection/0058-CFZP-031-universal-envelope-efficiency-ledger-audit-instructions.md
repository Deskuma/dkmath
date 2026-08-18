# CFZP-0058 / CFZP-031

## universal-envelope efficiency ledger audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-024: finite Good-credit / Bad-debt certificate
- CFZP-027: subcritical ready third-quadrant Good hit
- CFZP-028: conditional fixed-prime irrational-rotation cofinal Good hits
- CFZP-029: universal automatic Bad envelope
- CFZP-030: common critical carrier and finite weighted net balance

CFZP-030 により Good/Bad 双方は

```text
C(p,j) = 2 * log p * CriticalScale(p^j)
```

という同じ positive carrier を持つところまで正規化された。

本段ではさらに CFZP-029 の universal Bad local shape を **prime-power pair ごとの基準質量** として採用し、ready Good hit をその基準質量に対する positive efficiency coefficient で表す。

目標は finite net balance を

```text
Good : +ρ(pk) * μ(pk)
Bad  : -1     * μ(pk)
```

という weighted occupancy ledger に変換することである。

新しい cofinal provider / density assumption / asymptotic theorem を導入してはいけない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaUniversalEnvelopeEfficiencyLedgerAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaUniversalEnvelopeEfficiencyLedgerAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaWeightedPrimePowerCreditDebtFactorizationAudit
import Mathlib.Tactic
```

---

## 2. Gate A — universal reference mass

prime-power pair ごとの canonical reference mass を定義する。

推奨 shape:

```lean
noncomputable def cfzp031PrimePowerReferenceMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzp030PrimePowerCriticalCarrier p j *
    cfzp030BadLocalShape ε W p j
```

そして exact に

```lean
cfzp031PrimePowerReferenceMass ε W p j =
  cfzp029PrimePowerBadDebtEnvelope ε W p j
```

を証明する。

safe prime-power 条件

```text
0 < ε
ε < log 2
Nat.Prime p
0 < j
```

の下では reference mass は strictly positive まで取ること。

`BadLocalShape` 自体も可能なら strictly positive を公開する。
CFZP-029 envelope の phase-core polynomial には positive term が含まれるので、safe positive right angle を使えば示せるはずである。

---

## 3. Gate B — ready Good efficiency ratio

ready Good shape を reference Bad shape で割った dimensionless efficiency を定義する。

```lean
noncomputable def cfzp031ReadyGoodEfficiency
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : ℝ :=
  cfzp030ReadyGoodShape ε W p j k τ /
    cfzp030BadLocalShape ε W p j
```

subcritical ready hit の条件

```text
0 < ε
ε < log 2
Nat.Prime p
0 < j
Cfzp027SubcriticalPhaseAspect W
0 < τ
τ ≤ π / 4
Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ
```

の下で

```text
0 < cfzp031ReadyGoodEfficiency ...
```

を証明する。

その上で exact factorization:

```lean
cfzp030GoodLocalCredit p j
    (cfzp030ReadyGoodShape ε W p j k τ) =
  cfzp031ReadyGoodEfficiency ε W p j k τ *
    cfzp031PrimePowerReferenceMass ε W p j
```

を証明する。

これが CFZP-031 の中心 theorem である。

---

## 4. Gate C — prefactor floor/ceiling efficiency

CFZP-030 では floor ≤ ceiling までしか記録していない。
ここでは endpoint formulas を使い、Good prefactor / Bad prefactor の exact finite relation を first-class にする。

周波数 endpoints を

```text
l = cfzpPrimePowerPhaseMagnitudeLeft ε p j
r = cfzpPrimePowerPhaseMagnitudeRight ε p j
```

とする。

可能なら以下の efficiency factor を定義する。

```lean
noncomputable def cfzp031PrefactorEfficiency
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  Real.exp (-(cfzpModePhaseAbscissa W) * (r - l)) * (l / r)^3
```

そして safe prime-power 条件の下で

```text
0 < PrefactorEfficiency
PrefactorEfficiency ≤ 1
CenteredDerivativePrefactorFloor
  = PrefactorEfficiency * CenteredDerivativePrefactorCeiling
```

を証明する。

さらに endpoint definitions から

```text
r - l = 2 * ε
```

が直接出せるなら、

```text
PrefactorEfficiency
  = exp (-2 * cfzpModePhaseAbscissa W * ε) * (l / r)^3
```

の exact normal form も公開する。

重要:
- limit / tendsto はまだ不要。
- 「j→∞ で比が○○へ収束」は本段では主張しない。
- exact finite identity を優先する。

---

## 5. Gate D — finite efficiency ledger

有限 block `(A,B]`、Good subset、ready-hit data `k, τ` に対して、Good を `+ρμ`、Bad を `-μ` とした ledger を定義する。

候補:

```lean
noncomputable def cfzp031EfficiencyLedger
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ)
    (Good : Finset (ℕ × ℕ))
    (k : ℕ × ℕ → ℕ)
    (τ : ℕ × ℕ → ℝ) : ℝ :=
  (∑ pk ∈ Good,
    cfzp031ReadyGoodEfficiency ε W pk.1 (pk.2 + 1) (k pk) (τ pk) *
      cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)) -
  (∑ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1))
```

ready-hit hypothesesの下で、これは exact に

```text
sum Good readyGoodLocalCredit
  - automaticBadDebtEnvelope Bad
```

へ等しいことを証明する。

これは「efficiency ledger」と「030 weighted Good/Bad difference」の exact bridge である。

---

## 6. Gate E — canonical CFZP-029 certificate との bridge

CFZP-030 の generic bridge は任意 certificate を許すため

```text
hbad : CertifiedBadDebtEnvelope cert.K = AutomaticBadDebtEnvelope
```

を明示的に要求する。これは正しい一般形なので変更しない。

一方、CFZP-029 constructor

```lean
cfzp029FiniteBlockCertificate_of_subcriticalReadyHits
```

で作られた canonical certificate では `K` は automatic derivative bound そのものである。

この specialized certificate については、可能なら definitional simplification / extensionality により

```text
CertifiedBadDebtEnvelope cert.K
  = AutomaticBadDebtEnvelope ...
```

を自動証明する theorem を追加する。

同様に `cert.κ` が ready Good shape に簡約できるなら、CFZP-030 `CertifiedNetBalance` と CFZP-031 `EfficiencyLedger` の exact equality まで公開する。

Lean simplification が過度に fragile になる場合は、029/027 constructor を無理に unfold して巨大証明にしないこと。その場合 Gate D の direct finite identity を正本とし、specialized certificate bridge は補助 theorem に留める。

---

## 7. Gate F — occupancy-score normal form

可能なら ledger をさらに「reference mass × score」の単一 block sumへ正規化する。

score の conceptual shape:

```text
score(pk) =
  if pk ∈ Good then ReadyGoodEfficiency(pk)
  else -1
```

定義候補:

```lean
noncomputable def cfzp031OccupancyScore ... (pk : ℕ × ℕ) : ℝ :=
  if pk ∈ Good then
    cfzp031ReadyGoodEfficiency ...
  else
    -1
```

そして `hGood : Good ⊆ blockSupport` の下で

```text
EfficiencyLedger
  = ∑ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
      ReferenceMass(pk) * OccupancyScore(pk)
```

を証明する。

これが通るなら非常に重要である。
CFZP-030 の「Good sum - Bad sum」が、CFZP-031 で初めて **一個の weighted signed occupancy sum** になる。

---

## 8. Gate G — exact dominance adapter

finite endpoint closure に必要な条件を efficiency ledger で直接書く theorem を追加する。

例えば canonical ready-hit data の下で

```text
RadialContactDeficit ε W A ≤ EfficiencyLedger + η
```

なら

```text
RadialContactDeficit ε W B ≤ η
```

へ既存 CFZP-030 / CFZP-024 theorem を通して到達する。

ただし新しい cofinal provider Prop を増やさないこと。
本段は finite one-block adapter まで。

---

## 9. 数学的診断として roadmap に記録すること

CFZP-031 の意味は次である。

```text
prime-power carrier C(p,j): common positive arithmetic weight
reference mass μ(p,j): universal automatic Bad ceiling
ready Good efficiency ρ(p,j): Good credit / reference mass
Good pair contribution: +ρ μ
Bad pair contribution:  -μ
```

したがって残る本質は単なる「Good hit が存在するか」ではなく、

```text
weighted occupancy of Good phase cells
vs
weighted occupancy of the complement
```

である。

特に CFZP-028 の fixed-prime cofinal hits は existence を与えるが、weighted occupancy dominance を直ちには与えない。この区別を明示する。

---

## 10. Firewall / Gap marker

少なくとも次は OPEN のままにする。

```text
noIndependentWeightedOccupancyDominanceProvider
noPositiveWeightedDensityProvider
noAutomaticSubcriticalWindowProvider
noIndependentPrimePhaseRotationIrrationalityProvider
noPrimeAxisWeightedMassProvider
```

以下は本段で導入しない。

- equidistribution theorem
- positive density theorem
- prime number theorem / Mertens 等の新規重装備
- infinite prime-power sums
- limit exchange / dominated convergence
- CFZP-018 provider の無条件化
- RH conclusion

---

## 11. Completion gate

- focused module build
- `lake env lean DkMath/RH.lean`
- full `lake build`
- new module に `sorry` / `axiom` / `native_decide` なし
- `DkMath/RH.lean` public import
- roadmap に CFZP-031 section 追記

実装量が増える場合でも、first priority は次の三本:

```text
ReferenceMass = automatic Bad envelope
ReadyGoodCredit = ReadyGoodEfficiency * ReferenceMass
EfficiencyLedger = single weighted occupancy sum
```

ここが閉じれば CFZP-031 は Green とする。