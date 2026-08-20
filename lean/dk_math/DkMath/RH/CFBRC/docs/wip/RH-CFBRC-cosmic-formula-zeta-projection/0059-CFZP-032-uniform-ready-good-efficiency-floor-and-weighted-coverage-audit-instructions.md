# CFZP-0059 / CFZP-032

## uniform ready-Good efficiency floor and weighted coverage audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-028: fixed-prime irrational AddCircle rotation -> cofinal ready Good hits (conditional)
- CFZP-029: universal automatic Bad envelope
- CFZP-030: common carrier and finite net balance
- CFZP-031: universal reference mass `μ`, ready Good efficiency `ρ`, weighted occupancy ledger

CFZP-031 で finite block は

```text
Good : +ρ(pk) * μ(pk)
Bad  : -1     * μ(pk)
```

という一個の weighted signed occupancy ledger に圧縮された。

本段の目的は二つである。

1. CFZP-031 の minor interface gap を閉じ、`EfficiencyLedger` 自体から radial-contact endpoint へ直接到達する finite theorem を作る。
2. subcritical ready third-quadrant hit について、Good efficiency `ρ` を **0 から離れた explicit positive constant** で一様に下から抑える。

その後、ledger dominance を

```text
weighted Good reference mass
vs
whole block reference mass
```

という一個の有限 coverage inequality に還元する。

この段でも equidistribution / positive density / infinite sum / PNT は導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaUniformReadyGoodEfficiencyFloorAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaUniformReadyGoodEfficiencyFloorAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaUniversalEnvelopeEfficiencyLedgerAudit
import Mathlib.Tactic
```

---

## 2. Gate A — close the direct EfficiencyLedger endpoint adapter

CFZP-031 の

```text
cfzp031EfficiencyLedger_bound_implies_radialContactDeficit_le
```

は theorem 名に反して hypothesis が `cfzp030CertifiedNetBalance` の bound のままである。
これは核心 ledger identity を壊す問題ではないが、031 -> endpoint の public API としては未完である。

本段では ready-hit data を直接受ける theorem を追加する。

目標 shape:

```lean
theorem cfzp032EfficiencyLedger_bound_implies_radialContactDeficit_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : ∀ pk ∈ Good, 0 < τ pk)
    (hτ4 : ∀ pk ∈ Good, τ pk ≤ Real.pi / 4)
    (hready : ∀ pk ∈ Good,
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W
        pk.1 (pk.2 + 1) (k pk) (τ pk))
    {η : ℝ}
    (hledger :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
        cfzp031EfficiencyLedger ε W A B Good k τ + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η
```

実装方法は二択。

### Route 1: canonical certificate projections

CFZP-029 constructor

```text
cfzp029FiniteBlockCertificate_of_subcriticalReadyHits
```

を使い、その specialized certificate について

```text
cert.Good = Good
cert.κ pk = cfzp030ReadyGoodShape ...
cert.K pk = cfzp029CenteredProfileDerivativeAbsBound ...
```

を必要最小限の `rfl` / `simp` / projection theorem で回収し、

```text
CertifiedNetBalance cert = EfficiencyLedger ...
```

を証明して CFZP-030 endpoint adapter に流す。

### Route 2: direct finite inequalities

constructor の unfold が fragile なら、以下を直接組み合わせる。

- Good ready local credit sum <= block positive mass
- Good negative debt = 0
- Bad negative debt <= automatic Bad envelope
- CFZP-031 ledger = Good local credit sum - automatic Bad envelope
- CFZP-022 signed block budget endpoint theorem

**public theorem から `cert`, `K`, `henvelope`, `hbad` を消すことが Gate A の completion condition。**

既存 CFZP-031 theorem は削除・変更しなくてよい。

---

## 3. Gate B — factor Good efficiency into prefactor efficiency × phase efficiency

CFZP-031 の Good efficiency は

```text
ReadyGoodShape / BadLocalShape
```

である。

定義を展開すると

```text
(Floor * PhaseMargin) / (Ceiling * PhaseEnvelope)
```

であり、CFZP-031 では既に

```text
Floor = PrefactorEfficiency * Ceiling
```

が CLOSED。

phase ratio を first-class にする。

推奨:

```lean
noncomputable def cfzp032ReadyGoodPhaseEfficiency
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : ℝ :=
  cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ /
    cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (cfzpPrimePowerPhaseAngleRight ε W p j)
```

safe prime-power + ready-hit 条件の下で denominator は strictly positive。

exact factorization:

```text
cfzp031ReadyGoodEfficiency ...
  = cfzp031PrefactorEfficiency ... *
      cfzp032ReadyGoodPhaseEfficiency ...
```

を証明する。

これが本段の基本分解。

---

## 4. Gate C — phase-envelope monotonicity in the right endpoint

CFZP-029 envelope

```text
E(α,R) = R^2 * |1-α^2|
       + 2*(αR+1)
       + 2*R*(αR+1)
```

について、

```text
0 ≤ α
0 ≤ R₁ ≤ R₂
```

なら

```text
E(α,R₁) ≤ E(α,R₂)
```

を証明する。

subcritical ready hit の cell containment から

```text
PhaseAngleRight ε W p j
  ≤ ThirdQuadrantCellRight k τ
```

なので、actual Bad phase envelope を periodic-cell right endpoint envelope で上から抑える。

この theorem は phase efficiency lower bound の分母制御に使う。

---

## 5. Gate D — common quadratic coefficient on a subcritical cell

aspect ratio を `α` とし、

```text
q(α) := 1 + 2*α - α^2
```

を定義してよい。

subcritical assumptions

```text
0 ≤ α
α < 1
```

の下で

```text
1 ≤ q(α)
0 < q(α)
|1 - α^2| = 1 - α^2
```

を閉じる。

periodic cell endpoints

```text
L := ThirdQuadrantCellLeft k τ
R := ThirdQuadrantCellRight k τ
```

について exact algebraic normal forms を作る。

Good phase-margin の括弧部分:

```text
PhaseSinCoeffFloor α L R + PhaseCosCoeffFloor α L
  = q(α) * L^2 + 2*L - 2*α*R - 2
```

Bad phase envelope at cell-right:

```text
PhaseDerivativeCoreAbsEnvelope α R
  = q(α) * R^2 + 2*(α+1)*R + 2
```

これにより Good/Bad の leading quadratic coefficient が同じ `q(α)` であることを Lean theorem として固定する。

これは本段の重要な数学診断である。

---

## 6. Gate E — explicit large-cell phase-efficiency floor

目標は ready cell が十分大きければ

```text
PhaseMargin / PhaseEnvelope >= sin(τ) / C
```

という **prime/exponent に依存しない定数 floor** を得ること。

推奨定数はまず `C = 16` を狙う。

proof spine:

1. `q ≥ 1`。
2. large cell で negative linear remainder を quadratic term の半分以下にする:

```text
2 * (α * R + 1) ≤ q * L^2 / 2
```

したがって

```text
q*L^2 + 2*L - 2*α*R - 2 >= q*L^2 / 2
```

3. denominator linear remainder を quadratic term 以下にする:

```text
2*(α+1)*R + 2 ≤ q*R^2
```

したがって

```text
Envelope α R ≤ 2*q*R^2
```

4. cell geometry から

```text
R ≤ 2*L
```

を得て

```text
L^2 / R^2 ≥ 1/4
```

5. よって

```text
PhaseMargin / Envelope >= sin τ / 16
```

を得る。

### cell-size threshold

まず `1 ≤ k` だけで上記二つの quadratic-vs-linear inequality が通るか試すこと。

理由:

```text
L >= 3π
R roughly >= 13π/4
0 ≤ α < 1
q >= 1
```

なので十分な余裕がある。
`Real.pi_gt_three`, `Real.pi_lt_four` 等の標準 exact bounds と `nlinarith` で閉じられる可能性が高い。

ただし proof が brittle になる場合は、無理に `k ≥ 1` に固定しない。
代わりに explicit readiness contract

```lean
def Cfzp032LargeCellEfficiencyReady (α : ℝ) (k : ℕ) (τ : ℝ) : Prop :=
  ...quadratic-vs-linear inequalities...
```

を定義し、subcritical `α` と fixed `τ` に対して

```text
∃ K₀, ∀ k ≥ K₀, Cfzp032LargeCellEfficiencyReady α k τ
```

を証明してよい。

**completion condition は「explicit finite K₀ after which a uniform positive phase-efficiency floor holds」であり、K₀=1 自体は必須ではない。**

---

## 7. Gate F — prefactor efficiency has a uniform positive floor on large ready hits

CFZP-031 exact width form:

```text
PrefactorEfficiency
  = exp (-a * (2ε)) * (leftMagnitude / rightMagnitude)^3
```

を使う。

ready hit の containment と target interior

```text
τ + T*ε < π/4
```

から、cell が十分右にあれば

```text
2*ε ≤ leftMagnitude
```

を得る。

すると

```text
rightMagnitude = leftMagnitude + 2ε ≤ 2*leftMagnitude
```

より

```text
1/2 ≤ leftMagnitude / rightMagnitude
```

したがって

```text
exp (-a*(2ε)) / 8 ≤ PrefactorEfficiency
```

を得る。

`1 ≤ k` で十分ならその形を優先する。
そうでなければ Gate E と同じ large-cell threshold に統合する。

---

## 8. Gate G — uniform positive ready-Good efficiency floor

explicit floor を定義する。

候補:

```lean
noncomputable def cfzp032UniformReadyGoodEfficiencyFloor
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (τ : ℝ) : ℝ :=
  Real.exp (-(cfzpModePhaseAbscissa W) * (2 * ε)) *
    Real.sin τ / 128
```

`0 < τ ≤ π/4` の下で

```text
0 < cfzp032UniformReadyGoodEfficiencyFloor ε W τ
```

を証明する。

そして safe/subcritical/interior/large-ready conditions の下で

```text
cfzp032UniformReadyGoodEfficiencyFloor ε W τ
  ≤ cfzp031ReadyGoodEfficiency ε W p j k τ
```

を証明する。

この theorem は `p` と `j` に依存しないことが重要。

定数 `128 = 8 * 16` は sharp である必要はない。
Lean proof を単純化するため、必要ならより大きい固定定数へ弱めてもよい。
ただし floor は strictly positive かつ `p,j` independent に保つこと。

---

## 9. Gate H — strengthen CFZP-028 cofinal hits to cofinal uniformly-efficient hits

新しい assumption/provider を導入するのではなく、CFZP-028 の conditional theorem から導出する。

fixed prime `p` に対し

```text
Nat.Prime p
subcritical W
0 < ε < log 2
0 < τ ≤ π/4
target interior
Irrational ((T log p)/(2π))
```

を仮定する。

CFZP-028 は任意 `J,K` より後の ready hit `(j,k)` を供給するので、Gate E/F の threshold も `K` に吸収する。

最終 theorem shape:

```text
∀ J K, ∃ j k,
  J ≤ j ∧ K ≤ k ∧
  Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ ∧
  UniformEfficiencyFloor ε W τ
    ≤ ReadyGoodEfficiency ε W p j k τ
```

これにより

```text
cofinal Good hit
```

から

```text
cofinal Good hit with uniform positive efficiency
```

へ conditional に強化する。

これは weighted density を意味しない。

---

## 10. Gate I — reduce ledger dominance to weighted Good reference-mass coverage

block 全体の reference mass と Good reference mass を定義する。

```lean
noncomputable def cfzp032BlockReferenceMass ... :=
  ∑ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)

noncomputable def cfzp032GoodReferenceMass ... :=
  ∑ pk ∈ Good,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1)
```

`hGood : Good ⊆ blockSupport` から exact split:

```text
BlockReferenceMass = GoodReferenceMass + BadReferenceMass
```

を証明する。

各 Good pair に一様 efficiency floor `ρ₀` があるとき

```text
(1 + ρ₀) * GoodReferenceMass - BlockReferenceMass
  ≤ EfficiencyLedger
```

を証明する。

理由:

```text
Ledger
  = ΣGood ρ(pk) μ(pk) - ΣBad μ(pk)
 >= ρ₀ ΣGood μ(pk) - (BlockMass - GoodMass)
  = (1+ρ₀)GoodMass - BlockMass
```

reference mass は safe block pair 上で nonnegative/positive であることを使う。

そして Gate A の direct endpoint adapter と合成し、finite coverage criterion:

```text
RadialContactDeficit ε W A + BlockReferenceMass
  ≤ (1 + ρ₀) * GoodReferenceMass + η
```

なら

```text
RadialContactDeficit ε W B ≤ η
```

を証明する。

さらに `ρ₀ := cfzp032UniformReadyGoodEfficiencyFloor ε W τ` を代入した specialized theorem を可能なら公開する。

これが CFZP-032 の最終 API endpoint。

---

## 11. 数学的意味 / 次の frontier

CFZP-032 が Green なら、残る finite dominance 問題は

```text
Good hit exists?
```

ではなく、さらに明確に

```text
Does the Good set capture enough of the reference mass μ?
```

へ縮約される。

つまり本質は

```text
weighted Good reference-mass coverage
```

である。

CFZP-028 + CFZP-032 により fixed irrational prime では cofinally many uniformly-efficient Good hits は得られる。
しかし reference mass は exponent 方向に減衰するため、cofinal hit existence だけから weighted mass share は出ない。

次段ではここを誤魔化さず、

- fixed-prime exponent axis の reference-mass tail structure
- prime axis (`j=1`) の mass structure
- どちらが weighted coverage を供給し得るか

を exact finite / tail diagnostics で判定する。

---

## 12. Firewall / Gap

少なくとも次を OPEN に保つ。

```text
noIndependentWeightedGoodReferenceMassCoverageProvider
noPositiveWeightedDensityProvider
noPrimeAxisWeightedMassProvider
noAutomaticSubcriticalWindowProvider
noIndependentPrimePhaseRotationIrrationalityProvider
```

導入禁止:

- equidistribution theorem から即 weighted dominance とする shortcut
- positive natural density -> exponentially weighted mass share の無検証変換
- infinite prime-power sum
- PNT / Mertens / zero-density theorem 等の重装備
- limit exchange
- CFZP-018 unconditional provider
- RH conclusion

---

## 13. Completion gate

Green 条件:

```text
CFZP-031 direct EfficiencyLedger -> radial endpoint adapter: CLOSED
Good efficiency = prefactor efficiency * phase efficiency: CLOSED
phase envelope monotonicity: CLOSED
common subcritical quadratic coefficient normal forms: CLOSED
uniform positive phase-efficiency floor after explicit finite cell threshold: CLOSED
uniform positive prefactor-efficiency floor after explicit finite cell threshold: CLOSED
uniform positive ready-Good efficiency floor independent of p,j: CLOSED
CFZP-028 cofinal hit -> cofinal uniformly-efficient hit: CLOSED (conditional)
weighted Good reference-mass coverage -> ledger lower bound: CLOSED
finite weighted coverage criterion -> radial endpoint: CLOSED
weighted Good reference-mass coverage provider: OPEN / GAP
```

公開 import と roadmap 更新も行うこと。
