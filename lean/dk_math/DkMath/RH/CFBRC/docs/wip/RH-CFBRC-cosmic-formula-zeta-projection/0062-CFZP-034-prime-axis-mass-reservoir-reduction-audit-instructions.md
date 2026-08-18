# CFZP-0062 / CFZP-034

## prime-axis mass reservoir reduction and finite residual decomposition — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-031: reference mass `μ(p,j)` と efficiency ledger
- CFZP-032: uniform ready-Good efficiency floor と weighted-coverage endpoint
- CFZP-033: `u=j*log p`、exact sigma-decay factorization、prime/exponent axis finite comparison

CFZP-033 により、safe/subcritical large-coordinate region で

```text
μ(p,1)  ~ finite constants * exp(-σ log p)
μ(p,j)  ~ finite constants * exp(-σ j log p) / j
```

が asymptotic notation なしの two-sided finite inequalities として得られた。

また既存 API では

```lean
cfzpModePhaseAbscissa W = W.rectangle.σ - 1/2
cfzpModePhaseAbscissa_pos W
```

なので `W.rectangle.σ > 1/2 > 0` は source から導ける。従って fixed-prime exponent axis は genuine exponential decay axis である。

一方 CFZP-032 の公開 uniform theorem は implementation convenience として `j ≥ 3` を使うが、その本質的 prefactor 条件は

```text
2ε ≤ phaseMagnitudeLeft = j*log p - ε.
```

prime axis `j=1` では

```text
3ε ≤ log p
```

で同じ prefactor floor を回収できる。

**CFZP-034 の目的は prime axis `j=1` を正式に開き直し、有限 block reference mass を

```text
eligible prime-axis mass
+ exceptional prime-axis mass
+ higher-prime-power residual mass
```

へ exact decomposition した上で、CFZP-032 weighted coverage を finite sigma-weighted prime-axis reservoir inequality へ reduction することである。**

本段では prime phase distribution provider、PNT、Mertens、Dirichlet、prime reciprocal divergence、infinite sums、limit exchange を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisMassReservoirReductionAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisMassReservoirReductionAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaReferenceMassAxisDiagnosticsAudit
import Mathlib.Tactic
```

公開 import `DkMath/RH.lean` と roadmap を更新する。

---

## 2. Gate A — sigma positivity and canonical prime-axis weight

既存 theorem `cfzpModePhaseAbscissa_pos W` と定義から、rectangle sigma の positivity を明示する adapter を置く。

目標:

```lean
theorem cfzp034_rectangleSigma_gt_half
    (W : PascalCenteredXiResidueTransportWindow) :
    (1 / 2 : ℝ) < W.rectangle.σ := by
  ...
```

必要なら `0 < W.rectangle.σ` も adapter 化する。

prime-axis reference weight:

```lean
noncomputable def cfzp034PrimeAxisSigmaWeight
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ))
```

prime `p` について

```text
0 < PrimeAxisSigmaWeight W p
PrimeAxisSigmaWeight W p < 1
```

を証明する。後者は `σ>0`, `log p>0` から直接閉じる。

無理に `p ^ (-σ)` / `rpow` へ変換しない。

---

## 3. Gate B — reopen the prime axis `j = 1`

CFZP-033 exact coordinate adapter を使い、large-prime prefactor threshold を first-class theorem にする。

中心 theorem:

```text
Nat.Prime p
3*ε ≤ log p
----------------
2*ε ≤ cfzpPrimePowerPhaseMagnitudeLeft ε p 1
```

推奨 theorem 名:

```lean
cfzp034_two_epsilon_le_primeAxisPhaseMagnitudeLeft
```

proof は

```text
phaseMagnitudeLeft ε p 1 = log p - ε
```

への exact rewrite + linarith でよい。

さらに CFZP-033 prime-axis mass comparison に必要な条件をまとめる finite predicate を置いてよい。

例:

```lean
def Cfzp034PrimeAxisMassEligible (ε : ℝ) (p : ℕ) : Prop :=
  3 * ε ≤ Real.log (p : ℝ) ∧
  1 ≤ Real.log (p : ℝ)
```

ここでは `Nat.Prime p` は support から得るため predicate に混ぜなくてもよい。

`3ε ≤ log p` から `2ε ≤ log p` も `0<ε` で回収し、CFZP-033 lower/upper theorem へ流す adapter を作る。

---

## 4. Gate C — prime-axis uniform Good efficiency

重要: CFZP-032 の theorem

```lean
cfzp032UniformReadyGoodEfficiencyFloor_le
```

は `j ≥ 3` を hardcode しているが、proof 内で本当に必要なのは

```text
large cell contract
2ε ≤ phaseMagnitudeLeft
```

である。

本段ではこの本質条件を prime axis `j=1` に対して回収する。

実装方針は二択:

1. 032 の低レベル lemmas
   - `cfzp032LargeCellEfficiencyReady_of_one_le`
   - `cfzp031PrefactorEfficiency_ge_exp_div_eight`
   - `cfzp032PhaseEfficiency_ge_sin_div_16`
   - `cfzp031ReadyGoodEfficiency_eq_prefactor_mul_phase`
   を再利用して prime-axis specialization を直接証明する。
2. proof duplication が大きい場合、新 module 内に generic adapter
   `..._of_uniformReadyCell`
   を一つ作り、それを `j=1` と `j≥3` の共通 source として使う。

既存 032 の公開 API を破壊的変更しないこと。

prime-axis target:

```text
0 < ε < log 2
Nat.Prime p
subcritical W
0 < τ ≤ π/4
Cfzp034PrimeAxisMassEligible ε p
1 ≤ k
Cfzp027PrimePowerReadyThirdQuadrantHit ε W p 1 k τ
--------------------------------------------------
cfzp032UniformReadyGoodEfficiencyFloor ε W τ
  ≤ cfzp031ReadyGoodEfficiency ε W p 1 k τ
```

これにより `j=1` は大素数側で 032 と同じ positive efficiency floor を持つ。

**CFZP-028 irrational rotation は fixed prime / varying j の theorem なので、ここへ誤接続しない。prime axis varying p の phase distribution は依然 GAP。**

---

## 5. Gate D — finite block support split by exponent axis

pair representation は exponent が `pk.2 + 1` なので prime axis は exactly

```text
pk.2 = 0
```

である。

既存

```lean
cfzp024PrimePowerPairBlockSupport A B
```

を filter して、少なくとも次を定義する。

```lean
def cfzp034PrimeAxisPairBlockSupport (A B : ℕ) : Finset (ℕ × ℕ) :=
  (cfzp024PrimePowerPairBlockSupport A B).filter fun pk => pk.2 = 0

def cfzp034HigherPowerPairBlockSupport (A B : ℕ) : Finset (ℕ × ℕ) :=
  (cfzp024PrimePowerPairBlockSupport A B).filter fun pk => pk.2 ≠ 0
```

exact partition:

```text
blockSupport = primeAxisSupport ∪ higherPowerSupport
Disjoint primeAxisSupport higherPowerSupport
```

を証明する。

さらに prime axis を eligibility で二分する。

```text
eligiblePrimeAxisSupport
exceptionalPrimeAxisSupport
```

where eligible iff `Cfzp034PrimeAxisMassEligible ε pk.1`。

最終的に exact three-way decomposition:

```text
BlockReferenceMass
  = EligiblePrimeAxisReferenceMass
  + ExceptionalPrimeAxisReferenceMass
  + HigherPowerReferenceMass
```

を theorem にする。

全て finite Finset sum で閉じる。

---

## 6. Gate E — sigma-weighted prime-axis mass comparison on finite supports

constants を first-class にしてよい。

候補:

```lean
noncomputable def cfzp034PrimeAxisMassLowerConstant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  2 * W.rectangle.T ^ 2 *
    Real.exp ((cfzpModePhaseAbscissa W) * ε)

noncomputable def cfzp034PrimeAxisMassUpperConstant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  128 * (W.rectangle.T + 1) ^ 2 *
    Real.exp ((cfzpModePhaseAbscissa W) * ε)
```

033 の actual constants と一致させる。

pair Finset `S` に対する weight sum:

```lean
noncomputable def cfzp034PrimeAxisSigmaWeightSum
    (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S, cfzp034PrimeAxisSigmaWeight W pk.1
```

`S` が eligible prime-axis support の subset なら、CFZP-033 lower/upper を項別に足して

```text
C_low * WeightSum(S)
  ≤ cfzp032GoodReferenceMass ε W S

cfzp032GoodReferenceMass ε W S
  ≤ C_up * WeightSum(S)
```

を証明する。

ここで `pk.2=0` から `pk.2+1=1` を simplify し、`cfzp033PrimeAxisReferenceMass` へ接続する。

---

## 7. Gate F — exact finite residual masses

次を first-class finite observables として定義する。

```text
EligiblePrimeAxisReferenceMass(A,B)
ExceptionalPrimeAxisReferenceMass(A,B)
HigherPowerReferenceMass(A,B)
```

Gate D の exact split に加え、eligible part について

```text
EligiblePrimeAxisReferenceMass
  ≤ C_up * EligiblePrimeAxisSigmaWeight
```

を証明する。

Good subset `Good ⊆ eligiblePrimeAxisSupport` について

```text
C_low * GoodPrimeAxisSigmaWeight
  ≤ GoodReferenceMass
```

を証明する。

`ExceptionalPrimeAxisReferenceMass` と `HigherPowerReferenceMass` は本段では勝手に捨てない。**exact finite residual として残す**。

これが重要な firewall である。

---

## 8. Gate G — prime-axis weighted reservoir endpoint reduction

固定 trim `τ` を使う Good prime-axis subset を考える。

```text
Good ⊆ eligiblePrimeAxisSupport
k : pair -> Nat
ready hit at j=1 for each Good pair
1 ≤ k(pk)
```

とする。

uniform efficiency floor:

```text
ρ₀ := cfzp032UniformReadyGoodEfficiencyFloor ε W τ > 0
```

を Gate C から全 Good pair に与える。

次の **finite sufficient criterion** を theorem として閉じる。

conceptual shape:

```text
G_A
+ ExceptionalPrimeAxisReferenceMass(A,B)
+ HigherPowerReferenceMass(A,B)
+ C_up * EligiblePrimeAxisSigmaWeight(A,B)
≤
(1 + ρ₀) * C_low * GoodPrimeAxisSigmaWeight(Good)
+ η
```

なら

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η.
```

proof spine:

1. exact three-way BlockReferenceMass decomposition。
2. eligible prime-axis mass upper bound by `C_up * total eligible weight`。
3. GoodReferenceMass lower bound by `C_low * Good weight`。
4. Gate C から `ρ₀ ≤ ReadyGoodEfficiency`。
5. `cfzp032_weightedCoverage_implies_radialContactDeficit_le` へ流す。

この theorem が CFZP-034 の主 endpoint。

ここで新しい abstract provider Prop を作るのではなく、**具体的 finite inequality そのもの**を入力にする。

---

## 9. Gate H — higher-power geometric suppression diagnostic

CFZP-033 の fixed-prime upper bound を sigma weight の power として読み直す。

まず exact exponential adapter を狙う。

```text
exp(-σ * (j * log p))
  = (cfzp034PrimeAxisSigmaWeight W p)^j
```

Lean では `Real.exp_nat_mul` 等、現 Mathlib で最も短い theorem を使う。

したがって large-coordinate hypotheses の下で

```text
μ(p,j)
  ≤ C_up / j * (PrimeAxisSigmaWeight W p)^j.
```

を adapter theorem として得る。

`0 < q < 1` は Gate A で既知。

実装が簡潔なら finite exponent set `Jset` に対し

```text
Σ j∈Jset, 2≤j, μ(p,j)
  ≤ C_up * Σ j∈Jset, q^j
```

まで証明してよい。

さらに finite geometric-series closed form が Mathlib API で短く閉じるなら

```text
Σ_{2≤j≤J} q^j ≤ q^2 / (1-q)
```

相当まで進めてよい。

ただし **この tail diagnostic は Gate G の completion を阻害しないこと**。support reindexing や geometric-series API が重い場合は one-pair power adapter までで Green とする。

---

## 10. What CFZP-034 should expose

本段終了時の closure frontier を次の形まで剥く。

```text
prime-axis eligible weight reservoir
        ↓
which primes land in the Good third-quadrant phase cells?
        ↓
Good weighted sigma mass
        ↓
finite residuals:
  exceptional prime-axis mass
  higher-prime-power mass
        ↓
CFZP-032 weighted coverage
        ↓
radial contact endpoint
```

特に未解決の中心は

```text
Can sufficiently much weight exp(-σ log p)
be captured by primes whose T*log p phase lies in Good cells?
```

となる。

これは **prime phase distribution problem** であり、CFZP-028 の fixed-prime irrational rotation theorem とは別物である。

---

## 11. Firewall / explicit GAP

新しい Gap type または roadmap に、少なくとも以下を明記する。

```text
noPrimeAxisWeightedGoodPhaseOccupancyProvider
noPrimeLogPhaseDistributionProvider
noAutomaticWeightedCoverageProvider
noExceptionalPrimeAxisResidualElimination
noHigherPrimePowerResidualElimination
noAutomaticSubcriticalWindowProvider
```

また本段では以下を導入しない。

- PNT
- Mertens theorem
- Dirichlet theorem
- prime reciprocal divergence
- equidistribution of `log p mod period`
- positive density of Good primes
- infinite sums / tsum
- summability
- limit exchange
- CFZP-018 provider
- RH

`weighted phase occupancy` を仮定名だけ変えた provider wrapper として追加するのは禁止。

---

## 12. Completion criteria

CFZP-034 Green 条件:

```text
sigma > 1/2 adapter: CLOSED
prime-axis sigma weight positivity / <1: CLOSED
j=1 large-prime prefactor threshold 3ε≤log p: CLOSED
prime-axis uniform efficiency floor: CLOSED
block support prime-axis/higher-power exact split: CLOSED
eligible/exceptional prime-axis exact split: CLOSED
exact three-way reference-mass decomposition: CLOSED
eligible prime-axis finite sigma-weight upper bound: CLOSED
Good prime-axis finite sigma-weight lower bound: CLOSED
prime-axis weighted reservoir -> radial endpoint reduction: CLOSED
higher-power sigma-weight power normalization: CLOSED if practical
prime-log phase weighted occupancy provider: OPEN / GAP
```

focused build、`DkMath/RH.lean` build、full build を通す。

roadmap に CFZP-034 section を追加する。

---

## 13. Stop condition

CFZP-034 実装後はそこで停止し、次段 CFZP-035 を先に設計しない。

034 の actual finite reservoir theorem と residual decomposition をレビューしてから、次に

```text
prime log-phase weighted occupancy
```

を直接攻めるか、先に

```text
higher-power residual compression
```

を閉じるかを決める。
