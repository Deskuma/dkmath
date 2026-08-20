# CFZP-0063 / CFZP-035

## exact signed efficiency normalization and coarse-reservoir obstruction — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-029: universal absolute event / Bad-debt envelope
- CFZP-031: reference mass `μ(p,j)` と binary efficiency ledger
- CFZP-032: uniform ready-Good efficiency floor と weighted coverage endpoint
- CFZP-033: exact sigma-decay factorization
- CFZP-034: prime-axis sigma-weight reservoir reduction、eligible / exceptional / higher-power split

CFZP-034 は数学的に Green だが、次の closure route に重要な情報損失が露出した。

034 の coarse prime-axis constants は

```text
C_low = 2 * T^2 * exp(a ε)
C_up  = 128 * (T+1)^2 * exp(a ε)
```

であり、`T > 0` なので `C_up / C_low > 64` 相当の大きな gap がある。
一方 CFZP-032 uniform ready-Good floor は

```text
ρ0 = exp(-2 a ε) * sin τ / 128
```

で、safe/subcritical/trimmed 条件では小さい正数である。

したがって

```text
Good -> +ρ μ
Bad  -> -μ
```

という binary universal-envelope ledger をさらに `C_low/C_up` へ落とした 034 reservoir を、そのまま prime-density 問題へ持っていくのは情報損失が大きすぎる。

**CFZP-035 の目的は、034 を否定することではない。034 の sufficient criterion が coarse であることを finite theorem として診断した上で、実際の branch-free event を reference mass で割った exact signed efficiency を first-class object にすることである。**

これにより各 prime-power pair を

```text
actual event = reference mass * exact signed score
```

と書き、Good 以外を一律 `-1` とせず実際の符号・大きさを保存する。

本段では prime distribution、Bertrand、PNT、Mertens、Dirichlet、density、infinite sum、limit exchange、CFZP-018 provider、RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaExactSignedEfficiencyNormalizationAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaExactSignedEfficiencyNormalizationAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisMassReservoirReductionAudit
import Mathlib.Tactic
```

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — coarse reservoir coefficient obstruction

まず 034 の theorem 自体を壊さず、coarse constants の比率だけを有限診断する。

最低限、次を証明する。

```text
64 * cfzp034PrimeAxisMassLowerConstant ε W
  < cfzp034PrimeAxisMassUpperConstant ε W
```

`T > 0` と exponential positivity のみで閉じること。

可能なら stronger / easier な形でもよい。
例えば

```text
2 * C_low < C_up
```

でも completion condition は満たすが、64 倍 gap が clean に閉じるならそちらを優先する。

さらに optional として、CFZP-032 floor が 1 未満であることを theorem 化してよい。

```text
0 < τ
τ ≤ π/4
0 < ε
=> cfzp032UniformReadyGoodEfficiencyFloor ε W τ < 1
```

または stronger に `< 1/128` が簡単なら閉じる。

### 目的

この Gate は「034 reservoir theorem が偽」という主張ではない。

```text
binary Bad=-1
+ coarse C_low/C_up
```

の二重 relaxation を closure の主エンジンにしない、という設計判断を Lean 側に記録するための diagnostic である。

`Good = Eligible` でも絶対に endpoint 不可能、など baseline/residual の符号まで仮定していない一般 no-go theorem を無理に作らないこと。

---

## 3. Gate B — exact signed efficiency

safe prime-power event の actual normalized score を導入する。

推奨:

```lean
noncomputable def cfzp035PrimePowerSignedEfficiency
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzpPrimePowerBranchFreeTrigEvent ε W p j /
    cfzp031PrimePowerReferenceMass ε W p j
```

safe assumptions

```text
0 < ε
ε < log 2
Nat.Prime p
0 < j
```

の下で reference mass positivity を使い、exact identity を閉じる。

```text
cfzpPrimePowerBranchFreeTrigEvent ε W p j
  = cfzp031PrimePowerReferenceMass ε W p j
      * cfzp035PrimePowerSignedEfficiency ε W p j
```

multiplication order は Lean が楽な形でよい。

### absolute bound

CFZP-029:

```text
|branchFreeTrigEvent| <= badDebtEnvelope
```

CFZP-031:

```text
referenceMass = badDebtEnvelope
```

を使い、

```text
|cfzp035PrimePowerSignedEfficiency ε W p j| <= 1
```

を証明する。

さらに adapters:

```text
-1 <= SignedEfficiency
SignedEfficiency <= 1
```

も置いてよい。

**この score は binary certificate score ではなく actual event / μ であることを docstring で明記する。**

---

## 4. Gate C — ready Good lower bound is a lower bound of the actual score

既存 ready Good credit は actual event の lower bound である。

CFZP-030/027 の theorem と

```text
GoodLocalCredit = ReadyGoodEfficiency * ReferenceMass
```

を使い、safe/subcritical ready hit の下で

```text
cfzp031ReadyGoodEfficiency ε W p j k τ
  <= cfzp035PrimePowerSignedEfficiency ε W p j
```

を証明する。

reference mass positivity で割る。

次に CFZP-034 の generic uniform-cell adapterを再利用し、

```text
Cfzp032UniformReadyCell ε W p j k τ
ready hit
=> UniformReadyGoodEfficiencyFloor ε W τ
   <= SignedEfficiency ε W p j
```

を閉じる。

prime-axis specialization:

```text
Prime p
Cfzp034PrimeAxisMassEligible ε p
k >= 1
ready third-quadrant hit at j=1
=> UniformReadyGoodEfficiencyFloor ε W τ
   <= SignedEfficiency ε W p 1
```

も public theorem にする。

これにより 032/034 Good theorem が actual signed score の certified positive floor であることが明確になる。

---

## 5. Gate D — exact signed-efficiency finite block ledger

034 と同じ pair block support を使う。

```lean
noncomputable def cfzp035SignedEfficiencyBlock
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  ∑ pk ∈ cfzp024PrimePowerPairBlockSupport A B,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
      cfzp035PrimePowerSignedEfficiency ε W pk.1 (pk.2 + 1)
```

`A ≤ B` の canonical block 上で各 pair は prime / positive exponent なので、Gate B を項別に使える。

### exact event block equality

既存 branch-free trig ledger / pulse block / block-support theoremのうち一番 clean な API を再利用して、以下のいずれかを閉じる。

第一候補:

```text
cfzp035SignedEfficiencyBlock ε W A B
  = cfzpPrimePowerBranchFreeTrigLedger ε W B
      - cfzpPrimePowerBranchFreeTrigLedger ε W A
```

第二候補として既存 pulse-block API がより clean なら

```text
cfzp035SignedEfficiencyBlock ε W A B
  = cfzp022VonMangoldtPulseBlock ε W A B
```

でもよい。

**重要なのは、新しい analytic theorem を作ることではなく、actual finite event sum と exact signed-efficiency sum が同一であること。**

block support の set-difference identity が必要なら CFZP-020/022 の既存 support monotonicity を優先して使い、同じ support theory を再実装しない。

---

## 6. Gate E — exact radial recurrence by signed score

safe frequency regimeで既存

```text
RadialDeficit X = ZeroCutoffBaseline - BranchFreeTrigLedger X
```

または pulse-block telescoping を使い、

```text
RadialDeficit B
  = RadialDeficit A - cfzp035SignedEfficiencyBlock ε W A B
```

を exact に証明する。

そこから endpoint adapter:

```lean
theorem cfzp035SignedEfficiencyBlock_bound_implies_radialContactDeficit_le
    ...
    (h :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A <=
        cfzp035SignedEfficiencyBlock ε W A B + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B <= η := by
  ...
```

を閉じる。

可能なら iff:

```text
RadialDeficit B <= η
<-> RadialDeficit A <= SignedEfficiencyBlock + η
```

も置いてよい。

この Gate が 035 の主要 endpoint である。

---

## 7. Gate F — exact three-way signed decomposition

CFZP-034 の exact supports:

```text
EligiblePrimeAxis
ExceptionalPrimeAxis
HigherPower
```

を再利用する。

各 support に対する exact signed sums を定義する。

例:

```lean
noncomputable def cfzp035SignedEfficiencyMassOn
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ pk ∈ S,
    cfzp031PrimePowerReferenceMass ε W pk.1 (pk.2 + 1) *
      cfzp035PrimePowerSignedEfficiency ε W pk.1 (pk.2 + 1)
```

これを helper にしてもよい。

exact:

```text
SignedEfficiencyBlock
  = EligiblePrimeAxisSigned
    + ExceptionalPrimeAxisSigned
    + HigherPowerSigned
```

を `Finset.sum_union` と 034 の union/disjoint theoremから閉じる。

ここでは exceptional/higher residual を absolute debt envelope に戻さない。
実際の signed contribution のまま保持する。

endpoint:

```text
RadialDeficit A
  <= EligibleSigned + ExceptionalSigned + HigherSigned + η
=> RadialDeficit B <= η
```

を Gate E の adapter として置く。

これにより 034 で explicit gap だった residual elimination は、035 の exact signed routeでは「必ず elimination しなければならない対象」ではなくなる。

---

## 8. Gate G — exact prime-axis sigma-weighted signed amplitude

CFZP-033 の exact factorizationを coarse constants に落とさず使う。

prime axis `j=1` に対し signed contribution は

```text
ReferenceMass(p,1) * SignedEfficiency(p,1)
```

であり、033 から exact に

```text
PrimeAxisSigmaWeight(p)
  * [
      2 * log p
      * exp(a ε)
      * ReducedShape(log p)
      * SignedEfficiency(p,1)
    ]
```

へ分解できる。

bracket 内を first-class amplitude として定義する。

候補:

```lean
noncomputable def cfzp035PrimeAxisSignedAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) *
    Real.exp ((cfzpModePhaseAbscissa W) * ε) *
    cfzp033ReferenceMassReducedShape ε W (Real.log (p : ℝ)) *
    cfzp035PrimePowerSignedEfficiency ε W p 1
```

そして safe prime `p` について exact:

```text
branchFreeTrigEvent ε W p 1
  = cfzp034PrimeAxisSigmaWeight W p
      * cfzp035PrimeAxisSignedAmplitude ε W p
```

または `ReferenceMass * SignedEfficiency = ...` の形でもよい。

eligible prime-axis support 上の finite sumについて

```text
EligiblePrimeAxisSigned
  = Σ pk in Eligible,
      PrimeAxisSigmaWeight(pk.1) * PrimeAxisSignedAmplitude(pk.1)
```

を exact に閉じる。

**ここでは amplitude の平均符号・density・distribution は主張しない。**

この exact weighted signed form が次段の prime-log phase analysis の正本になる。

---

## 9. Binary envelope との関係を firewall 化

031 binary occupancy score は削除・変更しない。

035 では次を明確に区別する。

```text
CFZP-031 score:
  certificate relaxation
  Good => +ReadyGoodEfficiency
  Bad  => -1

CFZP-035 score:
  exact actual event / reference mass
  always in [-1,1]
  ready Good => positive floor
```

可能なら ready Good pair について

```text
cfzp031OccupancyScore ... <= cfzp035PrimePowerSignedEfficiency ...
```

のような adapter を証明してよいが、関数引数が不自然なら無理に作らない。

completion priority は actual score exactness と radial block identityである。

---

## 10. Roadmap update

`0000-CFZP-roadmap.md` に CFZP-035 section を追加する。

最低限:

```text
coarse C_low/C_up reservoir gap diagnostic: CLOSED
exact signed efficiency event/referenceMass: CLOSED
signed efficiency absolute bound [-1,1]: CLOSED
ready Good efficiency <= actual signed efficiency: CLOSED
prime-axis uniform floor <= actual signed efficiency: CLOSED
exact signed-efficiency block event sum: CLOSED
exact signed block radial recurrence: CLOSED
three-way signed support decomposition: CLOSED
prime-axis exact sigma-weighted signed amplitude: CLOSED
prime-log signed phase dominance provider: OPEN / GAP
automatic subcritical window provider: OPEN / GAP
```

実装結果に合わせて wording を調整してよい。

---

## 11. Firewall / 禁止事項

CFZP-035 では以下を導入しない。

- PNT
- Mertens
- Dirichlet theorem
- Bertrand-based prime cell hit theorem
- prime-log equidistribution / density
- irrationality provider の無条件化
- infinite prime sum
- summability / divergence
- limit exchange
- exceptional/higher-power contribution を 0 と置くこと
- actual signed score を non-Good 上で `-1` と置くこと
- automatic weighted dominance provider
- CFZP-018 provider
- global RH conclusion

Gap は例えば:

```lean
inductive Cfzp035ExactSignedEfficiencyNormalizationGap : Prop
  | noPrimeAxisSignedScoreDominanceProvider
  | noPrimeLogSignedPhaseDistributionProvider
  | noAutomaticSubcriticalWindowProvider
```

程度でよい。

---

## 12. 完了条件

最優先は以下。

1. `SignedEfficiency = actual event / referenceMass`。
2. `actual event = referenceMass * SignedEfficiency` exact。
3. `|SignedEfficiency| <= 1`。
4. ready Good efficiency / uniform floor が actual signed efficiency の lower bound。
5. finite block signed-efficiency sum = actual branch-free event block exact。
6. `RadialDeficit B = RadialDeficit A - SignedEfficiencyBlock` exact。
7. 034 three-way supports に沿う exact signed decomposition。
8. prime axisで `sigmaWeight * SignedAmplitude` exact factorization。

**この段の狙いは、prime distribution を解くことではなく、distribution theorem が最終的に評価すべき対象を coarse binary debt ではなく exact signed phase amplitude に置き換えることである。**
