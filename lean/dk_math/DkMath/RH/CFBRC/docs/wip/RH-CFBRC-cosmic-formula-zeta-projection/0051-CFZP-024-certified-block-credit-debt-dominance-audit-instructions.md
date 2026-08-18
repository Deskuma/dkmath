# CFZP-0051 / CFZP-024

## certified block credit-debt dominance audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-019: branch-free signed-mass budget — Green-A
- CFZP-020: cutoff-frontier signed-mass recurrence — Green-A
- CFZP-021: von Mangoldt one-mode pulse compression — Green-A
- CFZP-022: finite pulse-block compensation — Green-A
- CFZP-023: quantitative prime-power pulse margin — Green-A

CFZP-022 により fixed-`ε` closure frontier は、有限 block `(A,B]` における

```text
G_B = G_A + BlockNegativeDebt(A,B) - BlockPositiveMass(A,B)
```

および

```text
G_B ≤ η
  <->
G_A + BlockNegativeDebt(A,B)
  ≤ BlockPositiveMass(A,B) + η
```

へ exact に圧縮された。

CFZP-023 は一つの prime-power pair `(p,j)` に対し、centered profile derivative の quantitative margin から

```text
credit(p,j,κ)
  = 2 * log(p) * CriticalScale(p^j) * κ
  ≤ PositiveEventMass(p,j)
```

を与え、absolute derivative envelope から

```text
NegativeEventDebt(p,j)
  ≤ 2 * log(p) * CriticalScale(p^j) * K
```

を与える。

本段ではこの one-event certificate を finite prime-power block 上で合算する。

重要なのは、良い pair `Good` 上では derivative-drop margin から event が nonnegative になるため、negative debt は **exact に 0** へ消せることである。従って debt envelope は block 全体ではなく `Bad = BlockSupport \ Good` にだけ課す。

中心形は

```text
CertifiedGoodCredit(A,B,Good,κ)
  ≤ BlockPositiveMass(A,B)

BlockNegativeDebt(A,B)
  ≤ CertifiedBadDebtEnvelope(A,B,Good,K)
```

であり、これらから

```text
G_A + CertifiedBadDebtEnvelope
  ≤ CertifiedGoodCredit + η
```

ならば

```text
G_B ≤ η
```

を得る。

これにより未解決 provider は、曖昧な `block dominance` ではなく、

> future block の Good prime-power credit が、現在 deficit と Bad prime-power debt envelope を支払える

という有限・定量的な算術/位相条件へ落ちる。

本段でもこの provider 自体は証明しない。phase equidistribution、density、uniform derivative margin、eventual positivity、infinite sum、joint limit、limit exchange、RH は導入しない。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaCertifiedBlockCreditDebtDominanceAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaCertifiedBlockCreditDebtDominanceAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaQuantitativePrimePowerPulseMarginAudit
import Mathlib.Tactic
```

transitive import で十分なら増やさない。

---

## 2. Gate A — canonical pair block support

CFZP-022 の block mass/debt は cumulative support difference で定義されている。
これを explicit finite support にする。

推奨:

```lean
def cfzp024PrimePowerPairBlockSupport (A B : ℕ) : Finset (ℕ × ℕ) :=
  pascalPrimePowerPairSupportUpTo B \
    pascalPrimePowerPairSupportUpTo A
```

`A ≤ B` の下で最低限:

```text
pk ∈ BlockSupport(A,B)
  -> pk ∈ support(B)
  -> pk ∉ support(A)
```

を public API にする。

可能なら label characterization も追加する:

```text
pk ∈ BlockSupport(A,B)
  -> A < primePowerPairLabel pk
  -> primePowerPairLabel pk ≤ B
```

既存 `mem_pascalPrimePowerPairSupportUpTo_iff`、CFZP-020 monotonicity、canonical injectivity を再利用する。

新しい prime-power predicate は発明しない。

---

## 3. Gate B — block mass/debt as exact support-difference sums

`A ≤ B` の下で CFZP-022 の block increments を exact finite sums に戻す。

必須概念形:

```text
BlockPositiveMass(A,B)
  = Σ pk in BlockSupport(A,B),
      PositiveEventMass(pk.1, pk.2+1)

BlockNegativeDebt(A,B)
  = Σ pk in BlockSupport(A,B),
      NegativeEventDebt(pk.1, pk.2+1)
```

CFZP-020 の support monotonicityと `Finset.sum_sdiff` / disjoint decomposition を優先する。

ここは以後の quantitative summation の基礎 API なので public theorem にする。

---

## 4. Gate C — Good / Bad finite split

任意の finite `Good : Finset (ℕ × ℕ)` を受け取り、

```text
Good ⊆ BlockSupport(A,B)
```

を仮定する。

Bad は

```lean
def cfzp024BadPrimePowerPairBlockSupport
    (A B : ℕ) (Good : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  cfzp024PrimePowerPairBlockSupport A B \ Good
```

等でよい。

最低限:

```text
BlockSupport = Good ∪ Bad
Disjoint Good Bad
Bad ⊆ BlockSupport
```

を固定する。

Good を「全 event が良い」と定義で固定しない。Good の選択は certificate hypothesis で与える。

---

## 5. Gate D — certified good credit

Good pair ごとの derivative margin を関数

```text
κ : ℕ × ℕ -> ℝ
```

で与える。

各 `pk ∈ Good` について

```text
0 ≤ κ pk
Cfzp023CenteredProfileDerivativeDropMargin
  ε W pk.1 (pk.2+1) (κ pk)
```

を仮定する。

Good credit を

```lean
noncomputable def cfzp024CertifiedGoodCredit
    (Good : Finset (ℕ × ℕ)) (κ : ℕ × ℕ → ℝ) : ℝ :=
  ∑ pk ∈ Good,
    2 * Real.log (pk.1 : ℝ) *
      cfzpModeCriticalScale (pk.1 ^ (pk.2 + 1)) * κ pk
```

の shape で定義する。必要なら `ε W` を引数に含めてもよいが、式自体に不要なら含めない。

`pk ∈ BlockSupport` から `Nat.Prime pk.1` と `0 < pk.2+1` を既存 membership API で回収し、CFZP-023 を各項へ適用する。

必須 theorem:

```text
CertifiedGoodCredit ≤ BlockPositiveMass(A,B)
```

注意:

- Good は block support の部分集合であること。
- `pk.2 + 1` の index convention を崩さない。
- `p^(j)` の `j` はここでは `pk.2 + 1`。

---

## 6. Gate E — Good debt vanishes exactly

Good pair 上では quantitative credit theoremから event nonnegative を得る。

従って CFZP-019 の one-event adapter を使い、各 Good pair について

```text
NegativeEventDebt(pk) = 0
```

を証明する。

Good 全体の debt sum が 0 である theorem を public にする。

ここでは `κ > 0` は不要。`0 ≤ κ` で credit lower bound 自体が nonnegative なので event nonnegative が得られるはずである。

CFZP-023 の `κ=0` sign theoremを使ってもよいが、一般 `κ≥0` の quantitative boundから直接閉じる方が依存が明瞭ならそちらを使う。

---

## 7. Gate F — certified bad debt envelope

Bad pair ごとの absolute derivative envelope を

```text
K : ℕ × ℕ -> ℝ
```

で与える。

各 `pk ∈ Bad` について

```text
0 ≤ K pk
Cfzp023CenteredProfileDerivativeAbsEnvelope
  ε W pk.1 (pk.2+1) (K pk)
```

を仮定する。

Bad debt envelope を

```lean
noncomputable def cfzp024CertifiedBadDebtEnvelope
    (Bad : Finset (ℕ × ℕ)) (K : ℕ × ℕ → ℝ) : ℝ :=
  ∑ pk ∈ Bad,
    2 * Real.log (pk.1 : ℝ) *
      cfzpModeCriticalScale (pk.1 ^ (pk.2 + 1)) * K pk
```

の shape で定義する。

CFZP-023 の negative-debt upper adapter を各 Bad pair に適用して、Good debt = 0 と合成し、必須 theorem:

```text
BlockNegativeDebt(A,B)
  ≤ CertifiedBadDebtEnvelope(Bad,K)
```

を閉じる。

これが本段の重要な sharpening である。Good pair は debt envelope に数えない。

---

## 8. Gate G — certified block dominance closes one finite payment

Gate D/F と CFZP-022 signed block budgetを合成する。

中心 theorem:

```text
G_A + CertifiedBadDebtEnvelope
  ≤ CertifiedGoodCredit + η

->
G_B ≤ η
```

推奨 theorem shape は引数が多くなりすぎるなら、certificate structure / bundled Prop を導入してよい。

例えば

```lean
structure Cfzp024FiniteBlockCertificate ... where
  Good : Finset (ℕ × ℕ)
  hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B
  κ : ℕ × ℕ → ℝ
  K : ℕ × ℕ → ℝ
  ...
```

のような構造を使ってよい。

ただし bundle の中に結論そのものを隠さない。certificate は per-pair margin/envelope data を持ち、dominance inequality は theorem/Prop として別に見えるようにする。

最低限 public に残す概念形:

```text
CertifiedBlockDominance(A,B,η)
  -> G_B ≤ η
```

---

## 9. Gate H — cofinal certified dominance provider interface

次の fixed-`ε` provider interface を定義する。

概念:

```text
for every η > 0 and every A,
  exists B ≥ A,
  exists finite Good subset and quantitative certificates,
  G_A + CertifiedBadDebtEnvelope
    ≤ CertifiedGoodCredit + η
```

名前候補:

```lean
def Cfzp024CofinalCertifiedBlockDominanceAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop := ...
```

そして safe-frequency regime で

```text
Cfzp024CofinalCertifiedBlockDominanceAt
  -> Cfzp022CofinalSignedPulseBlockBudgetAt
  -> PascalCenteredXiPrimeSideCofinalRadialContactZeroAt
  -> Cfzp018CofinalPrimeThresholdApproximateReachAt
```

を adapter theorem として閉じる。

可能なら直接 `Cfzp018...` まで bridge を一本用意する。

重要:

- implication のみでよい。
- reverse implication は主張しない。
- CS22/CFZP022 が derivative certificate の存在を与えるわけではない。

---

## 10. Gate I — optional cardinality compression

proof が短い場合のみ、次段の counting/density 攻略用に scalar compression を追加してよい。

例えば Good 各項について

```text
c ≤ credit(pk)
```

Bad 各項について

```text
envelope(pk) ≤ d
```

なら

```text
(card Good : ℝ) * c ≤ CertifiedGoodCredit
CertifiedBadDebtEnvelope ≤ (card Bad : ℝ) * d
```

を finite sum inequality で証明する。

これにより十分条件は概念的に

```text
G_A + card(Bad) * d
  ≤ card(Good) * c + η
```

へ落ちる。

ただし cast / cardinality proof が本体を汚すなら次段へ回し、Green の blocker にしない。

---

## 11. Gate J — firewalls

本段から次を導いてはならない:

```text
all sufficiently large pulses are positive
Good has positive density
Bad has zero density
phase centers are equidistributed
uniform κ > 0 exists
uniform K exists
CertifiedGoodCredit dominates automatically
cofinal compensation provider exists
RH
```

特に CFZP-022 cofinal compensation から derivative certificates の存在を reverse に推論しない。

`Good` の選択と `κ/K` は explicit finite certificate dataであり、それを供給する算術/位相 theorem は未解決である。

---

## 12. Gate K — explicit remaining Gap

Gap marker は例えば:

```lean
inductive Cfzp024CertifiedBlockCreditDebtDominanceGap : Prop
  | noIndependentCofinalCertifiedBlockDominanceProvider
```

とする。

必要なら docstring に、未解決内容を

```text
prime-power phase geometry must supply sufficiently many/large Good credits
while controlling the Bad debt envelope
```

と明記する。

---

## 13. Public import / roadmap

実装後:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaCertifiedBlockCreditDebtDominanceAudit
```

を `DkMath/RH.lean` に追加する。

roadmap に CFZP-024 section を追加し、最低限:

```text
pair block-support difference: CLOSED
block mass/debt exact finite sums: CLOSED
Good/Bad support split: CLOSED
Good quantitative credit sum <= positive block mass: CLOSED
Good debt vanishing: CLOSED
negative block debt <= Bad envelope: CLOSED
certified dominance -> finite radial payment: CLOSED
cofinal certified dominance -> CFZP-022/018: CLOSED / CONDITIONAL
independent certified-dominance provider: OPEN / GAP
```

を記録する。

---

## 14. Exit condition

Green 条件:

1. canonical block support `(A,B]` が exact に finite pair differenceとして固定される。
2. CFZP-022 block positive/debt がその support 上の exact sums に戻る。
3. Good subset の 023 derivative marginsを finite certified creditへ合算できる。
4. Good debt が exact に 0 へ消える。
5. Bad subset の 023 absolute envelopesを finite debt envelopeへ合算できる。
6. `BlockNegativeDebt ≤ BadEnvelope` が閉じる。
7. `CertifiedCredit ≤ BlockPositiveMass` が閉じる。
8. certified dominance inequality から `G_B ≤ η` が閉じる。
9. cofinal certified dominance から CFZP-022 / CS22 / CFZP-018 へ conditional bridge が閉じる。
10. provider 自体は Gap のまま残る。

この段が閉じれば、次の genuine frontier は representation ではない。

```text
どの prime-power phase centers が Good certificate を持つか
Good credit はどの程度の頻度/大きさで現れるか
Bad envelope の総量をどう抑えるか
```

という arithmetic/phase-distribution problem そのものになる。
