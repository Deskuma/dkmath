# CFZP-0049 / CFZP-022

## finite pulse-block compensation audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-018: arbitrary-slack prime-threshold reach — Green-A
- CFZP-019: branch-free signed-mass budget — Green-A
- CFZP-020: cutoff-frontier signed-mass recurrence — Green-A
- CFZP-021: von Mangoldt pulse compression — Green-A
- CS22: cofinal radial-contact closure

CFZP-021 により、整数 cutoff の one-step flow は

```text
G_(X+1) = G_X - Pulse(X+1)
```

へ exact に圧縮された。ここで

```text
Pulse(n) = 2 * Λ(n) * FiniteModeKernel(n)
```

であり、非 prime-power 時刻では pulse は 0、prime-power 時刻では既存 branch-free prime-power event と一致する。

本段では一歩ずつの recurrence を有限区間 `(A,B]` へ telescope し、後続 block が現在の radial deficit をどれだけ支払ったかを first-class にする。

中心像は

```text
PulseBlock(A,B) = Σ_{A < n ≤ B} Pulse(n)
G_B = G_A - PulseBlock(A,B)
```

である。従って

```text
G_B ≤ η
  <->
G_A ≤ PulseBlock(A,B) + η
```

となる。

これにより CS22 の cofinal radial-contact provider を、

> 任意の現在 cutoff `A` と任意 slack `η > 0` に対して、ある有限 future block `(A,B]` が現在 deficit `G_A` を `η` まで支払う

という finite local compensation contract に exact に変換する。

さらに CFZP-019 の cumulative positive mass / negative debt を block increment にして、

```text
PulseBlock(A,B)
  = BlockPositiveMass(A,B) - BlockNegativeDebt(A,B)
```

および

```text
G_A + BlockNegativeDebt(A,B)
  ≤ BlockPositiveMass(A,B) + η
```

という局所 signed-mass budget へ落とす。

本段ではこの compensation の独立 provider は証明しない。phase equidistribution、universal phase-cell coverage、asymptotic density、joint limit、limit exchange、global RH は導入しない。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFinitePulseBlockCompensationAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaFinitePulseBlockCompensationAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaVonMangoldtPulseCompressionAudit
import Mathlib.Tactic
```

必要なら CS22 / CFZP-019 の定義元を直接 import してよいが、transitive public API で足りるなら増やさない。

---

## 2. Gate A — finite pulse block

自然数 cutoff `A,B` に対し、区間 `(A,B]` の pulse 総和を定義する。

推奨:

```lean
noncomputable def cfzp022VonMangoldtPulseBlock
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc A B,
    cfzp021VonMangoldtPulse ε W n
```

`Finset.Ioc` が proof ergonomics 上不利なら、同じ `(A,B]` を表す

```text
range(B+1) \ range(A+1)
```

等を使ってよい。ただし semantics は first-class docstring で固定する。

最低限証明すること:

```text
PulseBlock(A,A) = 0
PulseBlock(X,X+1) = Pulse(X+1)
```

可能なら `B ≤ A` なら block = 0 も追加する。

---

## 3. Gate B — aggregate block telescoping

CFZP-021 の successor recurrence を有限 induction で telescope し、`A ≤ B` のとき

```text
Aggregate(B)
  = Aggregate(A) + PulseBlock(A,B)
```

を証明する。

差分形も first-class に残してよい:

```text
Aggregate(B) - Aggregate(A)
  = PulseBlock(A,B)
```

既存 finite sum definition から直接 interval difference を出した方が短ければ、それでもよい。

infinite series は使用しない。

---

## 4. Gate C — branch-free ledger block telescoping

safe-frequency regime `0 < ε < log 2` で、CFZP-021 の ledger/pulse identity を telescope して

```text
branchFreeLedger(B)
  = branchFreeLedger(A) + PulseBlock(A,B)
```

および

```text
branchFreeLedger(B) - branchFreeLedger(A)
  = PulseBlock(A,B)
```

を証明する。

これは finite equality のみであり、ledger monotonicity は主張しない。

---

## 5. Gate D — radial deficit finite-block telescope

中心 theorem。

`0 < ε` と `A ≤ B` の下で、可能なら safe-frequency 条件を要求せず raw radial recurrence から

```text
G_B = G_A - PulseBlock(A,B)
```

を証明する。

推奨 shape:

```lean
theorem cfzp022RadialContactDeficit_eq_sub_pulseBlock
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A -
        cfzp022VonMangoldtPulseBlock ε W A B := by
  ...
```

CFZP-021 の one-step theorem が safe `ε < log 2` を syntactically要求していても、基礎 `cfzpRadialContactDeficit_succ` が `0 < ε` のみで使えるならそちらから telescope する。

branch-free signed-mass bridgeに入るまでは不要な safe-frequency 制約を増やさない。

---

## 6. Gate E — finite block payment equivalence

Gate D から purely algebraic に、任意 `η : ℝ` について

```text
G_B ≤ η
  <->
G_A ≤ PulseBlock(A,B) + η
```

を証明する。

目標 theorem:

```lean
theorem cfzp022RadialContactDeficit_le_iff_pulseBlock_pays
    {ε η : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
        cfzp022VonMangoldtPulseBlock ε W A B + η := by
  ...
```

これが本段の主会計 identity である。

---

## 7. Gate F — block concatenation

`A ≤ B ≤ C` のとき

```text
PulseBlock(A,C)
  = PulseBlock(A,B) + PulseBlock(B,C)
```

を証明する。

Finset interval partition で閉じても、Gate B の aggregate difference を使って ring で閉じてもよい。

この theorem は次段で block partition / compensation chain を扱う基礎になる。

---

## 8. Gate G — block positive mass / negative debt

CFZP-019 の cumulative nonnegative quantitiesを block increment として定義する。

推奨:

```lean
noncomputable def cfzp022BlockPositiveEventMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  cfzp019BranchFreePositiveEventMass ε W B -
    cfzp019BranchFreePositiveEventMass ε W A

noncomputable def cfzp022BlockNegativeEventDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  cfzp019BranchFreeNegativeEventDebt ε W B -
    cfzp019BranchFreeNegativeEventDebt ε W A
```

`A ≤ B` の下で CFZP-020 monotonicity から双方 nonnegative を証明する。

そして safe-frequency regime で

```text
PulseBlock(A,B)
  = BlockPositiveEventMass(A,B)
      - BlockNegativeEventDebt(A,B)
```

を exact に証明する。

可能ならこの equality 自体は safe-frequency不要で、021/020 ledger identityから閉じられるか監査する。不要な仮定は外す。

---

## 9. Gate H — local signed block budget

Gate E/G から、`A ≤ B` の下で

```text
G_B ≤ η
  <->
G_A + BlockNegativeEventDebt(A,B)
  ≤ BlockPositiveEventMass(A,B) + η
```

を証明する。

これは CFZP-019 の global cumulative budget の **任意開始 cutoff版** である。

概念的には、future block の positive mass が

```text
current deficit + future negative debt
```

を slack `η` まで支払えば、その block endpoint で radial contact が達成される。

---

## 10. Gate I — cofinal finite pulse-block compensation

本段の主要 Prop を定義する。

推奨:

```lean
def Cfzp022CofinalFinitePulseBlockCompensationAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ A : ℕ,
    ∃ B : ℕ, A ≤ B ∧
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
        cfzp022VonMangoldtPulseBlock ε W A B + η
```

そして `0 < ε` の下で

```text
Cfzp022CofinalFinitePulseBlockCompensationAt ε W
  <->
PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W
```

を exact に証明する。

証明骨格:

### block compensation -> CS22

与えられた `η > 0`, `N` に対し `A := N` として compensation を使い `B ≥ N` を得る。Gate E により `G_B ≤ η`。

### CS22 -> block compensation

与えられた `η > 0`, `A` に対し CS22 から `B ≥ A`, `G_B ≤ η` を得る。Gate E で `G_A ≤ PulseBlock(A,B) + η`。

ここは新しい analytic assumption ではなく exact provider-coordinate change である。

---

## 11. Gate J — cofinal signed block budget

必要ならさらに named Prop を定義する:

```lean
def Cfzp022CofinalSignedPulseBlockBudgetAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ A : ℕ,
    ∃ B : ℕ, A ≤ B ∧
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp022BlockNegativeEventDebt ε W A B ≤
        cfzp022BlockPositiveEventMass ε W A B + η
```

safe-frequency regime で

```text
Cfzp022CofinalSignedPulseBlockBudgetAt
  <-> Cfzp022CofinalFinitePulseBlockCompensationAt
  <-> CS22 CofinalRadialContactZeroAt
  <-> CFZP-019 fixed-ε signed-mass budget
  <-> CFZP-018 fixed-ε approximate reach
```

まで transport する。

既存 theorem を再利用し、同じ cofinal proof を重複実装しない。

この Prop を作らない場合でも、Gate H の finite signed-budget theorem と Gate I の CS22 equivalence は必須。

---

## 12. Gate K — non-prime-power sparse support adapter (optional, high value)

proof cost が軽い場合のみ、PulseBlock が prime-power 時刻だけに支えられていることを finite theorem にする。

例:

```text
PulseBlock(A,B)
  = sum of Pulse(n) over n in (A,B] with IsPrimePow n
```

または、区間内に prime-power が存在しなければ

```text
PulseBlock(A,B) = 0
G_B = G_A
```

を証明する。

新しい prime-power predicate は作らず、CFZP-021 の `IsPrimePow` quiescence theoremを再利用する。

この optional gate が重ければ Green 条件に含めない。

---

## 13. Gate L — explicit remaining provider gap

独立 provider を導入しない。

Gap marker 例:

```lean
inductive Cfzp022FinitePulseBlockCompensationGap : Prop
  | noIndependentCofinalSignedPulseBlockBudgetProvider
```

次段の真の arithmetic/phase target は、任意 `η > 0` と開始 cutoff `A` に対してある有限 `B ≥ A` を構成し、

```text
G_A + BlockNegativeEventDebt(A,B)
  ≤ BlockPositiveEventMass(A,B) + η
```

を prime-power pulse / phase structure から与えることである。

---

## 14. firewalls

本段では以下を導入しない。

1. pulse の eventual / universal nonnegativity
2. branch-free ledger の monotonicity
3. prime-power phase の equidistribution
4. universal phase-cell coverage
5. density assumption
6. infinite Euler product / infinite prime-power sum
7. joint `(ε,X)` limit
8. limit exchange
9. cofinal block compensation の独立 provider
10. RH / finite-window criticality の無条件化

特に

```text
one positive pulse
```

や

```text
one nonnegative block
```

から cofinal compensation を推論しない。

---

## 15. exit condition

CFZP-022 Green の最低条件:

```text
finite PulseBlock(A,B): CLOSED
aggregate finite-block telescope: CLOSED
radial deficit finite-block telescope: CLOSED
G_B ≤ η <-> current deficit paid by PulseBlock + η: CLOSED
block concatenation: CLOSED
block positive/debt increments nonnegative for A ≤ B: CLOSED
PulseBlock = block positive mass - block debt: CLOSED
local signed block budget equivalence: CLOSED
cofinal block compensation <-> CS22 zero contact: CLOSED
safe block budget <-> CFZP-019/018 fixed-ε frontier: CLOSED (if named Prop added)
independent block compensation provider: OPEN / GAP
```

この段が閉じれば、closure frontier は

```text
arbitrary-slack reach
  -> signed cumulative budget
  -> one-step pulse flow
  -> finite future block compensation
  -> quantitative phase/prime-power block provider
```

まで圧縮される。

次段では representation を増やすのではなく、finite block 内で positive pulse mass が negative debt と current deficit を上回るための **実際の quantitative mechanism** を探索すること。