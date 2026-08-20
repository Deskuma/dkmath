# CFZP-0047 / CFZP-020

## cutoff-frontier signed-mass increment audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-018: prime-threshold approximate-reach frontier — Green-A
- CFZP-019: branch-free prime-power signed-mass budget — Green-A
- CFZP-006U/V/W/Y: prime-power finite ledger / branch-free boundary / sign-cell / phase-cell adapters

CFZP-019 で、safe-frequency regime `0 < ε < log 2` において有限 radial deficit は

```text
G_X = baseline + negativeDebt_X - positiveMass_X
```

へ exact に分解され、CFZP-018 の arbitrary-slack approximate reach は

```text
∀ η > 0, ∀ N, ∃ X ≥ N,
  baseline + negativeDebt_X ≤ positiveMass_X + η
```

という signed-mass budget と exact に同定された。

さらに 006Y の local phase-cell sign theorem は、各 prime-power event に対して

```text
event ≥ 0  -> local negative debt = 0
event ≤ 0  -> local positive mass = 0
```

まで transport 済みである。

しかし現在の API は `X` までの cumulative mass/debt だけであり、cutoff を `X -> X+1` と進めたときに何が新規に ledger へ加わるかが first-class になっていない。

本段の目的は、canonical prime-power pair support の cutoff frontier を導入し、positive mass / negative debt / signed ledger / radial deficit を one-step recurrence に変換することである。

これにより local phase-cell sign を「一つの event の符号」から「次の cutoff step が deficit を下げるか上げるか」へ正確に接続する。

本段では global budget provider、phase equidistribution、universal phase-cell coverage、asymptotic density、joint limit、limit exchange、RH は証明しない。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSignedMassCutoffFrontierIncrementAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaSignedMassCutoffFrontierIncrementAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaBranchFreePrimePowerSignedMassBudgetAudit
import Mathlib.Tactic
```

必要なら canonical support の定義元を直接 import してよいが、既存 transitively-imported API で足りるなら増やさない。

---

## 2. Gate A — pair-support cutoff monotonicity

まず current definition of

```lean
pascalPrimePowerPairSupportUpTo X
```

と

```lean
mem_pascalPrimePowerPairSupportUpTo_iff
```

を確認し、`X ≤ Y` なら support inclusion が成り立つことを public theorem にする。

目標 shape:

```lean
theorem cfzp020PrimePowerPairSupportUpTo_mono
    {X Y : ℕ} (hXY : X ≤ Y) :
    pascalPrimePowerPairSupportUpTo X ⊆
      pascalPrimePowerPairSupportUpTo Y := by
  ...
```

既存に同値 API があれば再利用する。なければ membership characterization から直接証明する。

この theorem は後続 Finset sum monotonicity の土台なので first-class に残す。

---

## 3. Gate B — one-step cutoff frontier

`X` から `X+1` で新しく入る pair support を定義する。

推奨:

```lean
noncomputable def cfzp020PrimePowerCutoffFrontier
    (X : ℕ) : Finset (ℕ × ℕ) :=
  pascalPrimePowerPairSupportUpTo (X + 1) \
    pascalPrimePowerPairSupportUpTo X
```

証明すること:

```text
frontier(X) ⊆ support(X+1)
support(X) と frontier(X) は disjoint
support(X+1) = support(X) ∪ frontier(X)
```

Finset の既存 `sdiff` / subset API を優先する。

### optional arithmetic sharpening

membership API から短く閉じられる場合のみ、frontier element が exact new prime-power label を持つこと、すなわち概念的に

```text
p^(j+1) = X+1
```

へ sharpen する。

ここは本段の必須 gate ではない。証明が support definition の内部詳細に深く依存するなら次段へ送る。

---

## 4. Gate C — frontier positive mass / negative debt

019 の one-event mass/debt を frontier 上で合計する。

推奨 definitions:

```lean
noncomputable def cfzp020FrontierPositiveEventMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ pk ∈ cfzp020PrimePowerCutoffFrontier X,
    cfzp019PrimePowerEventPositiveMass ε W pk.1 (pk.2 + 1)

noncomputable def cfzp020FrontierNegativeEventDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ pk ∈ cfzp020PrimePowerCutoffFrontier X,
    cfzp019PrimePowerEventNegativeDebt ε W pk.1 (pk.2 + 1)
```

双方の nonnegativity を証明する。

---

## 5. Gate D — cumulative mass/debt one-step recurrence

support partition を使い exact recurrence を証明する。

必須 theorem shape:

```text
positiveMass(X+1)
  = positiveMass(X) + frontierPositiveMass(X)

negativeDebt(X+1)
  = negativeDebt(X) + frontierNegativeDebt(X)
```

Lean theorem 名は repository naming convention に合わせる。

ここは algebraic exact identity であり、sign hypothesis を入れない。

---

## 6. Gate E — cutoff monotonicity

Gate D と frontier nonnegativity から

```text
positiveMass(X) ≤ positiveMass(X+1)
negativeDebt(X) ≤ negativeDebt(X+1)
```

を証明する。

さらに Gate A を直接使って、可能なら一般形

```text
X ≤ Y -> positiveMass(X) ≤ positiveMass(Y)
X ≤ Y -> negativeDebt(X) ≤ negativeDebt(Y)
```

も public theorem として閉じる。

重要:

```text
ledger = positiveMass - negativeDebt
```

なので、positive と debt が個別に monotone でも signed ledger 自体の monotonicity は推論しない。

この firewall を docstring か Gap section に明記する。

---

## 7. Gate F — signed ledger increment

019 の ledger identity と Gate D を合成して

```text
ledger(X+1) - ledger(X)
  = frontierPositiveMass(X) - frontierNegativeDebt(X)
```

を exact に証明する。

同値な additive shape

```text
ledger(X+1)
  = ledger(X)
      + frontierPositiveMass(X)
      - frontierNegativeDebt(X)
```

でもよい。できれば両方のうち downstream で使いやすい方を first-class theorem にする。

---

## 8. Gate G — radial-deficit recurrence

safe-frequency regime `0 < ε < log 2` で CFZP-019 の

```text
G_X = baseline + debt_X - mass_X
```

を使い、

```text
G_(X+1)
  = G_X + frontierNegativeDebt(X) - frontierPositiveMass(X)
```

を exact に証明する。

これは本段の中心 theorem とする。

概念的には

```text
positive frontier mass = deficit repayment
negative frontier debt  = deficit increase
```

である。

---

## 9. Gate H — frontier sign adapters

frontier 上の全 event が nonnegative なら

```text
frontierNegativeDebt(X) = 0
```

を証明する。

同様に全 event が nonpositive なら

```text
frontierPositiveMass(X) = 0
```

を証明する。

その結果、safe-frequency regime で

```text
all frontier events ≥ 0
  -> G_(X+1) ≤ G_X

all frontier events ≤ 0
  -> G_X ≤ G_(X+1)
```

を conditional theorem として閉じる。

006Y phase-cell hypotheses を frontier 全体へ直接要求する巨大 theorem は必須ではない。まずは

```text
∀ pk ∈ frontier(X), event(pk) ≥ 0
```

または

```text
∀ pk ∈ frontier(X), event(pk) ≤ 0
```

という clean local-to-frontier interface を置く。

006Y からこの interface への adapter が短く書けるなら追加してよい。

---

## 10. Gate I — empty frontier constancy

frontier が空なら

```text
positiveMass(X+1) = positiveMass(X)
negativeDebt(X+1) = negativeDebt(X)
ledger(X+1) = ledger(X)
G_(X+1) = G_X
```

を証明する。

これにより finite arithmetic evolution が実際には prime-power support の新規 event が現れる cutoff でのみ変化することを Lean API として露出する。

optional arithmetic sharpening `p^(j+1)=X+1` が閉じていれば、この statement はさらに明瞭になる。

---

## 11. Gate J — do not overclaim global reach

本段で次は証明しない:

```text
positiveMass grows faster than negativeDebt
signed ledger is monotone
frontier events are eventually all nonnegative
phase cells cover all prime powers
signed-mass budget is cofinally satisfied
CFZP-018 provider
finite-window criticality unconditionally
RH
```

one-step descent theorem があっても、それだけでは arbitrary-slack cofinal reach は出ない。

特に

```text
G_(X+1) ≤ G_X
```

が conditional に得られる場合でも、その条件が cofinally/evenually 成立する provider は別問題として残す。

---

## 12. Gap marker

本段の unresolved frontier は、例えば

```lean
inductive Cfzp020SignedMassCutoffIncrementGap : Prop
  | noIndependentCofinalFrontierNetPositiveMassProvider
```

のような marker としてよい。

これは nonexistence theorem ではなく、未解決 provider のラベルである。

---

## 13. Public export / roadmap

実装後:

1. `DkMath/RH.lean` に新規 module を import。
2. `0000-CFZP-roadmap.md` に CFZP-020 section を追加。
3. classification は、上記 finite algebraic / order-theoretic gates が閉じれば Green-A。

roadmap には少なくとも以下を明記する:

```text
pair-support cutoff monotonicity: CLOSED / OPEN
one-step frontier partition: CLOSED / OPEN
positive/debt one-step recurrence: CLOSED / OPEN
positive/debt cutoff monotonicity: CLOSED / OPEN
signed ledger frontier increment: CLOSED / OPEN
radial deficit one-step recurrence: CLOSED / OPEN
frontier event sign -> one-step deficit direction: CLOSED / OPEN
frontier sign provider / quantitative dominance: OPEN / GAP
cofinal signed-mass budget provider: OPEN / GAP
```

---

## 14. Verification

通常の project gate を実行する。

- focused Lean build
- `lake env lean DkMath/RH.lean`
- `lake build DkMath.RH`
- `git diff --check`
- 新規 module に `sorry`, `admit`, `axiom`, `native_decide`, `Complex.arg` を追加しない

ビルドが通った checkpoint は Lean が認めた事実として報告する。

---

## 15. 次段への観測メモ

CFZP-020 が閉じると unresolved analytic/arithmetic target は cumulative budget から one-step net flow へさらに分解される:

```text
ΔG_X = frontierDebt_X - frontierPositiveMass_X
```

したがって次の本質的候補は

```text
cofinally many/blockwise intervals で
  cumulative frontierPositiveMass
    >= cumulative frontierNegativeDebt + required baseline repayment
```

を作る quantitative block theorem である。

この段階で初めて phase-cell frequency / prime-power phase lattice / block coverage の量的情報を budget provider へ接続する。

CFZP-020 自身ではそこへ飛ばないこと。