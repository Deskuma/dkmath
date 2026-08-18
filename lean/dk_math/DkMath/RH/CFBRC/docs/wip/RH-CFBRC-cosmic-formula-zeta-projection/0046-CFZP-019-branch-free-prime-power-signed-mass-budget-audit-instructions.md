# CFZP-0046 / CFZP-019

## branch-free prime-power signed-mass budget audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-015: arithmetic radial-domination margin frontier — Green-A
- CFZP-016: cofinal radial-domination frontier minimization — Green-A
- CFZP-017: radial-margin prime-threshold decomposition — Green-A
- CFZP-018: prime-threshold approximate-reach frontier — Green-A

CFZP-018 により、fixed positive `ε` では現在の closure route に必要な prime-side 条件は exact threshold crossing ではなく、任意の normalized slack `δ > 0` に対する

```text
arbitrarily late X with
  NormalizedPrimeThreshold - δ ≤ NormalizedPrimeContribution(X)
```

まで弱められた。

さらに既存 CS22 と exact に

```text
Cfzp018CofinalPrimeThresholdApproximateReachAt ε W
  ↔ PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W
```

であり、finite radial deficit は

```text
G_X = π * (T - P_X)
```

である。

一方、CFZP-006U/V/Y 系では同じ finite prime interaction が canonical prime-power pair support 上の branch-free real event ledger として既に exact に書かれている。

safe-frequency regime `0 < ε < log 2` では

```text
AggregateRayInteractionEnergy(X)
  = cfzpPrimePowerBranchFreeTrigLedger ε W X
```

かつ

```text
G_X
  = cfzpZeroCutoffRadialContactBaseline ε W
      - cfzpPrimePowerBranchFreeTrigLedger ε W X
```

である。

CFZP-006Y は個々の prime-power event に対して phase-cell 条件から `event ≥ 0` または `event ≤ 0` を与える。しかし **局所 sign は global magnitude reach ではない**。

本段の目的はこの論理的隙間を exact に露出することである。

各 branch-free prime-power event を

```text
positive mass
negative debt
```

へ canonical に分解し、有限 ledger を

```text
ledger = positiveMass - negativeDebt
```

と書く。そして CFZP-018 の arbitrary-slack reach を

```text
baseline + negativeDebt ≤ positiveMass + slack
```

という cofinal signed-mass budget と exact に同定する。

これにより、006W/006Y の phase-cell sign theorem が何を消せるか、そして RH closure のためにさらに何の **量的 coverage** が必要かを Lean の型として固定する。

本段では independent budget provider、phase equidistribution、universal phase-cell coverage、RH は証明しない。

---

## 1. 新規 module

推奨:

`DkMath.RH.CFBRC.CosmicFormulaZetaBranchFreePrimePowerSignedMassBudgetAudit`

file:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaBranchFreePrimePowerSignedMassBudgetAudit.lean`

最低 import 候補:

- `DkMath.RH.CFBRC.CosmicFormulaZetaPrimeThresholdApproximateReachFrontierAudit`
- `DkMath.RH.CFBRC.CosmicFormulaZetaSafeFrequencyTrigonometricPhaseBoundaryAudit`
- `DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit`
- `Mathlib.Tactic`

既存 event / ledger / pair-support / radial-contact API をそのまま使う。

同じ trigonometric event、same finite mode kernel、same pair support を別定義で再構築しない。

---

## 2. Gate A — one-event positive mass / negative debt

branch-free event

```lean
cfzpPrimePowerBranchFreeTrigEvent ε W p j : ℝ
```

に対し、正部分と負部分を algebraic に定義する。

推奨:

```lean
noncomputable def cfzp019PrimePowerEventPositiveMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  max (cfzpPrimePowerBranchFreeTrigEvent ε W p j) 0

noncomputable def cfzp019PrimePowerEventNegativeDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  max (-cfzpPrimePowerBranchFreeTrigEvent ε W p j) 0
```

名称は調整してよいが、意味を変えない。

最低限、次を証明する。

```text
0 ≤ PositiveMass(event)
0 ≤ NegativeDebt(event)
event = PositiveMass(event) - NegativeDebt(event)
```

候補 theorem:

```lean
theorem cfzp019PrimePowerEventPositiveMass_nonneg ...
theorem cfzp019PrimePowerEventNegativeDebt_nonneg ...
theorem cfzp019PrimePowerEvent_eq_positiveMass_sub_negativeDebt ...
```

`max` の API が不便なら `by_cases h : 0 ≤ event` で閉じてよい。

重要:

- positive mass / negative debt は **新しい sign assumption ではない**。
- 任意の実 event に対する canonical algebraic decomposition である。
- event が正であることを定義へ埋め込まない。

---

## 3. Gate B — local sign adapters

既存 CFZP-006W/Y の sign theorem を signed-mass coordinate へ transport する。

一般 adapter として少なくとも次を用意する。

```text
event ≥ 0
  -> PositiveMass = event
  -> NegativeDebt = 0

event ≤ 0
  -> PositiveMass = 0
  -> NegativeDebt = -event
```

候補:

```lean
theorem cfzp019PrimePowerEventPositiveMass_eq_of_nonneg ...
theorem cfzp019PrimePowerEventNegativeDebt_eq_zero_of_nonneg ...
theorem cfzp019PrimePowerEventPositiveMass_eq_zero_of_nonpos ...
theorem cfzp019PrimePowerEventNegativeDebt_eq_neg_of_nonpos ...
```

そのうえで、可能なら CFZP-006Y の public theorem

```lean
cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_nonposPhaseCellCoverage
cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_nonnegPhaseCellCoverage
```

から直接 companion を出す。

例えば nonnegative-event 側では

```text
phase-cell coverage
  -> NegativeDebt(event) = 0
  -> PositiveMass(event) = event
```

nonpositive-event 側では

```text
phase-cell coverage
  -> PositiveMass(event) = 0
  -> NegativeDebt(event) = -event
```

を得る。

ただし 006Y の phase hypotheses を新しい provider structure に詰め替えない。既存 theorem を adapter として再利用する。

この Gate の意味は **phase cell が local debt/mass のどちらを消すか** を明示することであり、global reach を主張することではない。

---

## 4. Gate C — finite positive mass / negative debt ledgers

`cfzpPrimePowerBranchFreeTrigLedger` と全く同じ pair support

```lean
pascalPrimePowerPairSupportUpTo X
```

上で二つの有限量を定義する。

概念 shape:

```lean
noncomputable def cfzp019BranchFreePositiveEventMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
    cfzp019PrimePowerEventPositiveMass ε W pk.1 (pk.2 + 1)

noncomputable def cfzp019BranchFreeNegativeEventDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
    cfzp019PrimePowerEventNegativeDebt ε W pk.1 (pk.2 + 1)
```

次を証明する。

```text
0 ≤ PositiveEventMass_X
0 ≤ NegativeEventDebt_X
```

および本段の第一 exact identity:

```text
cfzpPrimePowerBranchFreeTrigLedger ε W X
  = PositiveEventMass_X - NegativeEventDebt_X
```

候補 theorem:

```lean
theorem cfzp019BranchFreeTrigLedger_eq_positiveMass_sub_negativeDebt ...
```

証明は `Finset.sum_congr` と Gate A の one-event identity を用いる。

support を filter して別 ledger を作る必要はない。

`max` による positive/negative part を使えば、未分類 event を落とさず exact decomposition を保持できる。

---

## 5. Gate D — radial deficit の exact signed-mass balance

safe-frequency regime

```text
0 < ε
ε < Real.log 2
```

で既存

```lean
cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
```

と Gate C を合成し、first-class theorem として

```text
G_X = baseline + NegativeDebt_X - PositiveMass_X
```

を出す。

推奨:

```lean
theorem cfzp019RadialContactDeficit_eq_baseline_add_debt_sub_positiveMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      cfzpZeroCutoffRadialContactBaseline ε W +
        cfzp019BranchFreeNegativeEventDebt ε W X -
        cfzp019BranchFreePositiveEventMass ε W X := by
  ...
```

係数や support を再推測しない。

既存 branch-free ledger が aggregate interaction と exact に同一であることを利用する。

---

## 6. Gate E — finite slack reach = signed-mass budget

Gate D から任意の geometric slack `η` について exact に

```text
G_X ≤ η
↔
baseline + NegativeDebt_X ≤ PositiveMass_X + η
```

を証明する。

候補:

```lean
theorem cfzp019RadialContactDeficit_le_iff_signedMassBudget
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ η ↔
      cfzpZeroCutoffRadialContactBaseline ε W +
          cfzp019BranchFreeNegativeEventDebt ε W X ≤
        cfzp019BranchFreePositiveEventMass ε W X + η := by
  ...
```

これは本段の中心 finite identity である。

意味は

```text
positive event mass
  pays
zero-cutoff baseline + negative event debt
  up to slack η.
```

ここで初めて local sign information と global magnitude frontier の間にある未解決量が見える。

---

## 7. Gate F — fixed-ε cofinal signed-mass budget

fixed `(ε,W)` で、arbitrary-slack budget を first-class proposition にする。

推奨:

```lean
def Cfzp019CofinalBranchFreeSignedMassBudgetAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
    cfzpZeroCutoffRadialContactBaseline ε W +
        cfzp019BranchFreeNegativeEventDebt ε W X ≤
      cfzp019BranchFreePositiveEventMass ε W X + η
```

これは exact threshold crossing provider ではない。

`η` は geometric radial-deficit units の slack とする。

normalized `δ` をここへ混ぜない。

---

## 8. Gate G — signed-mass budget と CS22 / CFZP-018 の exact equivalence

safe-frequency regime `0 < ε < log 2` で、まず

```text
Cfzp019CofinalBranchFreeSignedMassBudgetAt ε W
  ↔ PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W
```

を exact に証明する。

Gate E を点ごとに使えばよい。

その後 CFZP-018 の

```lean
cfzp018CofinalPrimeThresholdApproximateReachAt_iff_csf
```

を合成し、

```text
Cfzp019CofinalBranchFreeSignedMassBudgetAt ε W
  ↔ Cfzp018CofinalPrimeThresholdApproximateReachAt ε W
```

も公開する。

候補 theorem:

```lean
theorem cfzp019CofinalBranchFreeSignedMassBudgetAt_iff_contactZero ...
theorem cfzp019CofinalBranchFreeSignedMassBudgetAt_iff_cfzp018 ...
```

これにより 018 の abstract prime-threshold frontier が、canonical prime-power event の正質量と負債の budget へ exact に戻る。

重要:

- これは provider を証明したのではない。
- 同じ provider の **量的内部構造** を露出した theorem である。
- phase-cell sign からこの proposition を無条件には生成しない。

---

## 9. Gate H — sign-only firewall at aggregate level

phase-cell sign が何を与え、何を与えないかを有限 theorem として固定する。

一般 finite adapter を用意してよい。

例えば

```lean
/-- If every witnessed event in the finite support is nonnegative,
then the total negative debt vanishes. -/
theorem cfzp019NegativeEventDebt_eq_zero_of_all_events_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hall : ∀ pk ∈ pascalPrimePowerPairSupportUpTo X,
      0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1)) :
    cfzp019BranchFreeNegativeEventDebt ε W X = 0 := by
  ...
```

さらに同じ仮定で

```text
PositiveEventMass_X = branchFreeTrigLedger_X
```

を出してよい。

しかしそこから

```text
baseline ≤ PositiveEventMass_X + η
```

は導かない。

**全 event nonnegative でさえ magnitude reach は別問題** であることを設計上保持する。

必要なら純実数 countermodel を置いてよい。

例:

```text
0 ≤ mass
but
baseline - η > mass
```

となる実数 witness を示し、nonnegative mass alone does not pay an arbitrary positive baseline と固定する。

この countermodel は actual zeta event の反例ではなく、sign-only inference の論理 firewall であると docstring に明記する。

---

## 10. Gate I — safe-frequency restriction は outer ε -> 0+ で無償

branch-free trigonometric API は `ε < log 2` を要求する。

しかし

```text
Real.log 2 > 0
```

なので、`𝓝[>] 0` では

```text
ε < Real.log 2
```

は eventually 成立する。

これを first-class helper として証明する。

候補:

```lean
theorem eventually_epsilon_lt_log_two :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < Real.log 2 := by
  ...
```

Mathlib の `Iio_mem_nhds` / `mem_nhdsWithin_iff_exists_mem_nhds_inter` 等、現行 API に合う最小証明を使う。

新しい analytic theorem は不要。

ここで重要なのは、safe-frequency restriction が global closure route を強めないことを Lean 上で固定することである。

---

## 11. Gate J — doubly-cofinal safe signed-mass budget

外側 epsilon を含む proposition を定義する。

推奨:

```lean
def Cfzp019DoublyCofinalSafeBranchFreeSignedMassBudget
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ ε : ℝ in 𝓝[>] 0,
    0 < ε ∧ ε < Real.log 2 ∧
      Cfzp019CofinalBranchFreeSignedMassBudgetAt ε W
```

Gate I により safe restriction は eventually true なので、CFZP-018 の doubly-cofinal provider と exact equivalence を狙う。

```text
Cfzp019DoublyCofinalSafeBranchFreeSignedMassBudget W
  ↔ Cfzp018DoublyCofinalPrimeThresholdApproximateReach W
```

forward は fixed-ε equivalence を `Frequently.mono` で transport する。

reverse は CFZP-018 の frequent set と `Eventually (ε < log 2)` を交差させる。

outer condition を `Eventually` に強めない。

この theorem が閉じれば、safe-frequency phase-event language を使うこと自体には最終 frontier 上の strength cost がない。

---

## 12. Gate K — conditional finite-window closure companion

Gate J の equivalence を使い、signed-mass provider から既存 CFZP-018 closure theorem へ直接 adapter を出す。

候補:

```lean
theorem cfzp019FiniteWindowZeros_critical_of_doublyCofinalSafeSignedMassBudget
    (W : PascalCenteredXiResidueTransportWindow)
    (hbudget : Cfzp019DoublyCofinalSafeBranchFreeSignedMassBudget W) :
    ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
      ρ.re = (1 : ℝ) / 2 := by
  ...
```

証明は CFZP-018 theorem への adapter に留める。

fixed second-moment defect の zero-side theorem を再証明しない。

ここでも provider existence は仮定された引数であり、無条件 RH を主張しない。

---

## 13. Gate L — sharpened arithmetic frontier

本段完了後の unresolved condition は、概念的に

```text
cofinally ε -> 0+ in the safe-frequency regime,
  for every η > 0,
    arbitrarily late X satisfies

      zeroCutoffBaseline(ε,W)
        + accumulatedNegativeEventDebt(ε,W,X)
      ≤ accumulatedPositiveEventMass(ε,W,X) + η.
```

である。

Gap marker 例:

```lean
inductive Cfzp019BranchFreeSignedMassBudgetGap : Prop
  | noIndependentDoublyCofinalSignedMassBudgetProvider
```

provider inhabitant は作らない。

これは CFZP-018 frontier の rename だけではなく、**canonical prime-power event ごとの支払い構造へ分解した frontier** である。

今後の analytic phase route が証明すべき対象は、単なる sign coverage ではなく

```text
positive event mass growth / recurrence
versus
negative event debt + fixed baseline
```

の量的 budget である。

---

## 14. 次段への観測ポイント

CFZP-019 実装時には、次のどれが既存 API からさらに無条件に出るかを必ず監査し、report / roadmap に記録する。

1. `PositiveEventMass_X` または `NegativeEventDebt_X` の cutoff 更新則。
2. pair-support に新しい prime-power event が一つ加わる場合の exact increment。
3. event sign が既知の cell では debt increment が zero になる theorem。
4. support inclusion `X ≤ Y` と positive/debt mass の単調性。
   - 各 summand は非負なので、support inclusion が既存にあれば mass/debt 自体は monotone になり得る。
   - ただし **net ledger は monotone とは限らない**。
5. positive/debt のどちらかに existing finite envelope / bound が既に存在しないか。

これらが軽量に閉じるなら本段へ含めてよい。

特に 4 は次段の攻略上重要である。positive mass と negative debt を分離した結果、それぞれは非負 summand の累積量となる。これにより signed ledger 自体にはなかった monotone structure が露出する可能性がある。

ただし support inclusion の証明を新しい大仕事にしない。既存 API がなければ frontier note に留める。

---

## 15. Firewall

導入禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- infinite Euler product
- zero counting
- phase equidistribution の仮定
- universal phase-cell coverage provider
- exact threshold-crossing provider
- unconditional approximate-reach provider
- unconditional signed-mass budget provider
- joint `(ε,X)` limit
- limit exchange
- contour relocation の新規仮定
- common-baseline reach の rename
- global RH
- RH-equivalent theorem を prime-side arithmetic lemma の証明に逆利用すること

また次を混同しない。

```text
local event sign:
  event ≥ 0  or  event ≤ 0

finite algebraic decomposition:
  ledger = positiveMass - negativeDebt

cofinal magnitude budget:
  baseline + negativeDebt ≤ positiveMass + η

CFZP-018 normalized reach:
  threshold - δ ≤ normalizedPrimeContribution
```

四者は別レイヤーである。

---

## 16. Public import / roadmap

実装完了後:

1. `DkMath/RH.lean` に新 module import を追加。
2. `0000-CFZP-roadmap.md` に CFZP-019 section を追加。
3. classification は、finite signed-mass identities、safe fixed-ε equivalence、outer safe-frequency equivalence、conditional finite-window adapter が閉じれば Green-A。
4. roadmap には少なくとも次を明記する。

```text
one-event positive/negative decomposition: CLOSED
branch-free ledger = positive mass - negative debt: CLOSED
finite radial deficit = baseline + debt - positive mass: CLOSED
slack radial contact <-> signed-mass budget: CLOSED
safe fixed-ε signed-mass budget <-> CFZP-018 approximate reach: CLOSED
safe-frequency restriction near ε -> 0+: NO STRENGTH COST
006Y local phase-cell sign -> local mass/debt elimination: CLOSED
local sign -> global signed-mass budget: OPEN / NOT INFERRED
independent doubly-cofinal signed-mass budget provider: OPEN / GAP
```

新しい finite monotonicity / increment theorem が得られた場合は別途記録する。

---

## 17. Green suite

最低限:

- 新 module focused build
- `lake build DkMath.RH`
- project の標準 full build / test が通常フローに含まれるなら実施
- `git diff --check`
- 新規 `sorry`, `admit`, `axiom`, `native_decide` なし
- 新規 `Complex.arg` なし
- global complex-log branch の新規導入なし

GitHub Actions は必須ではない。local Green を正本とする。

---

## 18. Exit condition

CFZP-019 の終了条件は、CFZP-018 の abstract arbitrary-slack prime-threshold frontier を、既存 branch-free prime-power event ledger の canonical signed-mass budgetへ exact に展開することである。

最終 surface は概念的に

```text
CFZP-018 approximate prime-threshold reach
  ↕ exact
CS22 cofinal radial contact zero
  ↕ exact, safe frequency
branch-free prime-power signed-mass budget

baseline + negativeDebt
  ≤ positiveMass + arbitrary slack
```

となる。

ここまで閉じた後の本当の未解決問題は、

> prime-power phase geometry が positive event mass を十分に再来・蓄積させ、negative debt と fixed baseline を arbitrary slack まで cofinally 支払うことを、独立 arithmetic/analytic theorem として証明できるか。

である。

次 checkpoint はこの quantitative provider の内部をさらに分解する。

特に CFZP-019 で positive mass / negative debt の個別 monotonicityや cutoff increment が露出した場合、CFZP-020 ではそれを用いて

```text
positive mass recurrence / growth
negative debt control
```

のどちらが本当の残敵かを切り分ける。

**sign theorem を増やすだけの方向へ戻らないこと。**