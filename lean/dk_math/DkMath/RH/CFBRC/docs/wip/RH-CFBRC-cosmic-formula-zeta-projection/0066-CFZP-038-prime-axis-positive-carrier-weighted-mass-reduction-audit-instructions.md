# CFZP-0066 / CFZP-038

## prime-axis positive-carrier weighted mass reduction — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-034: prime-axis sigma-weighted reference-mass reservoir
- CFZP-035: exact signed efficiency / exact signed block / radial recurrence
- CFZP-036: sigma-stripped prime-axis amplitude = periodic carrier + `K/u` remainder
- CFZP-037: uniform positive/negative carrier arcs, late remainder absorption, prime-log target intervals, positive prime-event transport

CFZP-037 は Green-A。current source で特に次が CLOSED:

```text
Cfzp037CarrierPositiveArcData
cfzp037PositiveArcLeft
cfzp037PositiveArcRight
cfzp037_exists_late_positive_arc_index
cfzp037_positive_arc_coordinate_amplitude_ge_margin_half
cfzp037PositivePrimeIntervalLeft
cfzp037PositivePrimeIntervalRight
cfzp037PositiveArcMultiplicativeRatio
cfzp037_prime_log_mem_positive_arc_iff_mem_exp_interval
Cfzp037PrimeAxisPositiveArcHitAt
cfzp037PrimeAxisEvent_ge_sigmaWeight_mul_margin_of_positiveArcHit
cfzp037PrimeAxisEvent_pos_of_positiveArcHit
cfzp037PositiveArcPrimeSigmaWeightMass
```

また CFZP-035 では actual event の exact ledger が既に CLOSED:

```text
cfzp035PrimePowerBranchFreeTrigEvent_eq_referenceMass_mul
cfzp035PrimePowerSignedEfficiency_lower_bound
cfzp035SignedEfficiencyMassOn
cfzp035SignedEfficiencyBlock
cfzp035SignedEfficiencyBlock_eq_branchFreeTrigEventBlock
cfzp035RadialContactDeficit_eq_sub_signedEfficiencyBlock
cfzp035SignedEfficiencyBlock_bound_implies_radialContactDeficit_le
cfzp035SignedEfficiencyBlock_eq_three_way_split
cfzp035EligiblePrimeAxisSignedEfficiencyMass_eq_weightedAmplitude
```

CFZP-034 には finite pair support と sigma weight がある:

```text
cfzp034EligiblePrimeAxisPairBlockSupport
cfzp034ExceptionalPrimeAxisPairBlockSupport
cfzp034HigherPowerPairBlockSupport
cfzp034ExceptionalPrimeAxisReferenceMass
cfzp034HigherPowerReferenceMass
cfzp034PrimeAxisSigmaWeight
cfzp034PrimeAxisSigmaWeightSum
cfzp034PrimeAxisMassUpperConstant
cfzp034PrimeAxisSigmaWeightSum_upper
cfzp034_rectangleSigma_gt_half
```

**CFZP-038 の目的は、037 の positive carrier prime hits を 035 の exact signed ledger に直接入れ、有限 prime-axis block の正寄与を sigma-weighted mass として抽出すること。arc 外の項は signed efficiency の universal lower bound `-1` により reference mass を有限 debt envelope として保持する。さらに単一 positive arc の prime cardinality を sigma-weighted mass lower bound に変換し、次段の arithmetic provider を「prime が1個あるか」ではなく「positive arcs がどれだけ sigma-weighted prime mass を捕獲するか」に固定する。**

重要:

- 037 の positive carrier certificate と 027 の `ReadyThirdQuadrantHit` は別物。
- **positive carrier hit から `ReadyThirdQuadrantHit` を捏造しない。**
- 本段の main endpoint は 034 の ready-Good endpoint ではなく、035 の exact signed block recurrence を使う。
- 「各 arc に prime が1個」は main provider にしない。周期セルごと1個だけなら sigma weight は一般に幾何減衰し得るため、必要なのは finite weighted mass / count-to-mass control。

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、positive density、infinite sums、summability、limit exchange、`σ < 1` の無根拠導入、exceptional/higher-power residual elimination、CFZP-018 provider、RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisPositiveCarrierWeightedMassAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisPositiveCarrierWeightedMassAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisPeriodicCarrierArcGeometryAudit
import Mathlib.Tactic
```

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — positive-arc Good pair support

034 の eligible prime-axis pair support は `pk.2 = 0` を内部に持つ。
037 の positive arc hit を filter して、035 signed ledger と直接互換な Good pair support を作る。

まず単一 cell:

```lean
def cfzp038PositiveArcGoodPairSupportAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n A B : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (cfzp034EligiblePrimeAxisPairBlockSupport ε A B).filter
    (fun pk => Cfzp037PrimeAxisPositiveArcHitAt ε W arc n pk.1)
```

有限 cell window 用:

```lean
def cfzp038PositiveArcGoodPairSupport
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (N₀ N₁ A B : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (cfzp034EligiblePrimeAxisPairBlockSupport ε A B).filter
    (fun pk => ∃ n ∈ Finset.Icc N₀ N₁,
      Cfzp037PrimeAxisPositiveArcHitAt ε W arc n pk.1)
```

証明:

```text
GoodAt(n) ⊆ eligible prime-axis block support
Good(N₀,N₁) ⊆ eligible prime-axis block support
```

および membership elimination API:

```text
pk ∈ Good -> eligible pk
pk ∈ Good -> ∃ n ∈ Icc N₀ N₁, positiveArcHit n pk.1
```

を用意する。

同じ prime を複数 cell が捕獲した場合も pair support 上では一度だけ数える。cell ごとの cardinality を後で加算する際に disjointness を勝手に仮定しない。

---

## 3. Gate B — late Good hit gives exact signed-mass credit

`Nlate ≤ N₀ ≤ n` と 037 の late provider

```lean
hlate : ∀ m, Nlate ≤ m →
  cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
    cfzp037PositiveArcLeft arc m
```

を仮定する。

`pk ∈ Good` なら、witness cell `n` を取り、

```lean
cfzp037PrimeAxisEvent_ge_sigmaWeight_mul_margin_of_positiveArcHit
```

から

```text
sigmaWeight(pk.1) * (arc.margin/2)
<= event(pk.1, 1)
```

を得る。

eligible prime-axis support では `pk.2 = 0` なので、035 の signed mass term

```text
referenceMass(pk.1, pk.2+1) * signedEfficiency(pk.1, pk.2+1)
```

は exact に `event(pk.1,1)`。

したがって finite Good sum theorem を閉じる:

```lean
theorem cfzp038GoodSigmaWeight_credit_le_signedMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    {Nlate N₀ N₁ A B : ℕ}
    (hNlate : Nlate ≤ N₀)
    (hlate : ∀ m, Nlate ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc m)
    (hAB : A ≤ B) :
    (arc.margin / 2) *
        cfzp034PrimeAxisSigmaWeightSum W
          (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) ≤
      cfzp035SignedEfficiencyMassOn ε W
        (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) := by
  ...
```

積の順序は Lean の simp が楽な方でよい。

ここは 027 ready-cell API を一切使わないこと。

---

## 4. Gate C — universal finite debt envelope for arbitrary block subsets

CFZP-035 の

```lean
cfzp035PrimePowerSignedEfficiency_lower_bound
```

は safe prime-power mode で score `>= -1`。
reference mass は positive。

したがって canonical block support の任意 subset `S` に対し、

```lean
theorem cfzp038SignedMass_ge_neg_referenceMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ cfzp024PrimePowerPairBlockSupport A B) :
    -cfzp032GoodReferenceMass ε W S ≤
      cfzp035SignedEfficiencyMassOn ε W S := by
  ...
```

を閉じる。

これは「Bad は実際に負」という主張ではない。符号不明項の worst-case finite lower envelope が `-referenceMass` というだけ。

この generic theorem から residual specialization:

```text
-cfzp034ExceptionalPrimeAxisReferenceMass ε W A B
<= signedMass(exceptional support)

-cfzp034HigherPowerReferenceMass ε W A B
<= signedMass(higher-power support)
```

を得る。

---

## 5. Gate D — eligible support = Good + complement Bad

定義:

```lean
def cfzp038PositiveArcBadPairSupport
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (N₀ N₁ A B : ℕ) : Finset (ℕ × ℕ) :=
  cfzp034EligiblePrimeAxisPairBlockSupport ε A B \
    cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B
```

Lean syntax は `\` / `sdiff` の current Finset API に合わせる。

証明:

```text
Good ∪ Bad = eligible
Disjoint Good Bad
Bad ⊆ eligible
```

これにより exact signed split:

```text
signedMass(eligible) = signedMass(Good) + signedMass(Bad)
```

を閉じる。

さらに exact sigma-weight split:

```text
weightSum(eligible) = weightSum(Good) + weightSum(Bad)
```

も閉じる。

---

## 6. Gate E — exact carrier-reservoir endpoint without subcritical/ready-cell assumptions

まず最も強く、coarse sigma upper constant を使わない endpoint を作る。

Good は Gate B で positive credit:

```text
signedMass(Good) >= (margin/2) * GoodWeight
```

Bad は Gate C で:

```text
signedMass(Bad) >= - ReferenceMass(Bad)
```

exceptional / higher-power も Gate C で named reference residual を debt envelope とする。

従って次の finite reservoir condition が radial endpoint に十分であることを証明する:

```lean
theorem cfzp038PositiveCarrierExactReservoir_implies_radialContactDeficit_le
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    {Nlate N₀ N₁ A B : ℕ}
    (hAB : A ≤ B)
    (hNlate : Nlate ≤ N₀)
    (hlate : ∀ m, Nlate ≤ m →
      cfzp037RemainderAbsorptionThreshold ε W arc.margin ≤
        cfzp037PositiveArcLeft arc m)
    (hreservoir :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp032GoodReferenceMass ε W
          (cfzp038PositiveArcBadPairSupport ε W arc N₀ N₁ A B) +
        cfzp034ExceptionalPrimeAxisReferenceMass ε W A B +
        cfzp034HigherPowerReferenceMass ε W A B ≤
      (arc.margin / 2) *
        cfzp034PrimeAxisSigmaWeightSum W
          (cfzp038PositiveArcGoodPairSupport ε W arc N₀ N₁ A B) + η) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η := by
  ...
```

証明の spine:

1. `cfzp035SignedEfficiencyBlock_eq_three_way_split`
2. eligible signed mass を Good+Bad へ exact split
3. Gate B の Good credit
4. Gate C の Bad / exceptional / higher residual lower bounds
5. `cfzp035SignedEfficiencyBlock_bound_implies_radialContactDeficit_le`

これが **CFZP-038 の main completion target**。

利点:

- `Cfzp027SubcriticalPhaseAspect W` 不要
- `ReadyThirdQuadrantHit` 不要
- `k`, `τ`, uniform ready-cell floor 不要
- actual signed event を直接使う

---

## 7. Gate F — sigma-only coarse corollary

次に 034 の finite upper comparisonを使い、Bad reference mass を sigma weight だけで置換する optional corollary を作る。

`Bad ⊆ eligible` なので、`hsub : Cfzp027SubcriticalPhaseAspect W` の下で

```text
ReferenceMass(Bad)
<= C_up * WeightSum(Bad)
```

を `cfzp034PrimeAxisSigmaWeightSum_upper` から得る。

従って:

```text
G_A
+ exceptionalReferenceMass
+ higherPowerReferenceMass
+ C_up * BadWeight
<= (margin/2) * GoodWeight + η
```

なら radial endpoint。

さらに

```text
TotalEligibleWeight = GoodWeight + BadWeight
```

を用いて等価に近い sufficient form:

```text
G_A
+ exceptionalReferenceMass
+ higherPowerReferenceMass
+ C_up * TotalEligibleWeight
<= (C_up + margin/2) * GoodWeight + η
```

から endpoint を出す theorem も作る。

候補 theorem:

```text
cfzp038PositiveCarrierSigmaReservoir_implies_radialContactDeficit_le
cfzp038PositiveCarrierTotalWeightReservoir_implies_radialContactDeficit_le
```

これは 034 ready-Good theorem のコピーではなく、037 exact carrier hit + 035 signed ledger からの別 route である。

---

## 8. Gate G — right-end sigma floor on a single positive cell

ここから arithmetic provider の入力を有限に具体化する。

定義:

```lean
noncomputable def cfzp038PositiveArcRightSigmaWeight
    (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n : ℕ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * cfzp037PositiveArcRight arc n)
```

`cfzp034_rectangleSigma_gt_half W` から `0 < σ` を得る。

positive arc hit:

```text
log p <= PositiveArcRight(n)
```

なので exponent の order reversal に注意して

```lean
theorem cfzp038PositiveArcRightSigmaWeight_le_primeWeight
    ...
    (hhit : Cfzp037PrimeAxisPositiveArcHitAt ε W arc n p) :
    cfzp038PositiveArcRightSigmaWeight W arc n ≤
      cfzp034PrimeAxisSigmaWeight W p := by
  ...
```

を閉じる。

right sigma floor は strictly positive も証明する。

---

## 9. Gate H — finite cardinality -> sigma-weighted mass

単一 cell の Good support `GoodAt(n)` について Gate G を sum し、

```lean
theorem cfzp038_card_mul_rightSigmaWeight_le_goodWeightAt
    ... :
    ((cfzp038PositiveArcGoodPairSupportAt ε W arc n A B).card : ℝ) *
        cfzp038PositiveArcRightSigmaWeight W arc n ≤
      cfzp034PrimeAxisSigmaWeightSum W
        (cfzp038PositiveArcGoodPairSupportAt ε W arc n A B) := by
  ...
```

を閉じる。

これが「prime count certificate」を「weighted mass certificate」へ変換する finite adapter。

さらに Gate B と組み合わせて、late cell なら

```text
(card GoodAt(n) : ℝ)
* rightSigmaWeight(n)
* (margin/2)
<= signedMass(GoodAt(n))
```

まで出してよい。

**ここでは cardinality の下界そのものは証明しない。**

---

## 10. Gate I — optional finite count-certificate adapter

外部算術 theorem を将来差し込める型だけ用意する。

例えば:

```lean
def Cfzp038PositiveArcPrimeCountCertificateAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (arc : Cfzp037CarrierPositiveArcData ε W)
    (n A B : ℕ) (C : ℝ) : Prop :=
  C ≤ (cfzp038PositiveArcGoodPairSupportAt ε W arc n A B).card
```

あるいは cast を含む real-valued lower bound にしてもよい。

count certificate + Gate H から

```text
C * exp(-σ*Right_n) <= GoodWeightAt(n)
```

を有限 theorem として閉じる。

もし growth-shaped adapter を置くなら `σ < 1` を **明示的 hypothesis** として受け取ること。current source から自動導出できない上側制約を追加しない。

例えば count lower が将来

```text
c * exp(Left_n) / Left_n <= card GoodAt(n)
```

として供給された場合にのみ、

```text
GoodWeightAt(n)
>= c * exp(Left_n - σ*Right_n) / Left_n
```

へ変換する finite algebraic adapter は可。

ただし PNT 等を本段で provider として import/使用しない。

---

## 11. Gate J — arithmetic frontier を型として固定

本段終了時点で本当の未証明対象を明示する。

最低限、次のどちらかを Prop として first-class にしてよい:

```text
positive arcs の Good sigma weight が Bad debt + residuals を有限 block で上回る
```

または main theorem の `hreservoir` をそのまま provider predicate 化する。

Gap 例:

```lean
inductive Cfzp038PrimeAxisPositiveCarrierWeightedMassGap : Prop
  | noPositiveArcPrimeCountProvider
  | noPositiveArcSigmaWeightedMassDominanceProvider
  | noPrimeLogWeightedDistributionProvider
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination
  | noAutomaticSubcriticalWindowProvider
```

`noPrimeInEveryPositiveArcProvider` は残してもよいが、**それだけでは closure provider として不足**であることを docstring / roadmap に明記する。

---

## 12. 禁止事項 / firewall

CFZP-038 では次を導入しない。

- PNT
- Mertens
- Dirichlet
- Bertrand を fixed-ratio interval provider として無条件使用
- prime reciprocal divergence
- prime-log equidistribution
- positive density
- infinite sums / summability
- limit exchange
- `σ < 1` の無根拠導出
- positive carrier hit ⇒ `ReadyThirdQuadrantHit` の偽接続
- residual mass が消えるという主張
- CFZP-018 provider
- global RH

全 theorem は finite support / finite sum のまま閉じる。

---

## 13. roadmap 更新

`0000-CFZP-roadmap.md` に CFZP-038 を追記し、少なくとも次を区別する。

```text
positive-arc Good pair support: CLOSED
late positive hit -> sigma-weighted actual-event credit: CLOSED
universal signed debt envelope: CLOSED
eligible Good/Bad exact split: CLOSED
exact positive-carrier reservoir -> radial endpoint: CLOSED
sigma-only Good/Bad reservoir reduction: CLOSED if implemented
right-end sigma floor: CLOSED
finite cardinality -> weighted mass adapter: CLOSED
prime count lower bound in carrier cells: OPEN / GAP
positive-arc weighted mass dominance: OPEN / GAP
prime-log weighted distribution: OPEN / GAP
exceptional/higher-power residual elimination: OPEN / GAP
infinite prime distribution / global RH: OUT OF SCOPE
```

---

## 14. 検証

最低限:

```bash
lake build DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisPositiveCarrierWeightedMassAudit
lake build DkMath.RH
git diff --check
```

新規 `sorry`, `axiom`, `native_decide` を入れない。

---

## 15. CFZP-038 の完了判定

Green 条件:

1. 037 positive carrier hits が finite pair support 上の Good set に exact に入る
2. late Good sigma-weighted credit が 035 signed mass へ直接下界される
3. arbitrary subset signed mass に `-referenceMass` universal lower envelope がある
4. eligible prime axis が Good/Bad に exact 分割される
5. residuals を消さずに exact carrier-reservoir endpoint が閉じる
6. 可能なら Bad reference mass を sigma weight へ落とす coarse corollary が閉じる
7. single-cell cardinality が right-end sigma floor 経由で weighted mass に変換される
8. prime count / weighted distribution provider は明示 Gap のまま

この段が Green になった後、CFZP-039 は実装結果を見て選ぶ。

第一候補は、**finite multiplicative prime interval count / weighted occupancy provider の既存 Mathlib・既存 DkMath 資産監査**。ただし CFZP-038 の exact reservoir coefficient を見ずに PNT や density へ飛ばないこと。
