/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.ClassGroupBridge

#print "file: DkMath.FLT.Kummer.RegularPrimeRoute"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open DkMath.CosmicFormulaBinom

/-!
# Regular Prime Route — Kummer Targets から FLT 幹線への接続

## 目的

Kummer branch で定義した abstract targets を合成して、
DkMath FLT 幹線の `2m-pure` → FLT chain に接続する。

## 全体の chain 概略

```
  ClassGroupPTorsionFree                     (concrete target)
        ↓
    GenericAlgebraicIdentity                   (thinnest theorem-level kernel)
        ↓
    EquationOnlyFactorizationIdentity          (Nat specialization)
        ↓
    PrimeSpecialization                        (where primality first enters)
        ↓
    AbstractFactorizationIdentity              (prime+equation wrapper)
        ↓
    CounterexampleSpecialization               (pack audit layer)
        ↓
    PureFactorizationIdentity                  (prime-ge5 wrapper)
        ↓
    GapDivisibleSpecialization                 (where gap-divisible first enters)
        ↓
    FactorizationIdentity                      (specialized wrapper)
        ↓
    IdealEquationPackaging                     (Dedekind / integrality side)
        ↓
    IdealFactorization                         (factorization wrapper)
        ↓
    IdealProductPthPower                       (Dedekind / ideal arithmetic side)
        ↓
    IdealClassPTorsionWitness                  (class-group side)
        ↓
    PTorsionAnnihilation                       (generic ClassGroup API)
        ↓
    PrincipalIdealExtraction                   (Dedekind / class-group API side)
        ↓
    IdealPthPower                              (Stage 1 composition)
        ↓
    UnitNormalization                          (abstract stage)
        ↓
    NormDescent                                (abstract stage)
        ↓
    CyclotomicPrincipalization                 (3-stage composition)
        ↓
    GapDivisibleBranch                         (= Principalization)
        ↕
    Regular branch + GapDivisible branch       (by_cases q ∣ (z-y))
        ↓
    2m-pure                                    (no so#rry ✅)
        ↓
    2m-global                                  (from 2m-pure, auto)
        ↓
    PthRootCore → GNReducedGap → 無限降下法    (existing chain, no so#rry)
        ↓
  FLTPrimeGe5Target                          ✅
```

## open kernel の整理

Kummer branch 導入後、gap-divisible 側の Stage 1a は
DkMath-native local core により **CLOSED** した:
1. ~~Regular branch~~: `qAdicGapReductionRegularBranch_of_global` **CLOSED** ✅
  → witness R の自動構成が ZMod unit 理論で完了。
2. ~~Gap-divisible Stage 1a (FLT-useful chain)~~: `cyclotomicEquationFactorizationIdentity_of_diophantineEquation` **CLOSED** ✅
  → `CyclotomicLocalEquationFactorizationCoreTarget` から供給可能になった。
3. ~~Generic algebraic placeholder~~: `cyclotomicGenericFactorizationIdentity_overCommSemiring` **CLOSED** ✅
  → current target が placeholder のため no-so#rry で閉じた。

補足:
`CyclotomicLocalFactorizationCoreTarget` は DkMath-native な局所証明核として no-so#rry で追加済み。
さらに `CyclotomicLocalEquationFactorizationCoreTarget` により、
`x^p + y^p = z^p` の FLT 方程式形まで局所的には no-so#rry で押し込めている。
また `linear_factor_ideal_mul_eq_span_pow_of_add_pow_eq` により、
その局所核から principal ideal の積の式 `(x)^p` まで concrete に降ろせるようになった。
さらに `linear_factor_ideals_sup_eq_top_of_mul_sub_isUnit` により、
pairwise-coprime に必要な comaximal 性も explicit な unit 仮定のもとで実装できた。
generator レベルでも `linear_factors_isCoprime_of_mul_sub_isUnit` が得られるため、
後段の coprime arithmetic へ渡しやすくなった。
ideal レベルでも `linear_factor_ideals_inf_eq_mul_of_mul_sub_isUnit` により
product = inf の basic lemma を確保できた。
加えて `dedekindInfPrimePowEqProd` により、Dedekind 領域での有限族 prime-power に対する
`inf = product` の generic receiver も DkMath 側へ取り込めた。
さらに `dedekindQuotientEquivPiOfFinsetProdEq` と
`dedekindExistsRepresentativeModFinset` により、Chinese remainder 側の finite-family receiver も確保できた。
加えて `dedekindIdealCountNormalizedFactorsEq` により、
prime-power exponent を factor count として読む入口も取れた。
さらに `dedekindIdealEqPowOfMulEqPowOfIsCoprime` と
`dedekindIdealEqPowOfProdEqPowOfPairwise` により、
review-012 の本丸である「pairwise-coprime な ideal family の積が p 乗 ideal なら各因子も p 乗 ideal」
という generic Dedekind theorem を no-so#rry で起こせた。
さらに `dedekindClassGroupMk0PowEqOneOfEqPowAndIsPrincipal` と
`dedekindClassGroupPowWitnessOfProdEqPowOfPairwise` により、
その ideal arithmetic から class-group p-torsion witness までの generic bridge も no-so#rry で接続できた。
review-013 により `CyclotomicClassGroupPTorsionFreeTarget` も concrete 化され、
`cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` は no-so#rry になった。
FLT を閉じる観点で direct に残る本筋の open は
`cyclotomicPrincipalization_of_classGroupPTorsionFree` の 1 本である。
review-014 により、この legacy one-shot theorem を守るのではなく、
`FLTPrimeGe5Target_of_refinedRegularPrimeRoute` を推奨 mainline とみなす方針を採る。
したがって今後の honest open は class-group ではなく、
`CyclotomicUnitNormalizationTarget` と `CyclotomicNormDescentTarget` に集中する。
さらに review-015 の入口として、Stage 2 の generic core
`principalGeneratorsUnitMulOfSpanEq`・
`unitMulPowOfSpanEqPowIdeal`・
`unitMulPowOfSpanEqPowPrincipal`
も no-so#rry で追加済みであり、
review-016 により local specialization
`linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal` と
`cyclotomicLocalUnitNormalizationCore` も no-so#rry で固定できた。
さらに review-019 により `CyclotomicUnitNormalizationTarget` 自体も
存在形 boundary から供給される pack-specialized element-level statement へ concretize 済みとなった。
review-017 により、pack + explicit ideal equality から
`z - ζy = u * β^p` を出す exact receiver
`cyclotomicUnitNormalization_of_spanEqPowPrincipal` も no-so#rry で追加できた。
さらに first-case specialization では
`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` により、
chosen factor について `z - ζy = u * β^p` を直接返す
norm 直前の thin wrapper も no-so#rry で固定できた。
review-018 により `CyclotomicLinearFactorIdealPthPowerTarget` は存在形へ直され、
`cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower` によって
その boundary target から element-level の Stage 2 statement まで composition で到達できる。
review-020 により、その一歩手前として
`principalRootIdealExistsOfEqPowAndTorsionKill` と
`linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill`
も no-so#rry で追加できた。
review-021 に備え、receiver 直前の companion lemma
`rootIdealNeBotOfEqPow`・`linearFactorNeZeroOfSpanEqPow` と、
root-ideal nonzero 版 receiver
`linearFactorIdealPthPowerExistsOfSpanEqPowAndRootNeBot`
も no-so#rry で追加した。
review-022 により、Stage 1 の explicit equality / exponent nonzero / linear-factor nonzero から
存在形 boundary を回収する
`cyclotomicLinearFactorIdealPthPower_of_spanEqPow` と、
そこから concrete Stage 2 target まで直接進む
`cyclotomicUnitNormalization_of_linearFactorSpanEqPow`
も no-so#rry で追加できた。
review-023 により、さらに 2-factor route の exact receiver 層として
`linearFactorSpanEqPowOfTailMulEqSpanPowAndIsCoprime`・
`cyclotomicLinearFactorSpanEqPow_of_tailFactorCoprime`・
`cyclotomicUnitNormalization_of_tailFactorCoprimeRoute`
も no-so#rry で追加できた。
review-024 により、actual cyclotomic supply 側でも
`CyclotomicLocalExponentAgreementTarget` を仮定すれば
`cyclotomicTailLinearFactorMulEqSpanPow_of_exponentAgreement` と
`cyclotomicLocalExponentNonzero_of_exponentAgreement`
が no-so#rry で追加できた。
また `(x)` 非零は任意の domain では supply できぬため、
honest な `CharZero` variant
`cyclotomicXSpanNonzero_of_counterexamplePack_of_charZero`
として切り出した。
review-025 により、actual coprimality 側も
`linearFactorIdealIsCoprimeProdEraseOfPairwiseMulSubIsUnit` と
`cyclotomicTailLinearFactorCoprime_of_pairwiseUnitWitness`
により、
「full family の差の unit 性 + tail decomposition witness」
を supply すれば chosen factor と tail の coprimality が generic に回収できる形へ sharpen された。
さらに
`cyclotomicUnitNormalization_of_exponentAgreementAndPairwiseUnitWitness`
により、指数一致 + pairwise witness + `(x)` 非零 + 線型因子非零 + class-group kill から
concrete Stage 2 target まで直接進めるようになった。
review-026 により、Mathlib の `ntRootsFinset_pairwise_associated_sub_one_sub_of_prime` を活用して
共通 prime ideal 分析の核心が no-so#rry で固められた:
- `associated_span_eq`: Associated なら span も等しい
- `linearFactorDiffSpanEqSubOneSpan`: 異なる linear factor 差の span が (ζ-1)*y の span に等しい
- `commonPrimeContainsSubOneY`: 共通 prime が chosen と別因子の両方を含むなら (ζ-1)*y も含む
- `commonPrimeDvdsSubOneOrY`: さらに prime の性質から P | (ζ-1) ∨ P | y
- `SubOneDividesPrimePTarget`: (ζ-1) ∈ P → P | (p) は cyclotomic number theory の target として残す
review-027 により、Mathlib の
`IsPrimitiveRoot.toInteger_sub_one_dvd_prime'` と `toInteger_isPrimitiveRoot`
を使った ring-of-integers specialization adapter も no-so#rry で追加できた:
- `subOneDividesPrimeP_of_toInteger_sub_one_dvd_prime'`: `hζ.toInteger - 1 ∈ P` から `P ∣ (p)`
- `commonPrimeDvdsPrimeOrY_of_ringOfIntegersCyclotomic`: 共通 prime ideal 分析の `(ζ-1)` 分岐を `P ∣ (p)` に変換
- `linearFactorIdeals_isCoprime_of_noCommonPrime`: common-prime contradiction を coprimality へ戻す generic receiver
- `chosenLinearFactor_isCoprime_with_other_of_primeOrYContradiction_of_ringOfIntegersCyclotomic`:
  ring of integers specialization で、`P ∣ (p) ∨ y ∈ P` の contradiction target から
  chosen factor と別の 1 因子の pairwise coprimality を回収

その後の更新で Stage 1 の coprimality leg もさらに concrete 化された:
- `noYInCommonPrime_of_chosenFactorInP_of_coprime_of_productEq`:
  y ∈ P 分岐を pack の `Nat.Coprime x y` と product identity から no-so#rry で閉じる
- `primeOverPEqualsZetaMinusOne_fill`:
  Mathlib `eq_span_zeta_sub_one_of_liesOver'` を使って
  `PrimeOverPEqualsZetaMinusOneTarget` を concrete に充足
- `integerInZetaMinusOneIdealDivisibleByP_fill`:
  norm 計算から `IntegerInZetaMinusOneIdealDivisibleByPTarget` を concrete に充足
- `noPrimeOverP_of_firstCase_of_chosenFactorInP` / `noPrimeOrY_of_firstCase_of_coprime`:
  first-case 条件のもとで `P ∣ (p) ∨ y ∈ P` の両分岐を統合して矛盾へ戻す
- `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack`:
  chosen factor と別因子の coprimality を pack-specialized に回収

したがって、以前 honest open だった
`P ∣ (p) ∨ y ∈ P` contradiction 自体は、少なくとも Stage 1 coprimality leg では整理済みじゃ。
現在の実際の open は、この coprimality を存在形 boundary target へどう押し込み、
さらに Stage 3 norm descent をどう concrete 化するかに寄っておる。

`CyclotomicUnitNormalizationTarget` はすでに concrete 化済みであり、
`CyclotomicNormDescentTarget` が未解決 stage として残っている。
ただし review-039 / review-040 相当の current state では、
first-case specialization に限れば Stage 3 の入口配線自体は
さらに 2 本へ分割できるところまで進んだ。
具体的には
`CyclotomicNormEqGNFirstCasePackThinTarget` と
`CyclotomicNormUnitAbsorbFirstCasePackThinTarget` を分離し、
それらを current thin wrapper へ接ぐ
`cyclotomicNormGNPower_of_firstCase_of_pack_thin` を追加したことで、
まず `GN p (z - y) y = s^p` を返す最初の concrete 境界が定義できた。
さらに
`false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin` により、
既存の no-pow target があれば即座に矛盾へ戻せる abstract bridge も置けた。
今後は Stage 1 の存在形 boundary と、
この Stage 3 split の各片割れを個別に concretize していく。
さらに current state では、`CyclotomicNormEqGNFirstCasePackThinTarget` 側も
review-040 の内部 3 分割のうち
- norm → `Gal(K/ℚ)` product
- `Gal(K/ℚ)` product → `(ZMod p)ˣ` product
- nontrivial factor product → `GN` / quotientPrimePow
までは theorem 名つきで固定できた。
ゆえに残る本丸は、`(ZMod p)ˣ` product を actual nontrivial factor product に落とす combinatorial bridge と、
それらを束ねて `CyclotomicNormEqGNFirstCasePackThinTarget` 本体へ戻す合成である。

`CyclotomicGapDivisibleFactorizationSpecializationTarget`・
`CyclotomicIdealEquationTarget`・`CyclotomicIdealProductPthPowerTarget`・
`CyclotomicPTorsionAnnihilationTarget`・`CyclotomicPrincipalIdealExtractionTarget` は
Stage 1 内部の責務分離として追加した。
前者は generic ClassGroup API の target として、後者は principal-ideal extraction API として
concrete 化済みであり、review-013 により
`CyclotomicClassGroupPTorsionFreeTarget` から `CyclotomicPTorsionAnnihilationTarget` への橋も
no-so#rry で供給できるようになった。
したがって現在の direct open は Stage 1b ではなく、
Stage 2 / Stage 3 を含む full principalization 側に移った。

Stage 1a 自体も、generic algebraic factorization identity / equation-only factorization identity / prime specialization /
abstract factorization identity / counterexample specialization /
pure factorization identity / gap-divisible specialization /
ideal equation packaging / ideal product / class witness の 10 層へ分離した。
今後 genuinely new theory を載せるべき場所は、その最上流 generic algebraic factorization identity theorem である。

それぞれ独立に攻略可能。
-/

namespace DkMath.FLT

/-!
## §1. `q = p` ケースの処理

`2m-pure` は任意の q に対して述べられている。
`q ≠ p` のケースは Regular + GapDivisible で処理できる。
`q = p` のケースは peel 側（p | x → p | gap → p-adic descent）の territory。

pack の構造解析:
- `q = p` かつ `p | x` のとき:
  - x^p + y^p = z^p, p | x
  - z^p ≡ y^p (mod p^p)
  - gap = z - y, x^p = gap · GN(p, gap, y)
  - p | x → p^p | x^p = gap · GN
  - GN(p, gap, y) ≡ p · y^{p-1} (mod gap)
  - gap = z - y, gcd(gap, y) = 1

`q = p` の descent existence は、peel route で p | gap のケースを
扱う際に natural に出る。ここでは abstract target として isolate。
-/

/--
`q = p` branch: p 自身が x を割る場合の descent existence。
Peel route (p | gap) の territory。
-/
abbrev PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ x →
    ∃ g' : ℕ, g' * GN p g' y = (x / p) ^ p

/-!
## §2. 3-way split: 2m-pure = (q=p) + Regular + GapDivisible

3 つの branch を合成して 2m-pure を構成する。
-/

/--
3-way split: `2m-pure` を 3 つの独立 branch に分解。

任意の pack + Prime q + q|x に対して:
- q = p: PEquals branch
- q ≠ p ∧ q ∤ (z-y): Regular branch
- q ≠ p ∧ q | (z-y): GapDivisible branch
-/
theorem qAdicGapReductionPure_of_threeWaySplit
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hGap : PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionPureTarget := by
  intro p x y z hpack q hq hq_dvd_x
  by_cases hqp : q = p
  · subst hqp
    exact hPeq hpack hq_dvd_x
  · exact qAdicGapReduction_qNeP_of_regularAndGapDivisible hReg hGap hpack hq hq_dvd_x hqp

/-!
## §3. Full chain: 3-way split → 2m-pure → FLT

existing DescentChain の `FLTPrimeGe5Target_of_qAdicGapReductionPure_infiniteDescent` を
利用して FLT まで接続。
-/

/--
Kummer 3-way split から FLT への full chain。

3 つの descent branch + 2 つの既存 open kernel を仮定として受け取り、
FLTPrimeGe5Target を返す。

既存 open kernel:
- `hPFE`: Peel route の PacketFromError
- `hNoLift`: NonLiftableGN Bridge
-/
theorem FLTPrimeGe5Target_of_kummerThreeWaySplit
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hGap : PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_qAdicGapReductionPure_infiniteDescent
    (qAdicGapReductionPure_of_threeWaySplit hPeq hReg hGap)
    hPFE hNoLift

/-!
## §4. Refined Kummer route: ideal / unit / norm の 3 段

唯一の genuinely global kernel を `CyclotomicIdealPthPowerTarget` として明示し、
その下流の unit / norm stage を別 target に分けた refined route。
`CyclotomicPrincipalizationTarget` を直接仮定する版より、
今後の formalization の責務分離が明確になる。
-/

/--
Refined Kummer route: ideal p-th power + unit normalization + norm descent → FLT。

ここで class group 側の genuinely global 入力は `hIdeal` だけ。
`hUnit` / `hNorm` は下流 stage を別々に監査できるように切り出した。
-/
theorem FLTPrimeGe5Target_of_refinedKummerRoute
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hIdeal : CyclotomicIdealPthPowerTarget)
    (hUnit : CyclotomicUnitNormalizationTarget)
    (hNorm : CyclotomicNormDescentTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_threeStages hIdeal hUnit hNorm))
    hPFE hNoLift

/-!
## §5. Refined Stage 1 route

Stage 1 自体をさらに 1a-1a-i / 1a-1a-ii / 1a-1b / 1a-2 / 1a-3 / 1b / 1c へ裂いた版。
最薄の open kernel は `hWitness` に局所化される。
-/

/--
Refined Stage 1 route: p-torsion witness + annihilation + extraction + unit / norm → FLT。
-/
theorem FLTPrimeGe5Target_of_refinedStage1Route
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hWitness : CyclotomicIdealClassPTorsionWitnessTarget)
    (hKill : CyclotomicPTorsionAnnihilationTarget)
    (hExtract : CyclotomicPrincipalIdealExtractionTarget)
    (hUnit : CyclotomicUnitNormalizationTarget)
    (hNorm : CyclotomicNormDescentTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_refinedKummerRoute hPeq hReg
    (cyclotomicIdealPthPower_of_refinedStage1Route hWitness hKill hExtract)
    hUnit hNorm hPFE hNoLift

/-!
## §6. Refined class-group route

class group 側の genuinely global kernel を Stage 1 theorem に isolate した版。
legacy one-shot route (`FLTPrimeGe5Target_of_kummerRoute`) より責務分離が明確。
-/

/--
Refined class-group route: class group → ideal p-th power → unit / norm → FLT。
-/
theorem FLTPrimeGe5Target_of_refinedClassGroupRoute
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hCl : CyclotomicClassGroupPTorsionFreeTarget)
    (hUnit : CyclotomicUnitNormalizationTarget)
    (hNorm : CyclotomicNormDescentTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_refinedClassGroupRoute hCl hUnit hNorm))
    hPFE hNoLift

/-!
## §7. Refined regular-prime route

review-014 に従う推奨 mainline。
regular prime から class-group 仮定だけを供給し、
Stage 2 / Stage 3 は独立入力として保つ。
-/

/--
推奨 mainline: regular prime + Stage 2 + Stage 3 → FLT。
-/
theorem FLTPrimeGe5Target_of_refinedRegularPrimeRoute
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hRegBranch : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hRegClass : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrime p)
    (hUnit : CyclotomicUnitNormalizationTarget)
    (hNorm : CyclotomicNormDescentTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hRegBranch
    (qAdicGapReductionGapDivisible_of_refinedRegularPrimeRoute hRegClass hUnit hNorm)
    hPFE hNoLift

/--
推奨 mainline の provider 具体化版。

regular-prime route の Stage 3 を abstract `hNorm` で受ける代わりに、
squarefree-GN provider から concrete に構成する。
-/
theorem FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hRegBranch : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hRegClass : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrime.{0} p)
    (hUnit : CyclotomicUnitNormalizationTarget.{0})
    (hSqProv : TriominoSquarefreeGNBridgeProvider)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hRegBranch
    (qAdicGapReductionGapDivisible_of_refinedRegularPrimeRoute_and_squarefreeGNProvider
      hRegClass hUnit hSqProv)
    hPFE hNoLift

/--
provider concrete な regular-prime mainline から global provider へ接続する public 入口。

`TriominoSquarefreeGNBridgeProvider` を concrete に持てる branch では、
abstract `FLTPrimeGe5Target` を経由して外へ渡す代わりに、
この theorem を canonical default 相当の provider-facing route として使う。
-/
theorem triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hRegBranch : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hRegClass : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrime.{0} p)
    (hUnit : CyclotomicUnitNormalizationTarget.{0})
    (hSqProv : TriominoSquarefreeGNBridgeProvider)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider
      hPeq hRegBranch hRegClass hUnit hSqProv hPFE hNoLift)

/--
provider concrete な regular-prime mainline から `TriominoPrimeProvider` へ接続する public 入口。

global provider alias を直接返す最外側 API として使えるよう、
`PrimeGe5FLTProvider` core bridge への合成をここで固定する。
-/
theorem triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hRegBranch : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hRegClass : ∀ {p : ℕ}, Nat.Prime p → 5 ≤ p → IsRegularPrime.{0} p)
    (hUnit : CyclotomicUnitNormalizationTarget.{0})
    (hSqProv : TriominoSquarefreeGNBridgeProvider)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider
      hPeq hRegBranch hRegClass hUnit hSqProv hPFE hNoLift)

/-!
## §8. Kummer route: ClassGroup → GapDivisible → 2m-pure → FLT

ClassGroupPTorsionFree + Regular branch + PEquals branch → FLT の
legacy one-shot theorem。
-/

/--
Split class-group route: first-case は current stable bridge 群で処理し、
non-first-case (`p ∣ z - y`) だけを open kernel として残す public mainline。

`cyclotomicPrincipalization_of_classGroupPTorsionFree` の legacy one-shot に代えて、
残責務を theorem 境界で明示する版。
-/
theorem FLTPrimeGe5Target_of_kummerRoute_of_caseSplit
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
    (hNonFirst : CyclotomicPrincipalizationNonFirstCaseTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_classGroupPTorsionFree_of_caseSplit
        hCl hNoLift hNonFirst))
    hPFE hNoLift

/--
Split public route: first-case は canonical bridge を使い、
non-first-case は prepare / descent kernel split で受ける版。

これにより public mainline でも、未解決責務を theorem 境界 2 本で監査できる。
-/
theorem FLTPrimeGe5Target_of_kummerRoute_of_kernelSplit
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
    (hPrep : CyclotomicPrincipalizationNonFirstCasePrepareTarget)
    (hDesc : CyclotomicPrincipalizationNonFirstCaseDescentTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_classGroupPTorsionFree_of_kernelSplit
        hCl hPrep hDesc))
    hPFE hNoLift

/--
Split public route: first-case は canonical bridge を使い、
non-first-case は prepare / existence kernel split で受ける版。

これにより public mainline でも、残る direct open を existence 語彙へ一段押し下げて監査できる。
-/
theorem FLTPrimeGe5Target_of_kummerRoute_of_existenceKernelSplit
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
    (hPrep : CyclotomicPrincipalizationNonFirstCasePrepareTarget)
    (hExist : CyclotomicPrincipalizationNonFirstCaseDescentExistenceTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_classGroupPTorsionFree_of_existenceKernelSplit
        hCl hPrep hExist))
    hPFE hNoLift

/--
Split public route: first-case は canonical bridge を使い、
non-first-case は prepare / valuation / reduction split で受ける版。

これにより public mainline でも、残る direct open を reduction kernel へさらに押し下げて監査できる。
-/
theorem FLTPrimeGe5Target_of_kummerRoute_of_valuationReductionKernelSplit
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
    (hPrep : CyclotomicPrincipalizationNonFirstCasePrepareTarget)
    (hVal : CyclotomicPrincipalizationNonFirstCaseValuationTarget)
    (hRed : CyclotomicPrincipalizationNonFirstCaseReductionTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_classGroupPTorsionFree_of_valuationReductionKernelSplit
        hCl hPrep hVal hRed))
    hPFE hNoLift

/--
Split public route: first-case は canonical bridge を使い、
non-first-case は prepare / valuation / error / packet split で受ける版。

これにより public mainline でも、残る direct open を packet kernel へさらに押し下げて監査できる。
-/
theorem FLTPrimeGe5Target_of_kummerRoute_of_errorPacketKernelSplit
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
    (hPrep : CyclotomicPrincipalizationNonFirstCasePrepareTarget)
    (hVal : CyclotomicPrincipalizationNonFirstCaseValuationTarget)
    (hErr : CyclotomicPrincipalizationNonFirstCaseErrorTarget)
    (hPkt : CyclotomicPrincipalizationNonFirstCasePacketTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_classGroupPTorsionFree_of_errorPacketKernelSplit
        hCl hPrep hVal hErr hPkt))
    hPFE hNoLift

/--
Split public route: first-case は canonical bridge を使い、
non-first-case は prepare / valuation / error / tailError / packetFromError split で受ける版。

これにより public mainline でも、残る direct open を packetFromError kernel へさらに押し下げて監査できる。
-/
theorem FLTPrimeGe5Target_of_kummerRoute_of_tailErrorPacketFromErrorKernelSplit
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
    (hPrep : CyclotomicPrincipalizationNonFirstCasePrepareTarget)
    (hVal : CyclotomicPrincipalizationNonFirstCaseValuationTarget)
    (hErr : CyclotomicPrincipalizationNonFirstCaseErrorTarget)
    (hTail : CyclotomicPrincipalizationNonFirstCaseTailErrorTarget)
    (hPFEKummer : CyclotomicPrincipalizationNonFirstCasePacketFromErrorTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_classGroupPTorsionFree_of_tailErrorPacketFromErrorKernelSplit
        hCl hPrep hVal hErr hTail hPFEKummer))
    hPFE hNoLift

/--
Legacy one-shot Kummer route: ClassGroup 仮定から FLT へ。

open kernels:
- `hPeq`: q = p ケース （peel route territory）
- `hReg`: q ≠ p ∧ q ∤ (z-y) ケース （witness 自動構成 territory）
- `hCl`: class group p-torsion free （Kummer regularity territory）
- `hPFE`: Peel route の PacketFromError（既存）
- `hNoLift`: NonLiftableGN Bridge（既存）
-/
theorem FLTPrimeGe5Target_of_kummerRoute
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
  (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_classGroupPTorsionFree hCl))
    hPFE hNoLift

end DkMath.FLT
