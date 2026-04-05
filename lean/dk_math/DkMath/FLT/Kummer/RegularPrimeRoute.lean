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
残る open は cyclotomic pack への specialization と norm 側にさらに局所化された。

`CyclotomicUnitNormalizationTarget` と `CyclotomicNormDescentTarget` は
現時点では abstract stage として明示化した。今後は各 stage ごとに
Mathlib 既存資産で concrete 化できるかを独立に監査する。

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

/-!
## §8. Kummer route: ClassGroup → GapDivisible → 2m-pure → FLT

ClassGroupPTorsionFree + Regular branch + PEquals branch → FLT の
legacy one-shot theorem。
-/

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
    (hCl : CyclotomicClassGroupPTorsionFreeTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_classGroupPTorsionFree hCl))
    hPFE hNoLift

end DkMath.FLT
