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
     ClassGroupPTorsionFree                     (placeholder)
        ↓
     IdealFactorization                         (thinnest theorem-level kernel)
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
  2m-pure                                    (no sorry ✅)
        ↓
   2m-global                                  (from 2m-pure, auto)
        ↓
  PthRootCore → GNReducedGap → 無限降下法   (existing chain, no sorry)
        ↓
   FLTPrimeGe5Target                          ✅
```

## open kernel の整理

Kummer branch 導入後の open kernel は **1 つ**に集約された:
1. ~~Regular branch~~: `qAdicGapReductionRegularBranch_of_global` **CLOSED** ✅
   → witness R の自動構成が ZMod unit 理論で完了。
2. **Gap-divisible global stage**: `cyclotomicIdealFactorization_of_gapDivisibleGeometry`
  → Kummer 理論 / 円分体 factorization の formal 化が必要（現時点で最薄の theorem-level kernel）。

`CyclotomicUnitNormalizationTarget` と `CyclotomicNormDescentTarget` は
現時点では abstract stage として明示化した。今後は各 stage ごとに
Mathlib 既存資産で concrete 化できるかを独立に監査する。

`CyclotomicIdealProductPthPowerTarget`・`CyclotomicPTorsionAnnihilationTarget`・
`CyclotomicPrincipalIdealExtractionTarget` は Stage 1 内部の責務分離として追加した。
前者は generic ClassGroup API の target として、後者は principal-ideal extraction API として
concrete 化済みだが、`CyclotomicClassGroupPTorsionFreeTarget` から前者を供給する橋は未解決である。
この未解決は target 形の問題ではなく、cyclotomic integer-ring parameterization を
仮定側へどう露出するか、という infrastructure 側の問題である。

Stage 1a 自体も、factorization / ideal product / class witness の 3 層へ分離した。
今後 genuinely new theory を載せるべき場所は、その最上流 factorization theorem である。

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

Stage 1 自体をさらに 1a-1 / 1a-2 / 1a-3 / 1b / 1c へ裂いた版。
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
## §7. Kummer route: ClassGroup → GapDivisible → 2m-pure → FLT

ClassGroupPTorsionFree + Regular branch + PEquals branch → FLT の
one-shot theorem。
-/

/--
Kummer principalization route: ClassGroup 仮定から FLT へ。

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
