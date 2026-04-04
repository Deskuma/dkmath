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
   ClassGroupPTorsionFree                     (sorry: open kernel)
        ↓
   CyclotomicPrincipalization                 (sorry → ClassGroup)
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
2. **Gap-divisible branch**: `cyclotomicPrincipalization_of_classGroupPTorsionFree` (sorry)
   → Kummer 理論の formal 化が必要（唯一の open kernel）。

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
## §4. Kummer route: ClassGroup → GapDivisible → 2m-pure → FLT

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
