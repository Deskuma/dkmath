/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong
import DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchADescentChain"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Branch A Descent Chain — Open Kernels → FLTPrimeGe5Target

このモジュールは、RestoreArithmeticStrong（primitive descent chain）と
GapInvariant（Branch A/B split mainline）を統合し、

**「残る open kernel を仮定として受け取り、FLTPrimeGe5Target を確定する」**

conditional chain を 1 箇所で確立する。

## 全体 chain 概略

```
BranchB: gapNotIsPow_default + gapPowBranchB → BranchBRefuter       ← concrete ✅
BranchA primitive: GNReducedGap + CyclotomicExistence → FringeContradiction ← conditional ✅
BranchA peel: ValuationPeelPacket                                    ← open (NePCoprimeKernel)
BranchA(Peel + Primitive): → SmallerPacket → BranchARefuter          ← conditional

FLTPrimeGe5:  BranchARefuter + BranchBRefuter → done                ← conditional
```

## Open Kernels

残る数学的 open kernel は以下の 3 本:
1. `GNReducedGapTarget`: descent gap の GN Body 一致
2. `CyclotomicExistenceTarget`: Wieferich 条件下の原始素因子存在
3. `ValuationPeelPacketTarget`: p ∣ t 側の smaller packet 構成

primitive route のみ（¬p ∣ t 側）であれば kernel は 1. + 2. の 2 本。
全 Branch A（p ∣ t を含む）には 3. も必要。
-/

namespace DkMath.FLT

/-!
## §1. Primitive route conditional: 2 kernel → FringeContradiction

`RestoreArithmeticStrong.lean` で確立済み:
- `branchAFringeContradiction_of_gnReducedGap_and_cyclotomicExistence`

ここでは再 export のみ。
-/

-- (直接使えるため、新定理は不要)

/-!
## §2. BranchB Refuter — concrete

`GapInvariant.lean` で確立済み:
- `gapNotIsPowTarget_default`
- `gapPowFromPrimeGe5Counterexample_branchB_impl`
- `branchBRefuter_of_gapPow_and_defaultNotPow`
-/

/--
BranchB Refuter の concrete 実装を 1 行で export。

Branch B (`¬ p ∣ (z-y)`) では:
- `gapNotIsPow_default`: gap ≠ p乗（全域）
- `gapPowBranchB`: gap = p乗（Branch B concrete）
→ 矛盾。
-/
theorem branchBRefuter_concrete :
    BranchBRefuterTarget :=
  branchBRefuter_of_gapPow_and_defaultNotPow
    (fun hpack hpB => gapPowFromPrimeGe5Counterexample_branchB_impl hpack hpB)

/-!
## §3. BranchA Refuter — conditional on 3 kernels

Branch A の反例排除には:
- Primitive route (¬p ∣ t): GNReducedGap + CyclotomicExistence → PacketDescentTarget
- Peel route (p ∣ t): ValuationPeelPacketTarget
の 2 分岐が必要（`SmallerPacket_of_routes` で合流）。

ここでは 3 kernel を仮定として受け取り、BranchARefuterTarget を確定する。
-/

/--
3 つの open kernel を仮定として受け取り、`BranchARefuterTarget` を確定する。

これは FLT 無限降下法の Branch A 側に必要な数学が正確にこの 3 本であることの
formal certificate である。

Inputs:
1. `GNReducedGapTarget`: descent gap の GN Body 一致
2. `CyclotomicExistenceTarget`: Wieferich 条件下の原始素因子存在
3. `ValuationPeelPacketTarget`: p ∣ t 側の smaller packet 構成

Output: `BranchARefuterTarget` (= Pack + p ∣ gap → False)
-/
theorem branchARefuter_of_3kernels
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget) :
    BranchARefuterTarget :=
  primeGe5BranchARefuter_of_distinguishedPrimeDescent
    (primeGe5BranchADistinguishedPrimeDescent_of_smallerCounterexample
      (primeGe5BranchASmallerCounterexample_of_smallerPacket
        (primeGe5BranchASmallerPacket_of_routes hPeel
          (primeGe5BranchAPrimitivePacketDescent_of_gnReducedGap_and_cyclotomicExistence
            hGNGap hEx))))

/-!
## §4. FLTPrimeGe5Target — conditional on 3 kernels

BranchA (3 kernel) + BranchB (concrete) → FLTPrimeGe5Target
-/

/--
3 つの open kernel から `FLTPrimeGe5Target` を確定する conditional chain。

これにより、FLT p ≥ 5 の完全証明に必要な残り作業が以下の 3 定理であることが
Lean 上で formal に保証される:

1. `GNReducedGapTarget`:
   ∃ g', g' * GN p g' y = p^p * (t*s')^p

2. `CyclotomicExistenceTarget`:
   ∀ Pack, p ∣ (z-y) → ∃ q, Prime q ∧ q ∣ (z^p-y^p) ∧ ¬ q ∣ (z-y)

3. `ValuationPeelPacketTarget`:
   Pack + p ∣ t → ∃ pkt', pkt'.z < z
-/
theorem FLTPrimeGe5Target_of_3kernels
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_branch_split_refuter_with_normalizer_impl
    (branchARefuter_of_3kernels hGNGap hEx hPeel)
    branchBRefuter_concrete

/--
4 つの open kernel から `FLTPrimeGe5Target` を確定する **完全 no-so#rryAx** chain。

3-kernel 版 (`FLTPrimeGe5Target_of_3kernels`) は BranchB 側の
`gapNotIsPowTarget_default` に ZsigmondyResearch so#rry が混入する。
この 4-kernel 版は `GapNotIsPowTarget` も仮定として外出しし、
全 axioms を `[propext, Classical.choice, Quot.sound]` のみにする。

4 つの kernel:
1. `GNReducedGapTarget`: descent gap の GN Body 一致
2. `CyclotomicExistenceTarget`: Wieferich 条件下の原始素因子存在
3. `ValuationPeelPacketTarget`: p ∣ t 側の smaller packet 構成
4. `GapNotIsPowTarget`: gap ≠ p 乗（BranchB refuter の前提）
-/
theorem FLTPrimeGe5Target_of_4kernels
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hGapNotIsPow : GapNotIsPowTarget) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_branch_split_refuter_with_normalizer_impl
    (branchARefuter_of_3kernels hGNGap hEx hPeel)
    (fun hpack hpB => (hGapNotIsPow hpack)
      (gapPowFromPrimeGe5Counterexample_branchB_impl hpack hpB))

/--
3 つの open kernel から `GlobalPrimeExponentFLTProvider` を確定する conditional chain。

`FLTPrimeGe5Target` → `GlobalPrimeExponentFLTProvider` の接続は
`TriominoCosmicPrimeGe5Core.lean` で確立済み。
-/
theorem globalProvider_of_3kernels
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget) :
    GlobalPrimeExponentFLTProvider :=
  triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_3kernels hGNGap hEx hPeel)

/--
4-kernel 版 `GlobalPrimeExponentFLTProvider` (完全 no-so#rryAx)。
-/
theorem globalProvider_of_4kernels
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hGapNotIsPow : GapNotIsPowTarget) :
    GlobalPrimeExponentFLTProvider :=
  triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_4kernels hGNGap hEx hPeel hGapNotIsPow)

/--
3 つの open kernel から `TriominoPrimeProvider` を確定する conditional chain。
-/
theorem triominoPrimeProvider_of_3kernels
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget) :
    TriominoPrimeProvider :=
  triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_3kernels hGNGap hEx hPeel)

/--
4-kernel 版 `TriominoPrimeProvider` (完全 no-so#rryAx)。
-/
theorem triominoPrimeProvider_of_4kernels
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hGapNotIsPow : GapNotIsPowTarget) :
    TriominoPrimeProvider :=
  triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_4kernels hGNGap hEx hPeel hGapNotIsPow)

/-!
## §5. GapNotIsPowTarget の clean 化: NonLiftableGNBridge → GapNotIsPowTarget

`gapNotIsPowTarget_default` は `triominoWieferichBranchBridge_default` 経由で
`ZsigmondyCyclotomicResearch.squarefree_implies_padic_val_le_one`（so#rry あり、命題自体が偽）
に依存しており `so#rryAx` 汚染がある。

ここでは、`TriominoCosmicNonLiftableGNBridge`（= primitive prime が GN に深刺ししない）
を仮定として外出しし、clean な `GapNotIsPowTarget` を構成する。

chain:
  NonLiftableGNBridge
  → NoPowOnGN (Branch A は concrete、Branch B は NonLiftableGNBridge)
  → BodyInvariant → GapInvariant = GapNotIsPowTarget

全中間定理は既存の no-so#rry 定理のみを使用。
-/

/--
`TriominoCosmicNonLiftableGNBridge` から `GapNotIsPowTarget` を clean に構成する。

`so#rryAx` なし。Branch A 側は `noSqPrimeOnGN_when_p_dvd_u_impl` (concrete) で、
Branch B 側は NonLiftableGNBridge 仮定で、合成して全 Pack をカバーする。
-/
theorem gapNotIsPowTarget_of_nonLiftableGNBridge
    (hBridge : TriominoCosmicNonLiftableGNBridge) :
    GapNotIsPowTarget :=
  gapInvariant_of_bodyInvariant
    (bodyInvariant_of_NoPowOnGN
      (triominoCosmicNoPowOnGN_of_nonLiftableGNBridge hBridge))

/--
`TriominoCosmicNonLiftableGNBridge` から `BranchBRefuterTarget` を clean に構成する。

3-kernel 版で使っていた `branchBRefuter_concrete`（so#rryAx 汚染）の代替。
-/
theorem branchBRefuter_of_nonLiftableGNBridge
    (hBridge : TriominoCosmicNonLiftableGNBridge) :
    BranchBRefuterTarget := fun hpack hpB =>
  (gapNotIsPowTarget_of_nonLiftableGNBridge hBridge hpack)
    (gapPowFromPrimeGe5Counterexample_branchB_impl hpack hpB)

/-!
## §6. 4-kernel chain v2: NonLiftableGNBridge による clean 統合

4 つの open kernel:
1. `GNReducedGapTarget`: descent gap の GN Body 一致
2. `CyclotomicExistenceTarget`: Wieferich 条件下の原始素因子存在
3. `ValuationPeelPacketTarget`: p ∣ t 側の smaller packet 構成
4. `NonLiftableGNBridge`: primitive prime が GN に深刺ししない

4 番目は `GapNotIsPowTarget`（v1）を **より根源的な仮定** に置き換えたもの。
NonLiftableGNBridge → GapNotIsPowTarget の導出は clean (no-so#rry)。
-/

theorem FLTPrimeGe5Target_of_4kernels_v2
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_branch_split_refuter_with_normalizer_impl
    (branchARefuter_of_3kernels hGNGap hEx hPeel)
    (branchBRefuter_of_nonLiftableGNBridge hNoLift)

theorem globalProvider_of_4kernels_v2
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    GlobalPrimeExponentFLTProvider :=
  triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_4kernels_v2 hGNGap hEx hPeel hNoLift)

theorem triominoPrimeProvider_of_4kernels_v2
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    TriominoPrimeProvider :=
  triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_4kernels_v2 hGNGap hEx hPeel hNoLift)

/-!
## §7. Primitive-only route: 2 kernel → BranchA FringeContradiction

Peel route を使わず、primitive route のみで
`BranchAInterferenceFringeBundle → False` を確定する。
FringeDescent は `¬p ∣ t` の FringeBundle 内で閉じるため Peel は不要。

このルートは BranchARefuterTarget ではないが（FringeBundle → False であって Pack → False ではない）、
primitive descent の完全性を保証する formal certificate として機能する。
-/

-- `branchAFringeContradiction_of_gnReducedGap_and_cyclotomicExistence` は
-- RestoreArithmeticStrong.lean で確立済み。direct re-export。

/-!
## §8. NePCoprimeKernel: ValuationPeelPacketTarget の上位互換

`NePCoprimeKernel` は Branch A normal form で `Coprime(t, s) → False` を主張する。
これは `p | t` の場合も `¬ p | t` の場合も包含するため、
`ValuationPeelPacketTarget` + `PrimitivePacketDescentTarget` の **両方の上位互換** である。

したがって NePCoprimeKernel 1 本で BranchARefuter が直接構成でき、
3-kernel chain (GNGap + CycloEx + Peel) の Peel を **完全に bypass** する。
-/

/--
`NePCoprimeKernel` から `BranchARefuterTarget` を直接構成する。

NePCoprimeKernel は「normal form で Coprime(t, s) → False」を主張するが、
Coprime(t, s) は BranchA normal form で concrete に派生する (`coprime_ts_default`)。
したがって BranchA 反例は存在できず、BranchARefuterTarget が出る。

ValuationPeel route 全体を bypass する。
-/
theorem branchARefuter_of_nePCoprimeKernel
    (hKernel : PrimeGe5BranchANormalFormNePCoprimeKernelTarget) :
    BranchARefuterTarget := by
  intro p x y z hpack hp_dvd_gap
  rcases primeGe5BranchAShapeValue_of_factorization
    primeGe5BranchAShapeFactorization_default hpack hp_dvd_gap with ⟨t, ht⟩
  rcases primeGe5BranchANormalForm_of_witness hpack hp_dvd_gap ht with ⟨s, hsGN, hsx⟩
  exact hKernel hpack hp_dvd_gap
    (primeGe5BranchAShapeWitness_to_descent_input hpack hp_dvd_gap ht).gapShape
    hsGN
    (primeGe5BranchANormalForm_coprime_ts_default hpack hp_dvd_gap
      (primeGe5BranchAShapeWitness_to_descent_input hpack hp_dvd_gap ht).gapShape hsGN)

/-!
## §9. 2-kernel chain: NePCoprimeKernel + NonLiftableGNBridge → FLTPrimeGe5

ValuationPeel と GNReducedGap/CyclotomicExistence を **全て bypass** し、
必要な open kernel を **2 本** に圧縮した最小 chain。

1. `NePCoprimeKernelTarget`: BranchA normal form で Coprime(t,s) → False
2. `NonLiftableGNBridge`: primitive prime が GN に深刺ししない

NePCoprimeKernel が BranchA 全体を殺し、NonLiftableGNBridge が BranchB を殺す。
-/

theorem FLTPrimeGe5Target_of_2kernels
    (hKernel : PrimeGe5BranchANormalFormNePCoprimeKernelTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_branch_split_refuter_with_normalizer_impl
    (branchARefuter_of_nePCoprimeKernel hKernel)
    (branchBRefuter_of_nonLiftableGNBridge hNoLift)

theorem globalProvider_of_2kernels
    (hKernel : PrimeGe5BranchANormalFormNePCoprimeKernelTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    GlobalPrimeExponentFLTProvider :=
  triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_2kernels hKernel hNoLift)

theorem triominoPrimeProvider_of_2kernels
    (hKernel : PrimeGe5BranchANormalFormNePCoprimeKernelTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    TriominoPrimeProvider :=
  triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_2kernels hKernel hNoLift)

/-!
## §10. kernel 間の包含関係の形式化

Open kernel の階層を明示する。
-/

/--
`NePCoprimeKernel` は `ValuationPeelPacketTarget` の上位互換。

NePCoprimeKernel は全 BranchA normal form で False を出すため、
p ∣ t 条件下の pkt'.z < z 要求は trivially satisfied（False → anything）。
-/
theorem valuationPeelPacketTarget_of_nePCoprimeKernel
    (hKernel : PrimeGe5BranchANormalFormNePCoprimeKernelTarget) :
    PrimeGe5BranchAValuationPeelPacketTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts _ _ _ hpt
  exfalso
  exact hKernel hpack hp_dvd_gap hgap hsGN hcop_ts

/--
`NePCoprimeKernel` は `PrimitivePacketDescentTarget` の上位互換。

同様に、¬ p ∣ t 条件下の pkt'.z < z 要求も trivially satisfied。
-/
theorem primitivePacketDescentTarget_of_nePCoprimeKernel
    (hKernel : PrimeGe5BranchANormalFormNePCoprimeKernelTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts _ _ _ _
  exfalso
  exact hKernel hpack hp_dvd_gap hgap hsGN hcop_ts

/--
`NePCoprimeKernel` は `SmallerPacketTarget` の上位互換。

Peel + Primitive の両方を殺す。
-/
theorem smallerPacketTarget_of_nePCoprimeKernel
    (hKernel : PrimeGe5BranchANormalFormNePCoprimeKernelTarget) :
    PrimeGe5BranchASmallerPacketTarget :=
  primeGe5BranchASmallerPacket_of_routes
    (valuationPeelPacketTarget_of_nePCoprimeKernel hKernel)
    (primitivePacketDescentTarget_of_nePCoprimeKernel hKernel)

end DkMath.FLT
