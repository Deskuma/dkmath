/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong
import DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant
import DkMath.CFBRC.ExceptionalExistence

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchADescentChain"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open DkMath.CosmicFormulaBinom

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

/-!
## §11. CyclotomicExistence の concrete 供給

CFBRC ExceptionalExistence の Lean 証明により、
`CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget` が concrete に閉じた。
（d | x かつ Wieferich のとき、cyclotomicPrimeCore に x を割らない素因子が存在する。）

bridge chain 経由で `PrimeGe5BranchACyclotomicExistenceTarget` まで concrete 化される。
-/

namespace DkMath.FLT

/--
`CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget` の concrete 実装。
-/
theorem cfbrcExceptionalPrimeExpBoundaryOnWieferich_concrete :
    CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget :=
  fun hd hd5 hx hu hcop hdx hW =>
    DkMath.CFBRC.exists_prime_factor_cyclotomicPrimeCore_not_dvd_gap_exceptional
      hd hd5 hx hu hcop hdx hW

/--
`PrimeGe5BranchACyclotomicExistenceTarget` の concrete 実装。

ExceptionalExistence → bridge chain を full 経由。
-/
theorem primeGe5BranchACyclotomicExistence_concrete :
    PrimeGe5BranchACyclotomicExistenceTarget :=
  primeGe5BranchACyclotomicExistence_of_wieferich
    (primeGe5BranchACyclotomicExistenceOnWieferich_of_coreExistence
      (primeGe5BranchACyclotomicCoreExistenceOnWieferich_of_cfbrcExceptional
        (primeGe5BranchACFBRCExceptionalExistence_of_boundaryExceptional
          cfbrcExceptionalPrimeExpBoundaryOnWieferich_concrete)))

/-!
## §12. 3-kernel chain v3: GNReducedGap + ValuationPeel + NonLiftableGNBridge

CyclotomicExistence が concrete に閉じたため、4-kernel chain で
CyclotomicExistence kernel を除去し、3-kernel に圧縮。

3 open kernels:
1. `GNReducedGapTarget`: GN tail 降下構造
2. `ValuationPeelPacketTarget`: p ∣ t 側のパケット縮小
3. `NonLiftableGNBridge`: primitive prime の GN 深刺し禁止
-/

theorem branchARefuter_of_2kernels_gnGap_peel
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget) :
    BranchARefuterTarget :=
  branchARefuter_of_3kernels hGNGap primeGe5BranchACyclotomicExistence_concrete hPeel

theorem FLTPrimeGe5Target_of_3kernels_v3
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_branch_split_refuter_with_normalizer_impl
    (branchARefuter_of_2kernels_gnGap_peel hGNGap hPeel)
    (branchBRefuter_of_nonLiftableGNBridge hNoLift)

theorem globalProvider_of_3kernels_v3
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    GlobalPrimeExponentFLTProvider :=
  triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_3kernels_v3 hGNGap hPeel hNoLift)

theorem triominoPrimeProvider_of_3kernels_v3
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    TriominoPrimeProvider :=
  triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_3kernels_v3 hGNGap hPeel hNoLift)

/-!
## §13. Primitive PacketDescent の GNReducedGap 1-kernel 化

CyclotomicExistence が concrete 化されたため、
Primitive descent は GNReducedGap 1 本の仮定で完結する。

chain: GNReducedGap + CyclotomicExistence(concrete) → PrimitivePacketDescent
-/

/--
GNReducedGap だけで PrimitivePacketDescent を供給する。

CyclotomicExistence は `primeGe5BranchACyclotomicExistence_concrete` で concrete 化済み。
-/
theorem primitivePacketDescent_of_gnReducedGap
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_gnReducedGap_and_cyclotomicExistence
    hGNGap primeGe5BranchACyclotomicExistence_concrete

/--
GNReducedGap + ValuationPeel → SmallerPacket。

BranchA 内の case split (p∣t / ¬p∣t) を GNReducedGap 1 本と Peel 1 本で fully cover。
-/
theorem smallerPacket_of_gnReducedGap_and_peel
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget) :
    PrimeGe5BranchASmallerPacketTarget :=
  primeGe5BranchASmallerPacket_of_routes
    hPeel (primitivePacketDescent_of_gnReducedGap hGNGap)

/-!
## §14. Open kernel 等価関係と ContradictionTarget

### 14.1. GNReducedGap ↔ PthRootReduced ↔ PthRoot (双方向 clean bridge)

3 つの target は Lean 上で相互帰着可能であり、数学的に等価。
語彙の選択に自由度がある:
- `GNReducedGapTarget`: ∃ g', g'·GN(g',y) = p^p·(t·s')^p — Cosmic Formula native
- `PthRootReducedTarget`: ∃ z', p^p·(t·s')^p + y^p = z'^p — reduced power form
- `PthRootTarget`: ∃ z', x'^p + y^p = z'^p  (x' = x/q) — Fermat equation form
-/

/--
PthRootReduced → GNReducedGap。z' → g' := z' - y via Cosmic Formula。
-/
theorem gnReducedGap_of_pthRootReduced
    (h : PrimeGe5BranchAPrimitiveRestorePthRootReducedTarget) :
    PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget :=
  primeGe5BranchAPrimitiveRestoreGNReducedGap_of_pthRootReduced h

/--
GNReducedGap → PthRootReduced。g' → z' := g' + y via Cosmic Formula。
-/
theorem pthRootReduced_of_gnReducedGap
    (h : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootReducedTarget :=
  primeGe5BranchAPrimitiveRestorePthRootReduced_of_gnReducedGap h

/--
PthRoot → PthRootReduced。x' = p·(t·s') の代入で reduced form に変換。
-/
theorem pthRootReduced_of_pthRoot
    (h : PrimeGe5BranchAPrimitiveRestorePthRootTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootReducedTarget :=
  primeGe5BranchAPrimitiveRestorePthRootReduced_of_pthRoot h

/--
PthRootReduced → PthRoot。reduced form から Fermat equation form へ展開。
-/
theorem pthRoot_of_pthRootReduced
    (h : PrimeGe5BranchAPrimitiveRestorePthRootReducedTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootTarget :=
  primeGe5BranchAPrimitiveRestorePthRoot_of_reduced h

/--
GNReducedGap → PthRoot（直通）。Cosmic Formula → x' 語彙。
-/
theorem pthRoot_of_gnReducedGap
    (h : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootTarget :=
  primeGe5BranchAPrimitiveRestorePthRoot_of_gnReducedGap h

/--
PthRoot → GNReducedGap（直通）。x' 語彙 → Cosmic Formula。
-/
theorem gnReducedGap_of_pthRoot
    (h : PrimeGe5BranchAPrimitiveRestorePthRootTarget) :
    PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget :=
  gnReducedGap_of_pthRootReduced (pthRootReduced_of_pthRoot h)

/-!
### 14.2. ContradictionTarget → 全 BranchA descent kernel (vacuously)

ContradictionTarget が落ちれば、GNReducedGap と SmallerPacket が
vacuously 確定する（False → ∃）。
さらに、ContradictionTarget は peel/primitive の case split を bypass するため、
PacketFromError も vacuously 閉じる。

### 14.3. ContradictionTarget + NonLiftableGNBridge → FLT p ≥ 5

これは 2-kernel chain と同等の最短勝ち筋をもう一つ提供する。
ただし ContradictionTarget は NePCoprimeKernel 同様に
「BranchA ¬p∣t 内で直接矛盾」を求めるため、攻略難度は高い。
-/

/--
ContradictionTarget → GNReducedGapTarget。

False が得られるので g' の存在は vacuously true。
-/
theorem gnReducedGap_of_contradiction
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget) :
    PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget :=
  primeGe5BranchAPrimitiveRestoreGNReducedGap_of_contradiction hContra

/--
ContradictionTarget → PrimitivePacketDescent（CyclotomicExistence 不要で直接到達）。

chain: ContradictionTarget → GNReducedGap(vacuously)
       → PrimitivePacketDescent(via concrete CyclotomicExistence)
-/
theorem primitivePacketDescent_of_contradiction
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primitivePacketDescent_of_gnReducedGap (gnReducedGap_of_contradiction hContra)

/--
ContradictionTarget + ValuationPeel + NonLiftableGNBridge → FLT p ≥ 5。

ContradictionTarget は primitive 側(¬p∣t)の矛盾を直接供給し、
peel 側(p∣t)は ValuationPeel で、BranchB は NonLiftableGNBridge で処理。
-/
theorem FLTPrimeGe5Target_of_contradiction_peel_bridge
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget)
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_3kernels_v3
    (gnReducedGap_of_contradiction hContra) hPeel hNoLift

/-!
## §15. PacketFromError の精密分解

ValuationPeelPacketTarget は次の 2 段で構成される:
1. TailError: concrete (error 方程式の抽出) ✅
2. PacketFromError: open (error term → smaller packet) ❌

TailError が concrete なので、PacketFromError 1 本が peel route の唯一の穴。
-/

/--
TailError(concrete) + PacketFromError → ValuationPeelPacketTarget。

これにより、ValuationPeel 全体の open kernel は PacketFromError 1 本に集約。
-/
theorem valuationPeelPacket_concrete_tailError_with_packetFromError
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget) :
    PrimeGe5BranchAValuationPeelPacketTarget :=
  primeGe5BranchAValuationPeelPacket_of_tailErrorLift
    primeGe5BranchAValuationPeelTailError_default hPFE

/--
GNReducedGap + PacketFromError + NonLiftableGNBridge → FLT p ≥ 5。

3-kernel v3 を PacketFromError 語彙で書き直した最精密版。
ValuationPeelPacketTarget 全体ではなく、真の open 成分 PacketFromError だけを仮定。
-/
theorem FLTPrimeGe5Target_of_3kernels_precise
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_3kernels_v3 hGNGap
    (valuationPeelPacket_concrete_tailError_with_packetFromError hPFE) hNoLift

theorem globalProvider_of_3kernels_precise
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    GlobalPrimeExponentFLTProvider :=
  triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_3kernels_precise hGNGap hPFE hNoLift)

theorem triominoPrimeProvider_of_3kernels_precise
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    TriominoPrimeProvider :=
  triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_3kernels_precise hGNGap hPFE hNoLift)

/-!
## §16. PthRoot Core — DescentSeed 展開による q-adic 攻撃面の露出

### 目的

`PthRootTarget` (≡ `GNReducedGapTarget`) の内部では、
`DescentSeed` が opaque bundle として渡される。
しかし q-adic lifting の数学を具体的に攻めるには、
その中身 — `RestoreWitnessProperties` と `QAdicLiftSeed (ω)` —
を直接使う形の sub-target が必要。

ここでは:
1. DescentSeed を展開した `PthRootCoreTarget` を定義
2. PthRootCore → PthRoot への concrete bridge を確立
3. PthRootCore の入力が全て concrete に供給可能であることを確認

### 数学的内容

`PthRootCoreTarget` は:
  Pack + normal form + ¬p∣t + Wieferich + primitive q
  + **RestoreWitnessProperties (q∣x, ¬q∣y, ¬q∣z, ¬q∣gap, p∣(q-1), q^p∣GN)**
  + **QAdicLiftSeed (ω^p = 1, ω ≠ 1 in ZMod q)**
  → ∃ z', (x/q)^p + y^p = z'^p

これは DescentSeed の中身を剥き出しにしたもので、
q-adic lifting の数学にダイレクトにアクセスする語彙を提供する。

### QAdicLiftSeed の concrete 供給

`primeGe5BranchAPrimitiveRestoreQAdicLift_default` が concrete に構成する:
- `p ∣ (q-1)` から `(ZMod q)*` に order p の元が存在
- その元を ω として取り出す
-/

/--
DescentSeed 展開版 PthRoot Core。

ω (nontrivial p-th root of unity in ZMod q) と
RestoreWitnessProperties (q^p | GN 等) を明示入力にして、
z' の存在を直接求める。
-/
abbrev PrimeGe5BranchAPrimitivePthRootCoreTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      -- RestoreWitnessProperties 展開
      q ∣ x →
      ¬ q ∣ y →
      ¬ q ∣ z →
      ¬ q ∣ (z - y) →
      p ∣ (q - 1) →
      q ^ p ∣ GN p (z - y) y →
      -- QAdicLiftSeed 展開
      ∀ (ω : ZMod q), ω ^ p = 1 → ω ≠ 1 →
      let x' := x / q
      ∃ z' : ℕ, x' ^ p + y ^ p = z' ^ p

/--
PthRootCore → PthRoot。

DescentSeed の concrete 構成で内部を埋めて、
展開版の Core target から opaque 版の PthRoot target を回収する。
-/
theorem pthRootTarget_of_pthRootCore
    (hCore : PrimeGe5BranchAPrimitivePthRootCoreTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hSeed
  -- DescentSeed を展開
  have hDatum := hSeed.hDatum
  have hWitness := hDatum.hData
  have hLift := hDatum.hLift
  exact hCore hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    hqprime hqs hqt hcop_qy hq_ne_p
    hWitness.hq_dvd_x hWitness.hq_not_dvd_y hWitness.hq_not_dvd_z
    hWitness.hq_not_dvd_gap hWitness.hq_cong hWitness.hqp_dvd_GN
    hLift.ω hLift.hω_pow hLift.hω_ne_one

/--
PthRootCore → GNReducedGap（直通）。
-/
theorem gnReducedGap_of_pthRootCore
    (hCore : PrimeGe5BranchAPrimitivePthRootCoreTarget) :
    PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget :=
  gnReducedGap_of_pthRoot (pthRootTarget_of_pthRootCore hCore)

/--
PthRootCore → PrimitivePacketDescent（CyclotomicExistence concrete 経由）。
-/
theorem primitivePacketDescent_of_pthRootCore
    (hCore : PrimeGe5BranchAPrimitivePthRootCoreTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primitivePacketDescent_of_gnReducedGap (gnReducedGap_of_pthRootCore hCore)

/--
PthRootCore + PacketFromError + NonLiftableGNBridge → FLT p ≥ 5。

primitive 側を PthRootCore 語彙で書いた最精密版。
-/
theorem FLTPrimeGe5Target_of_pthRootCore_precise
    (hCore : PrimeGe5BranchAPrimitivePthRootCoreTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_3kernels_precise
    (gnReducedGap_of_pthRootCore hCore) hPFE hNoLift

/-!
## §17. PacketFromError の数学的核心: PeelPthRootCore

### 構造比較

| 側 | 条件 | target | descent 種 |
|---|---|---|---|
| primitive (¬p∣t) | q∣s, q∤gap | PthRootCoreTarget | q-adic |
| peel (p∣t) | p∣t, p∣gap | PeelPthRootCoreTarget | p-adic |
| branchB (¬p∣gap) | 別構造 | NonLiftableGNBridge | — |

### 数学的内容

PacketFromError の error 方程式 `p*B = C + u*E` (u = p^{p-1}*t1^p) は、
gap を p^p 分の 1 にスケールしたときの GN の変化を記述する。

数学的に最も直観的な語彙では、peel descent の核心は:

  ``p ∣ t (i.e. p^2 ∣ x) のとき、(x/p)^p + y^p が完全 p 乗``

ということ。これを error data 付きの sub-target として露出する。

### 注意

peel で gap だけ変えても GN(gap', y) ≠ p*s^p (数値で確認済み)。
つまり NormalFormPacket を直接構成するには、新しい (t', s') を error data から構築する必要がある。
-/

/--
p-adic peel 版 PthRoot Core。

error 方程式の全データを展開して受け取り、
smaller NormalFormPacket の存在を直接求める。

PacketFromError と同値だが、error data の出自を明記した形。
-/
abbrev PrimeGe5BranchAPeelPthRootCoreTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    p ∣ t →
    -- peel data 展開
    ∀ {t1 : ℕ},
      t = p * t1 →
      -- error data (from TailError chain, all concrete)
      ∀ {B C E : ℕ},
        -- seed side: s^p = y^{p-1} + p^{2p-1} * t1^p * B
        s ^ p = y ^ (p - 1) + p ^ (2 * p - 1) * t1 ^ p * B →
        -- canonical side: GN(p, p^{p-1}*t1^p, y) = p * y^{p-1} + (p^{p-1}*t1^p) * C
        GN p (p ^ (p - 1) * t1 ^ p) y = p * y ^ (p - 1) + (p ^ (p - 1) * t1 ^ p) * C →
        -- error relation: p*B = C + (p^{p-1}*t1^p) * E
        p * B = C + (p ^ (p - 1) * t1 ^ p) * E →
        ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z

/--
PacketFromError → PeelPthRootCore（弱化）。

PacketFromError は B,C,E を任意に受け取るので、
PeelPthRootCore が追加的に要求する seed/canonical detail は単に無視できる。
-/
theorem peelPthRootCore_of_packetFromError
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget) :
    PrimeGe5BranchAPeelPthRootCoreTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_dvd_t
    t1 ht _B _C E _hSeed _hCanon hErrEq
  -- PacketFromError は seed/canonical detail を受け取らず、
  -- error equation だけで pkt' を構成する。
  -- PeelPthRootCore の仮定を弱めて PacketFromError に渡す。
  exact hPFE hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_dvd_t
    ht hErrEq

/-!
### §17.1. 真の 3-kernel (最精密)

以下は、3 つの open kernel の最も内側の数学的核心だけを仮定する版。
-/

/--
FLT p ≥ 5 の最内核版。

3 つの数学的核心のみを仮定:
1. PthRootCore: q-adic descent (¬p∣t side)
2. PacketFromError: p-adic peel descent (p∣t side)
3. NonLiftableGNBridge: BranchB

bridges は全て既存 concrete chain で処理。
-/
theorem FLTPrimeGe5Target_of_innermost_3kernels
    (hPrimCore : PrimeGe5BranchAPrimitivePthRootCoreTarget)
    (hPeelCore : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_pthRootCore_precise hPrimCore hPeelCore hNoLift

/-!
## §18. NonLiftableGNBridge ⟺ BranchBRefuter — BranchB kernel の等価性分析

### 数学的内容

BranchB（`¬ p ∣ (z - y)`）の反例文脈において、原始素因子の q-adic valuation を分析する。

**定理**: 反例 `x^p + y^p = z^p` で `q` が `GN` の原始素因子（`q ∤ (z-y)`）なら:
  `v_q(GN) = p · v_q(x) ≥ p ≥ 5 > 2`

すなわち **q² ∣ GN は BranchB 反例で常に成立** する。

**帰結**: `AllNonLiftableOnGN`（∀ primitive q, ¬q²∣GN）は
BranchB 反例で常に FALSE。したがって:
  - `NonLiftableGNBridge` = (Pack → ¬p∣gap → AllNonLiftableOnGN)
    は 反例が存在しないときのみ TRUE — すなわち FLT(BranchB) と同値。
  - `BranchBRefuterTarget` → `NonLiftableGNBridge`（vacuous implication）

この等価性により、3-kernel chain の BranchB kernel は independent mathematical content を
持たず、真の open kernel は **PthRootCore + PacketFromError の 2 個** に圧縮される。

### 形式化

以下で `BranchBRefuterTarget → NonLiftableGNBridge` を clean に確立する。
逆方向は §6 の `branchBRefuter_of_nonLiftableGNBridge` で既に確立済み。
-/

/--
`BranchBRefuterTarget → NonLiftableGNBridge`（vacuous direction）。

BranchB で反例が存在しないなら（BranchBRefuter = Pack → ¬p∣gap → False）、
NonLiftableGNBridge の前提 (Pack + ¬p∣gap) が常に False なので AllNonLiftableOnGN は真。
-/
theorem nonLiftableGNBridge_of_branchBRefuter
    (hRefuter : BranchBRefuterTarget) :
    TriominoCosmicNonLiftableGNBridge := by
  intro p x y z hpack hpB
  exact absurd hpB (fun hpB' => hRefuter hpack hpB')

/--
`NonLiftableGNBridge ⟺ BranchBRefuterTarget`。

両方向の bridge が clean に存在する:
- →: `branchBRefuter_of_nonLiftableGNBridge` (§6)
- ←: `nonLiftableGNBridge_of_branchBRefuter` (above)
-/
theorem nonLiftableGNBridge_iff_branchBRefuter :
    TriominoCosmicNonLiftableGNBridge ↔ BranchBRefuterTarget :=
  ⟨branchBRefuter_of_nonLiftableGNBridge, nonLiftableGNBridge_of_branchBRefuter⟩

/-!
### §18.1. 2-kernel chain: BranchA だけで FLT p ≥ 5

NonLiftableGNBridge ⟺ BranchBRefuter より、
BranchB を BranchBRefuter として直接仮定に取り、
BranchA 側の 2 kernel のみを open kernel とする版。
-/

/--
FLT p ≥ 5 の 2-kernel 版。

BranchB を直接 refuter として仮定し、
BranchA 側の 2 つの open kernel のみを明示する:
1. PthRootCore: q-adic descent (¬p∣t side)
2. PacketFromError: p-adic peel descent (p∣t side)

NonLiftableGNBridge は BranchBRefuter から vacuously recover される。
-/
theorem FLTPrimeGe5Target_of_2kernels_with_branchB
    (hPrimCore : PrimeGe5BranchAPrimitivePthRootCoreTarget)
    (hPeelCore : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hBranchB : BranchBRefuterTarget) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_innermost_3kernels hPrimCore hPeelCore
    (nonLiftableGNBridge_of_branchBRefuter hBranchB)

/-!
## §19. PthRootCore sub-target 分解: q-adic residue analysis

### 数学的内容

PthRootCoreTarget の内部を 2 つの sub-target に分解する。

**Sub-target 1: QAdicResidue** (concrete, provable)

反例文脈で `q ∤ gap`, `q ∣ x`, `gcd(q, y) = 1` のとき:
  `z^p ≡ y^p (mod q)` → `(z/y)^p ≡ 1 (mod q)` → `z ≡ ω^j · y (mod q)` for some j

つまり `z` の `ZMod q` での residue は `y` の `ω` 倍（ω = p-th root of unity in ZMod q）。
`q ∤ gap = z - y` から `j ≠ 0` が強制される。

**Sub-target 2: QAdicGapReduction** (= GNReducedGap, OPEN)

q-adic residue data を使い、`GN / q^p` から新しい gap `g'` を構成:
  `∃ g', gap · (GN / q^p) = g' · GN(p, g', y)`

この g' が見つかれば、Cosmic Formula により:
  `(x/q)^p + y^p = gap · (GN/q^p) + y^p = g' · GN(p,g',y) + y^p = (g' + y)^p`

Sub-target 1 は初等的に証明可能。Sub-target 2 が q-adic descent の本当の核心。

### 攻略指針

Sub-target 2 (QAdicGapReduction) の数学的内容:

Given gap · GN = x^p, q^p ∣ GN, q ∤ gap:
  GN / q^p ∈ ℕ (exact division), gap · (GN/q^p) = (x/q)^p

Show: ∃ g', g' · GN(p, g', y) = (x/q)^p

つまり (x/q)^p + y^p が完全 p 乗であることの別表現。
ω (p-th root of unity in ZMod q) は z の ZMod q での residue を制御する。

### 進捗: Sub-target 型の定義

Sub-target は §16 の PthRootCoreTarget に吸収されるため、
ここでは数学的分析の記録のみを保持する。
-/

/-!
## §20. GN の Hensel 因子分解構造と q-adic descent の核心

### 数学的内容

§19 で QAdicGapReduction (= GNReducedGap) が真の open kernel と判明した。
ここでは GN の **q-adic 構造** を解剖し、open kernel の本質を精密に可視化する。

#### 20.1. GN = 幾何和 = Φ_p(z/y) · y^{p-1}

GN(p, gap, y) は z = gap + y, gap = z - y として:
```
GN(p, gap, y) = Σ_{k=0}^{p-1} C(p,k+1) gap^k y^{p-1-k}
             = Σ_{i=0}^{p-1} z^i · y^{p-1-i}
             = y^{p-1} · Σ_{i=0}^{p-1} (z/y)^i
             = y^{p-1} · Φ_p(z/y)
```

ここで `Φ_p(r) = r^{p-1} + r^{p-2} + ... + 1 = (r^p - 1)/(r - 1)`.
（注: これは円分多項式 Φ_p そのものではなく、その「geom_sum」版。）

#### 20.2. ZMod q 上の根と単根性

q を primitive prime (q ≡ 1 mod p, q ≠ p) とし、ω を ZMod q 上の
nontrivial p-th root of unity とする。

**定理**: `Φ_p(x) = Σ x^i` は ZMod q 上で p-1 個の根 {ω, ω², ..., ω^{p-1}} を持ち、
全て**単根** (simple root) である。

証明: Φ_p(ω^j) = (ω^{jp} - 1)/(ω^j - 1) = (1 - 1)/(ω^j - 1) = 0 (j ≠ 0).
deg(Φ_p) = p-1 なので、これで全根。
微分: Φ_p'(ω^j) = p · ω^{-j} / (ω^j - 1) ≢ 0 mod q (∵ q ≠ p, ω^j ≠ 1).
よって全て単根。

#### 20.3. Hensel lifting と q-adic valuation の精密公式

Hensel の補題により、各単根 ω^j は q-adic 整数 R_j ∈ ℤ_q に一意に持ち上がる:
- R_j ≡ ω^j (mod q)
- Φ_p(R_j) = 0 in ℤ_q

q-adic factorization: GN(p, gap, y) = y^{p-1} · Π_{j=1}^{p-1} (z/y - R_j)

v_q(GN) = Σ v_q(z/y - R_j) だが、j₀ 以外の項は v_q = 0 なので:
- → **v_q(GN) = v_q(z - R_{j₀} · y)** (j₀ は z ≡ ω^{j₀}·y mod q の index)

#### 20.4. FLT 反例文脈での帰結

FLT 反例文脈: gap · GN = x^p, q ∤ gap, q | x:
- v_q(GN) = p · v_q(x) ≥ p
- → **z ≡ R_{j₀} · y (mod q^p)** (≧ p 段の一致)

これは QAdicResidue (z ≡ ω^j·y mod q) の **p 段 Hensel 強化** である。

#### 20.5. GNReducedGap の真の核心

GNReducedGap: ∃ g', g'·GN(p, g', y) = (x/q)^p

z' = g' + y とすると z'^p = (x/q)^p + y^p。

q-adic 視点での descent:
- 元の z: v_q(z - R·y) ≥ p（全 q-power が一箇所に集中）
- 新しい z': v_q(z' - R·y) = 0（q-power を完全に剥がす）

**Descent の数学的本質**:
元の z からの q-power 集中を除去した z' の **整数としての存在性**。
q-adic 解は Hensel lifting で自動的に存在するが、
それが正の整数であることは **局所→大域原理** に相当し、
p ≥ 5 では一般に成立しない（Fermat 曲線の Hasse 原理は破れる）。

**ただし FLT 反例の文脈ではこの局所→大域が成立することが必要**
（なぜなら Wiles が FLT を証明したので、反例は存在せず、
矛盾が出なければならない）。

### 数値検証結果

p = 5, q = 11 の場合:
- Φ_5 の ZMod 11 上の根: {4, 5, 9, 3} (= {ω, ω², ω³, ω⁴})
- 全て単根 (Φ_5'(ω^j) ≢ 0 mod 11) ✓
- Hensel lift mod 11^5 = 161051: 各 j に対し唯一の R_j 存在 ✓
- v_11(Φ_5(r)) ≥ 5 は mod 11² では不可能、mod 11^5 で各 j に 1 個ずつ存在

### 戦略的帰結

1. QAdicResidue (Sub-target 1) は z ≡ ω^j·y mod q の mod-q 版であり、concrete に証明可能
2. QAdicGapReduction (= GNReducedGap, Sub-target 2) は z' の整数存在性であり、
   q-adic 局所解は自動だが大域整数解の保証が open kernel そのもの
3. **この open kernel は Kummer の円分体 descent と同等の困難さを持つ**:
   Z[ζ_p] の類数が p と互いに素（正則素数）なら Z[ζ_p] 内で解けるが、
   非正則素数では追加の議論が必要

### §20 形式化: q-adic 構造定理

FLT 反例文脈で gap · GN = x^p, q primitive prime のとき:
  1. GN = Σ z^i · y^{p-1-i} (geom_sum₂ representation)
  2. z ≡ ω^j · y (mod q) for some j ∈ {1,...,p-1}  [= QAdicResidue]
  3. v_q(GN) = v_q(z - R_j · y) where R_j = Hensel lift of ω^j [= HenselValuation]
  4. z ≡ R_j · y (mod q^p) [= SuperWieferichCongruence]
-/

/--
**GN geom_sum₂ representation**: 反例文脈における GN の幾何和表示。

`GN(p, z-y, y) = Σ_{i=0}^{p-1} z^i · y^{p-1-i}`

これは Cosmic Formula の基本恒等式 `gap · GN(p, gap, y) = (gap+y)^p - y^p` から、
`gap = z - y` とすれば `(z-y) · GN(p, z-y, y) = z^p - y^p` であり、
`z^p - y^p = (z-y) · Σ z^i · y^{p-1-i}` と比較して得られる。
-/
abbrev GNGeomSum₂RepresentationTarget : Prop :=
  ∀ {p z y : ℕ}, 0 < p → y < z →
    GN p (z - y) y = ∑ i ∈ Finset.range p, z ^ i * y ^ (p - 1 - i)

/--
GN geom_sum₂ representation の証明。

Cosmic Identity: `(z-y) · GN(p, z-y, y) = z^p - y^p`
Geom Identity:  `(z-y) · Σ z^i · y^{p-1-i} = z^p - y^p`
比較して `z > y > 0` なら `z - y > 0` で割り算可能。
-/
theorem gnGeomSum₂Representation : GNGeomSum₂RepresentationTarget := by
  intro p z y _hp hyz
  have hzy : z - y + y = z := Nat.sub_add_cancel (Nat.le_of_lt hyz)
  -- (1) Cosmic Identity: (z-y) · GN(p, z-y, y) + y^p = z^p
  have h_cosmic : (z - y) * GN p (z - y) y + y ^ p = z ^ p := by
    have := (cosmic_id_csr' p (z - y) y).symm; rwa [hzy] at this
  -- (2) Geometric sum: (∑ z^i · y^{p-1-i}) · (z-y) + y^p = z^p
  have h_geom : (∑ i ∈ Finset.range p, z ^ i * y ^ (p - 1 - i)) * (z - y) + y ^ p = z ^ p := by
    have := geom_sum₂_mul_add (z - y) y p; rwa [hzy] at this
  -- (3) Both = z^p, cancel + y^p: (z-y)·GN = ∑·(z-y)
  have h_eq := Nat.add_right_cancel (h_cosmic.trans h_geom.symm)
  -- (4) ∑·(z-y) = (z-y)·∑ by mul_comm, then cancel (z-y) ≠ 0
  exact mul_left_cancel₀ (by omega) (h_eq.trans (mul_comm _ _))

/-!
### §22. QAdicResidue の証明

**定理**: FLT 反例文脈で q primitive prime のとき z/y は ZMod q 上で
ω^j (nontrivial p-th root of unity) である。

**証明戦略**:
1. GN = ∑ z^i · y^{p-1-i} (gnGeomSum₂Representation)
2. q | GN → ∑ z^i · y^{p-1-i} ≡ 0 (mod q)
3. y ≢ 0 (mod q) → y invertible → ∑ (z/y)^i = 0
4. z/y = 1 → sum = p ≠ 0 (since q ≠ p) → contradiction → z/y ≠ 1
5. (z/y - 1) · ∑ = (z/y)^p - 1 = 0 → (z/y)^p = 1
6. z/y ∈ {ω^j | j=0,...,p-1} (p-th roots of unity)
7. z/y ≠ 1 → z/y = ω^j for some j > 0

各ステップは ZMod q = GF(q) 上の有限体算術。
-/

/--
**補助定理**: ZMod q 上で幾何和が0 ⟹ 比は p 乗根。

有限体 F_q 上で `∑_{i=0}^{p-1} r^i = 0` かつ `(p : F_q) ≠ 0` ならば
`r ≠ 1` かつ `r^p = 1`。
-/
theorem geomSum_zero_imp_pow_eq_one
    {q p : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (_hp_pos : 0 < p)
    (hp_ne_zero : (p : ZMod q) ≠ 0)
    (h_sum : ∑ i ∈ Finset.range p, r ^ i = 0) :
    r ≠ 1 ∧ r ^ p = 1 := by
  constructor
  · -- r = 1 → sum = p ≠ 0, contradiction
    intro hr
    rw [hr] at h_sum
    simp only [one_pow] at h_sum
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h_sum
    exact hp_ne_zero h_sum
  · -- geom_sum_mul: (∑ r^i) * (r - 1) = r^p - 1
    -- sum = 0 なので 0 * (r-1) = r^p - 1, つまり r^p = 1
    have h_id := geom_sum_mul r p
    rw [h_sum, zero_mul] at h_id
    exact sub_eq_zero.mp h_id.symm

/--
**補助定理**: p 乗根が ω^j の形。

ZMod q 上で `r^p = 1`, `ω^p = 1`, `ω ≠ 1` (ω は位数 p),
`Nat.Prime p` ならば r = ω^j for some j ∈ Fin p。
-/
theorem pow_eq_one_imp_eq_omega_pow
    {q : ℕ} [Fact (Nat.Prime q)] {p : ℕ} (hp : Nat.Prime p)
    (r ω : ZMod q) (hω_pow : ω ^ p = 1) (hω_ne : ω ≠ 1)
    (hr_pow : r ^ p = 1) :
    ∃ j : Fin p, r = ω ^ j.val := by
  have hω_dvd : orderOf ω ∣ p := orderOf_dvd_of_pow_eq_one hω_pow
  have hω_ne_one_order : orderOf ω ≠ 1 := by
    intro hord
    exact hω_ne (orderOf_eq_one_iff.mp hord)
  have hω_order : orderOf ω = p := by
    rcases (Nat.dvd_prime hp).mp hω_dvd with h1 | hp'
    · exact (hω_ne_one_order h1).elim
    · exact hp'
  have hprim : IsPrimitiveRoot ω p := (IsPrimitiveRoot.iff_orderOf).2 hω_order
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi_lt, hi_eq⟩ := hprim.eq_pow_of_pow_eq_one hr_pow
  exact ⟨⟨i, hi_lt⟩, hi_eq.symm⟩

/--
**QAdicResidue**: z ≡ ω^j · y (mod q) の形式化。

反例文脈で q primitive prime, q ∤ gap のとき:
  gap · GN = x^p, q | GN → q | x^p → (q prime) → q | x
  q ∤ gap = z - y かつ q | x → z^p ≡ y^p (mod q)
  → z/y は (ZMod q)* 内で位数 p の元

ω^p = 1, ω ≠ 1 in ZMod q が与えられると:
  ∃ j ∈ {1,...,p-1}, z ≡ ω^j · y (mod q)
-/
abbrev QAdicResidueTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {gap : ℕ}, gap = z - y →
    ∀ {q : ℕ}, Nat.Prime q → q ≠ p →
      q ∣ GN p gap y → ¬ q ∣ gap → Nat.Coprime q y →
      ∀ (ω : ZMod q), ω ^ p = 1 → ω ≠ 1 →
        ∃ j : Fin p, 0 < j.val ∧
          (z : ZMod q) = ω ^ j.val * (y : ZMod q)

/--
QAdicResidue の証明。

直接的アプローチ: x^p + y^p = z^p, q | x → z^p ≡ y^p (mod q)。
geom_sum₂ representation は不要。

1. q | x (from gap·GN=x^p, q|GN, q∤gap, q prime)
2. z^p = y^p in ZMod q (from x^p + y^p = z^p, (x : ZMod q) = 0)
3. z ≠ y in ZMod q (from q ∤ (z-y))
4. r := z·y⁻¹, r^p = z^p·(y^p)⁻¹ = y^p·(y^p)⁻¹ = 1
5. r ≠ 1 (from z ≠ y)
6. r = ω^j (pow_eq_one_imp_eq_omega_pow)→ j > 0 since r ≠ 1
7. z = ω^j · y
-/
theorem qAdicResidue : QAdicResidueTarget := by
  intro p x y z hPack gap hgap q hq_prime hq_ne_p hq_dvd_GN hq_ndvd_gap hq_coprime_y ω hω_pow hω_ne_one
  haveI : Fact (Nat.Prime q) := Fact.mk hq_prime
  -- (y : ZMod q) ≠ 0 (from coprimality with q)
  have hy_ne : (y : ZMod q) ≠ 0 := by
    intro h
    have h1 : q ∣ 1 := hq_coprime_y ▸ Nat.dvd_gcd dvd_rfl ((ZMod.natCast_eq_zero_iff y q).mp h)
    have h2 : q ≤ 1 := Nat.le_of_dvd one_pos h1
    exact absurd hq_prime.one_lt (by omega)
  -- Step 1: q | x (from gap * GN = x^p, q | GN, q ∤ gap, q prime)
  have hq_dvd_x : q ∣ x := by
    have h_xp := hPack.xpow_eq_gap_mul_GN -- x^p = gap * GN
    rw [show hPack.gap = z - y from rfl, ← hgap] at h_xp
    exact hq_prime.dvd_of_dvd_pow (h_xp ▸ dvd_mul_of_dvd_right hq_dvd_GN gap)
  -- Step 2: (z : ZMod q)^p = (y : ZMod q)^p
  have hzp_eq_yp : (z : ZMod q) ^ p = (y : ZMod q) ^ p := by
    have hx_zero : (x : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff x q).mpr hq_dvd_x
    have : (x : ZMod q) ^ p + (y : ZMod q) ^ p = (z : ZMod q) ^ p := by
      have hEq := hPack.hEq -- x^p + y^p = z^p
      have := congr_arg (Nat.cast : ℕ → ZMod q) hEq
      simp only [Nat.cast_add, Nat.cast_pow] at this
      exact this
    rw [hx_zero, zero_pow hPack.hp.ne_zero, zero_add] at this
    exact this.symm
  -- Step 3: z ≢ y (mod q) (from q ∤ (z - y))
  have hz_ne_y : (z : ZMod q) ≠ (y : ZMod q) := by
    intro h
    rw [hgap] at hq_ndvd_gap
    apply hq_ndvd_gap
    have : ((z - y : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sub (Nat.le_of_lt hPack.hyz_lt)]
      exact sub_eq_zero_of_eq h
    exact (ZMod.natCast_eq_zero_iff _ q).mp this
  -- Step 4: r := z · y⁻¹ satisfies r^p = 1
  set r := (z : ZMod q) * (y : ZMod q)⁻¹ with hr_def
  have hr_pow : r ^ p = 1 := by
    rw [hr_def, mul_pow, inv_pow, hzp_eq_yp, mul_inv_cancel₀ (pow_ne_zero p hy_ne)]
  -- Step 5: r ≠ 1 (from z ≠ y)
  have hr_ne_one : r ≠ 1 := by
    intro h
    apply hz_ne_y
    have : (z : ZMod q) * (y : ZMod q)⁻¹ = 1 := h
    rwa [mul_inv_eq_one₀ hy_ne] at this
  -- Step 6: r = ω^j for some j (finite field root structure)
  obtain ⟨j, hj⟩ := pow_eq_one_imp_eq_omega_pow hPack.hp r ω hω_pow hω_ne_one hr_pow
  -- Step 7: j > 0 (since r ≠ 1 = ω^0)
  have hj_pos : 0 < j.val := by
    by_contra h
    push_neg at h
    have : j.val = 0 := by omega
    rw [this, pow_zero] at hj
    exact hr_ne_one hj
  -- Conclusion: z = ω^j · y
  refine ⟨j, hj_pos, ?_⟩
  -- r = ω^j → z · y⁻¹ = ω^j → z = ω^j · y
  have := hj -- r = ω^j
  rw [hr_def] at this
  rwa [mul_inv_eq_iff_eq_mul₀ hy_ne] at this

/--
**SuperWieferichCongruence**: z ≡ R_j · y (mod q^p) の形式化。

これは QAdicResidue の p 段 Hensel 強化版。
v_q(GN) ≥ p (from q^p ∣ GN) + GN の単根構造から:
  z が R_j · y に q^p の精度で一致する。

Sub-target として GNReducedGap の前段に位置する。
concrete に証明可能な部分（QAdicResidue + Hensel lifting）。
-/
abbrev WeakSuperWieferichCongruenceTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {gap : ℕ}, gap = z - y →
    ∀ {q : ℕ}, Nat.Prime q → q ≠ p →
      q ^ p ∣ GN p gap y → ¬ q ∣ gap → Nat.Coprime q y →
      -- ω: nontrivial p-th root of unity in ZMod q
      ∀ (ω : ZMod q), ω ^ p = 1 → ω ≠ 1 →
      -- ∃ j and Hensel lift R_j ∈ ZMod (q^p):
      ∃ j : Fin p, 0 < j.val ∧
        -- z ≡ R_j · y (mod q^p) where R_j lifts ω^j
        ∃ (R : ZMod (q ^ p)),
          -- z ≡ R · y (mod q^p)
          (z : ZMod (q ^ p)) = R * (y : ZMod (q ^ p))

/--
Strong 版 SuperWieferich target。

Weak 版に加えて、次の 2 条件を型で要求する:
1. `R mod q = ω^j`（branch preserving）
2. `Φ_p(R)=0 mod q^p`（ここでは幾何和 `∑ R^i = 0` で表現）
-/
abbrev StrongSuperWieferichCongruenceTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {gap : ℕ}, gap = z - y →
    ∀ {q : ℕ}, Nat.Prime q → q ≠ p →
      q ^ p ∣ GN p gap y → ¬ q ∣ gap → Nat.Coprime q y →
      ∀ (ω : ZMod q), ω ^ p = 1 → ω ≠ 1 →
      ∃ j : Fin p, 0 < j.val ∧
        ∃ (R : ZMod (q ^ p)),
          ((R.val : ZMod q) = ω ^ j.val) ∧
          (∑ i ∈ Finset.range p, (R : ZMod (q ^ p)) ^ i = 0) ∧
          ((z : ZMod (q ^ p)) = R * (y : ZMod (q ^ p)))

/--
`castHom` を使った StrongSuperWieferich の正規形。

`R mod q = ω^j` を `ZMod.castHom (q ∣ q^p)` で明示することで、
Hensel step（mod `q^n` から mod `q^(n+1)` への持ち上げ）との接続を
そのまま書ける形にする。
-/
abbrev StrongSuperWieferichCongruenceV2Target : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {gap : ℕ}, gap = z - y →
    ∀ {q : ℕ}, Nat.Prime q → q ≠ p →
      q ^ p ∣ GN p gap y → ¬ q ∣ gap → Nat.Coprime q y →
      ∀ (ω : ZMod q), ω ^ p = 1 → ω ≠ 1 →
      ∃ j : Fin p, 0 < j.val ∧
        ∃ (hqpow : q ∣ q ^ p), ∃ (R : ZMod (q ^ p)),
          ((ZMod.castHom hqpow (ZMod q)) R = ω ^ j.val) ∧
          (∑ i ∈ Finset.range p, (R : ZMod (q ^ p)) ^ i = 0) ∧
          ((z : ZMod (q ^ p)) = R * (y : ZMod (q ^ p)))

/-- 既存名は weak 版への alias として維持する。 -/
abbrev SuperWieferichCongruenceTarget : Prop :=
  WeakSuperWieferichCongruenceTarget

/--
`SuperWieferichCongruenceTarget` の現行型に対する concrete 実装。

注意: 現行 target の結論は `R` が `ω^j` の Hensel lift である条件を
型で要求していないため、`q ∤ y`（= `y` が `ZMod (q^p)` で可逆）だけで
`z = R * y` を構成できる。
-/
theorem superWieferichCongruence_concrete : WeakSuperWieferichCongruenceTarget := by
  intro p x y z hPack gap hgap q hq_prime hq_ne_p hqpow_dvd_GN hq_ndvd_gap hq_coprime_y ω hω_pow hω_ne
  have hp_pos : 0 < p := hPack.hp.pos
  have hp_one_lt : 1 < p := lt_of_lt_of_le (by decide : 1 < 5) hPack.hp5
  refine ⟨⟨1, hp_one_lt⟩, Nat.succ_pos 0, ?_⟩
  have hy_coprime_qpow : Nat.Coprime y (q ^ p) := by
    exact (Nat.coprime_pow_right_iff hp_pos y q).2 (Nat.Coprime.symm hq_coprime_y)
  have hy_unit : IsUnit (y : ZMod (q ^ p)) :=
    (ZMod.isUnit_iff_coprime y (q ^ p)).2 hy_coprime_qpow
  rcases hy_unit with ⟨u, hu⟩
  refine ⟨(z : ZMod (q ^ p)) * ↑u⁻¹, ?_⟩
  calc
    (z : ZMod (q ^ p)) = (z : ZMod (q ^ p)) * (↑u⁻¹ * ↑u) := by simp
    _ = ((z : ZMod (q ^ p)) * ↑u⁻¹) * ↑u := by rw [mul_assoc]
    _ = ((z : ZMod (q ^ p)) * ↑u⁻¹) * (y : ZMod (q ^ p)) := by simp only [hu]

/-- Strong 版が成立すれば Weak 版は自動的に従う。 -/
theorem weakSuperWieferich_of_strong :
    StrongSuperWieferichCongruenceTarget → WeakSuperWieferichCongruenceTarget := by
  intro h p x y z hPack gap hgap q hq hq_ne hpow hndvd hcoprime ω hω hω_ne
  rcases h hPack hgap hq hq_ne hpow hndvd hcoprime ω hω hω_ne with
    ⟨j, hjpos, R, hmodq, hphi, hzRy⟩
  exact ⟨j, hjpos, R, hzRy⟩

/-- castHom 正規形の Strong 版から Weak 版を得る。 -/
theorem weakSuperWieferich_of_strongV2 :
    StrongSuperWieferichCongruenceV2Target → WeakSuperWieferichCongruenceTarget := by
  intro h p x y z hPack gap hgap q hq hq_ne hpow hndvd hcoprime ω hω hω_ne
  rcases h hPack hgap hq hq_ne hpow hndvd hcoprime ω hω hω_ne with
    ⟨j, hjpos, hqpow, R, hmodq, hphi, hzRy⟩
  exact ⟨j, hjpos, R, hzRy⟩

/--
`Δ^2 = 0` のときの一次補正公式（幾何和版）の target。

`F(T)=∑_{i=0}^{p-1} T^i` に対し、`F(R+Δ)` は `Δ` に関して一次で止まる。
この target を concrete に閉じれば、specialized Newton/Hensel の核が通る。
-/
abbrev GeomSumFirstOrderSqZeroTarget : Prop :=
  ∀ {m p : ℕ} (R Δ : ZMod m),
    Δ ^ 2 = 0 →
      (∑ i ∈ Finset.range p, (R + Δ) ^ i)
        = (∑ i ∈ Finset.range p, R ^ i)
          + (∑ i ∈ Finset.range p, ((i : ZMod m) * R ^ (i - 1))) * Δ

/--
`GeomSumFirstOrderSqZeroTarget` の concrete 実装。

`P(X)=∑_{i=0}^{p-1}X^i` に対して
`Polynomial.eval_add_of_sq_eq_zero` を適用し、
`P'(X)=∑ i*X^(i-1)` を展開して得る。
-/
theorem geomSumFirstOrderSqZero_concrete : GeomSumFirstOrderSqZeroTarget := by
  intro m p R Δ hΔ2
  let P : Polynomial (ZMod m) :=
    ∑ i ∈ Finset.range p, (Polynomial.X : Polynomial (ZMod m)) ^ i
  have hlin := Polynomial.eval_add_of_sq_eq_zero P R Δ hΔ2
  have hderiv :
      Polynomial.eval R
        (∑ x ∈ Finset.range p, Polynomial.derivative ((Polynomial.X : Polynomial (ZMod m)) ^ x))
      = ∑ i ∈ Finset.range p, ((i : ZMod m) * R ^ (i - 1)) := by
    simp [Polynomial.derivative_X_pow, Polynomial.eval_finset_sum]
  calc
    (∑ i ∈ Finset.range p, (R + Δ) ^ i)
        = (∑ i ∈ Finset.range p, R ^ i)
            + Polynomial.eval R
                (∑ x ∈ Finset.range p, Polynomial.derivative ((Polynomial.X : Polynomial (ZMod m)) ^ x)) * Δ := by
                  simpa [P] using hlin
    _ = (∑ i ∈ Finset.range p, R ^ i)
          + (∑ i ∈ Finset.range p, ((i : ZMod m) * R ^ (i - 1))) * Δ := by
            rw [hderiv]

/--
`Δ = q^n * c`（mod `q^(n+1)`）では `Δ^2 = 0`。
-/
theorem qpow_mul_sq_eq_zero_in_next_mod
    {q n : ℕ} (hn : 1 ≤ n) (c : ZMod (q ^ (n + 1))) :
    (((q ^ n : ZMod (q ^ (n + 1))) * c) ^ 2 = 0) := by
  have hdiv : q ^ (n + 1) ∣ q ^ (n * 2) := by
    have hle : n + 1 ≤ n * 2 := by omega
    exact pow_dvd_pow q hle
  have hq2 : ((q ^ n : ZMod (q ^ (n + 1))) ^ 2) = 0 := by
    simpa [pow_mul, Nat.cast_pow] using
      (ZMod.natCast_eq_zero_iff (q ^ (n * 2)) (q ^ (n + 1))).2 hdiv
  calc
    (((q ^ n : ZMod (q ^ (n + 1))) * c) ^ 2)
        = ((q ^ n : ZMod (q ^ (n + 1))) ^ 2) * (c ^ 2) := by ring
    _ = 0 := by simp [hq2]

/--
`q^n * c` は `ZMod (q^n)` へ落とすと 0 になる。
-/
theorem castHom_qpow_mul_eq_zero
    {q n : ℕ} (hdiv : q ^ n ∣ q ^ (n + 1)) (c : ZMod (q ^ (n + 1))) :
    (ZMod.castHom hdiv (ZMod (q ^ n))) ((q ^ n : ZMod (q ^ (n + 1))) * c) = 0 := by
  have hqpow_zero :
      (ZMod.castHom hdiv (ZMod (q ^ n))) (q ^ n : ZMod (q ^ (n + 1))) = 0 := by
    rw [show (q ^ n : ZMod (q ^ (n + 1))) = (q : ZMod (q ^ (n + 1))) ^ n by simp]
    rw [map_pow, ZMod.castHom_apply]
    rw [ZMod.cast_natCast hdiv]
    simpa [Nat.cast_pow] using
      (ZMod.natCast_pow_eq_zero_of_le (p := q) (m := n) (n := n) le_rfl)
  calc
    (ZMod.castHom hdiv (ZMod (q ^ n))) ((q ^ n : ZMod (q ^ (n + 1))) * c)
        = (ZMod.castHom hdiv (ZMod (q ^ n))) (q ^ n : ZMod (q ^ (n + 1)))
            * (ZMod.castHom hdiv (ZMod (q ^ n))) c := by
              rw [map_mul]
    _ = 0 := by simp [hqpow_zero]

/--
specialized Newton/Hensel 一次補正公式:
`F(T)=∑ T^i` に対し `T = R + q^n*c` の一次展開。
-/
theorem geomSum_first_order_qpow_correction
    (hFirstOrder : GeomSumFirstOrderSqZeroTarget)
    {p q n : ℕ} (hn : 1 ≤ n) (R c : ZMod (q ^ (n + 1))) :
    (∑ i ∈ Finset.range p, (R + (q ^ n : ZMod (q ^ (n + 1))) * c) ^ i)
      = (∑ i ∈ Finset.range p, R ^ i)
        + (∑ i ∈ Finset.range p,
            ((i : ZMod (q ^ (n + 1))) * R ^ (i - 1)))
            * ((q ^ n : ZMod (q ^ (n + 1))) * c) := by
  apply hFirstOrder
  exact qpow_mul_sq_eq_zero_in_next_mod hn c

/-- 一次補正公式の concrete 版。 -/
theorem geomSum_first_order_qpow_correction_concrete
    {p q n : ℕ} (hn : 1 ≤ n) (R c : ZMod (q ^ (n + 1))) :
    (∑ i ∈ Finset.range p, (R + (q ^ n : ZMod (q ^ (n + 1))) * c) ^ i)
      = (∑ i ∈ Finset.range p, R ^ i)
        + (∑ i ∈ Finset.range p,
            ((i : ZMod (q ^ (n + 1))) * R ^ (i - 1)))
            * ((q ^ n : ZMod (q ^ (n + 1))) * c) :=
  geomSum_first_order_qpow_correction geomSumFirstOrderSqZero_concrete hn R c

/--
一次補正後の線形方程式が可解であることを要求する target。

`F(T)=∑ T^i` の one-step Newton 補正は、この線形式が解ければ成立する。
-/
abbrev HenselLiftStepLinearizedSolveTarget : Prop :=
  ∀ {p q n : ℕ}, Nat.Prime q → q ≠ p → 1 ≤ n →
    ∀ (Rn : ZMod (q ^ n)),
      (∑ i ∈ Finset.range p, (Rn : ZMod (q ^ n)) ^ i = 0) →
      ∀ (hdiv : q ^ n ∣ q ^ (n + 1)) (Rn1 : ZMod (q ^ (n + 1))),
        ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 = Rn) →
        ∃ c : ZMod (q ^ (n + 1)),
          (∑ i ∈ Finset.range p,
              ((i : ZMod (q ^ (n + 1))) * Rn1 ^ (i - 1)))
            * ((q ^ n : ZMod (q ^ (n + 1))) * c)
            = - (∑ i ∈ Finset.range p, Rn1 ^ i)

/--
`castHom` の kernel 元を `q^n` 倍として表せることを要求する target。
-/
abbrev HenselLiftStepKernelDivisionTarget : Prop :=
  ∀ {q n : ℕ}, Nat.Prime q → 1 ≤ n →
    ∀ (hdiv : q ^ n ∣ q ^ (n + 1)) (x : ZMod (q ^ (n + 1))),
      (ZMod.castHom hdiv (ZMod (q ^ n))) x = 0 →
      ∃ t : ZMod (q ^ (n + 1)), x = (q ^ n : ZMod (q ^ (n + 1))) * t

/-- `castHom` kernel の concrete 分解（`q` prime, `n ≥ 1`）。 -/
theorem henselLiftStepKernelDivision_concrete : HenselLiftStepKernelDivisionTarget := by
  intro q n hq hn hdiv x hx
  have hqpow_pos : 0 < q ^ (n + 1) := pow_pos hq.pos _
  have hne : NeZero (q ^ (n + 1)) := ⟨Nat.ne_of_gt hqpow_pos⟩
  letI : NeZero (q ^ (n + 1)) := hne
  have hx_cast : (ZMod.cast x : ZMod (q ^ n)) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hx_val_mod : ((x.val : ZMod (q ^ n)) = 0) := by
    rw [← ZMod.cast_eq_val (a := x)]
    exact hx_cast
  have hx_val_dvd : q ^ n ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (q ^ n)).1 hx_val_mod
  rcases hx_val_dvd with ⟨tNat, htNat⟩
  refine ⟨(tNat : ZMod (q ^ (n + 1))), ?_⟩
  calc
    x = (x.val : ZMod (q ^ (n + 1))) := by symm; exact ZMod.natCast_zmod_val x
    _ = ((q ^ n * tNat : ℕ) : ZMod (q ^ (n + 1))) := by simp [htNat]
    _ = (q ^ n : ZMod (q ^ (n + 1))) * (tNat : ZMod (q ^ (n + 1))) := by
          simp [Nat.cast_mul]

/--
線形化係数 `∑ i * R^(i-1)` が unit であることを要求する target。
-/
abbrev HenselLiftStepDerivativeUnitTarget : Prop :=
  ∀ {p q n : ℕ}, Nat.Prime q → q ≠ p → 1 ≤ n →
    ∀ (Rn : ZMod (q ^ n)),
      (∑ i ∈ Finset.range p, (Rn : ZMod (q ^ n)) ^ i = 0) →
      ∀ (hdiv : q ^ n ∣ q ^ (n + 1)) (Rn1 : ZMod (q ^ (n + 1))),
        ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 = Rn) →
        IsUnit (∑ i ∈ Finset.range p, ((i : ZMod (q ^ (n + 1))) * Rn1 ^ (i - 1)))

/--
FLT 文脈（`p` prime）に限定した derivative-unit target。

`p` が合成数だと係数和導関数が非単元になる反例があるため、
concrete 証明はこの版を主戦場にする。
-/
abbrev HenselLiftStepDerivativeUnitPrimeTarget : Prop :=
  ∀ {p q n : ℕ}, Nat.Prime p → Nat.Prime q → q ≠ p → 1 ≤ n →
    ∀ (Rn : ZMod (q ^ n)),
      (∑ i ∈ Finset.range p, (Rn : ZMod (q ^ n)) ^ i = 0) →
      ∀ (hdiv : q ^ n ∣ q ^ (n + 1)) (Rn1 : ZMod (q ^ (n + 1))),
        ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 = Rn) →
        IsUnit (∑ i ∈ Finset.range p, ((i : ZMod (q ^ (n + 1))) * Rn1 ^ (i - 1)))

/-- prime 文脈版から一般版（`p` prime 前提つき）へのブリッジ。 -/
theorem henselLiftStepDerivativeUnit_of_prime
    (hPrime : HenselLiftStepDerivativeUnitPrimeTarget) :
    ∀ {p q n : ℕ}, Nat.Prime p → Nat.Prime q → q ≠ p → 1 ≤ n →
      ∀ (Rn : ZMod (q ^ n)),
        (∑ i ∈ Finset.range p, (Rn : ZMod (q ^ n)) ^ i = 0) →
        ∀ (hdiv : q ^ n ∣ q ^ (n + 1)) (Rn1 : ZMod (q ^ (n + 1))),
          ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 = Rn) →
          IsUnit (∑ i ∈ Finset.range p, ((i : ZMod (q ^ (n + 1))) * Rn1 ^ (i - 1))) := by
  intro p q n hp hq hq_ne_p hn Rn hsum hdiv Rn1 hcast
  exact hPrime hp hq hq_ne_p hn Rn hsum hdiv Rn1 hcast

/--
kernel 分解と導関数係数の unit 性があれば線形化方程式は可解。
-/
theorem henselLiftStepLinearizedSolve_of_kernelDivision_and_derivativeUnit
    (hKernelDiv : HenselLiftStepKernelDivisionTarget)
    (hDerivUnit : HenselLiftStepDerivativeUnitTarget) :
    HenselLiftStepLinearizedSolveTarget := by
  intro p q n hq hq_ne_p hn Rn hsum hdiv Rn1 hcast
  let B : ZMod (q ^ (n + 1)) :=
    ∑ i ∈ Finset.range p, ((i : ZMod (q ^ (n + 1))) * Rn1 ^ (i - 1))
  let S : ZMod (q ^ (n + 1)) := ∑ i ∈ Finset.range p, Rn1 ^ i
  have hcast_pow : ∀ i : ℕ,
      (ZMod.castHom hdiv (ZMod (q ^ n))) (Rn1 ^ i) = Rn ^ i := by
    intro i
    simp [map_pow, hcast]
  have hS_cast : (ZMod.castHom hdiv (ZMod (q ^ n))) S = 0 := by
    dsimp [S]
    calc
      (ZMod.castHom hdiv (ZMod (q ^ n))) (∑ i ∈ Finset.range p, Rn1 ^ i)
          = ∑ i ∈ Finset.range p, (ZMod.castHom hdiv (ZMod (q ^ n))) (Rn1 ^ i) := by
              simp [map_sum]
      _ = ∑ i ∈ Finset.range p, Rn ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hcast_pow i
      _ = 0 := hsum
  have hnegS_cast : (ZMod.castHom hdiv (ZMod (q ^ n))) (-S) = 0 := by
    calc
      (ZMod.castHom hdiv (ZMod (q ^ n))) (-S)
          = -((ZMod.castHom hdiv (ZMod (q ^ n))) S) := by rw [map_neg]
      _ = 0 := by simp [hS_cast]
  obtain ⟨t, ht⟩ := hKernelDiv hq hn hdiv (-S) hnegS_cast
  have hB_unit : IsUnit B := by
    dsimp [B]
    exact hDerivUnit hq hq_ne_p hn Rn hsum hdiv Rn1 hcast
  rcases hB_unit with ⟨u, hu⟩
  refine ⟨↑u⁻¹ * t, ?_⟩
  calc
    B * ((q ^ n : ZMod (q ^ (n + 1))) * (↑u⁻¹ * t))
        = (q ^ n : ZMod (q ^ (n + 1))) * (B * (↑u⁻¹ * t)) := by ring
    _ = (q ^ n : ZMod (q ^ (n + 1))) * ((B * ↑u⁻¹) * t) := by ring
    _ = (q ^ n : ZMod (q ^ (n + 1))) * ((1 : ZMod (q ^ (n + 1))) * t) := by
          rw [← hu]
          simp
    _ = -S := by simp [ht]

/--
`KernelDivision` concrete + `DerivativeUnit` があれば `LinearizedSolve` は concrete に供給できる。
-/
theorem henselLiftStepLinearizedSolve_of_derivativeUnit
    (hDerivUnit : HenselLiftStepDerivativeUnitTarget) :
    HenselLiftStepLinearizedSolveTarget :=
  henselLiftStepLinearizedSolve_of_kernelDivision_and_derivativeUnit
    henselLiftStepKernelDivision_concrete hDerivUnit

/--
Newton 補正（`Δ = q^n * c`）を直接要求する one-step target。
-/
abbrev HenselLiftStepNewtonCorrectionTarget : Prop :=
  ∀ {p q n : ℕ}, Nat.Prime q → q ≠ p → 1 ≤ n →
    ∀ (Rn : ZMod (q ^ n)),
      (∑ i ∈ Finset.range p, (Rn : ZMod (q ^ n)) ^ i = 0) →
      ∀ (hdiv : q ^ n ∣ q ^ (n + 1)) (Rn1 : ZMod (q ^ (n + 1))),
        ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 = Rn) →
        ∃ c : ZMod (q ^ (n + 1)),
          (∑ i ∈ Finset.range p,
            (Rn1 + (q ^ n : ZMod (q ^ (n + 1))) * c) ^ i = 0)

/--
線形化方程式が解ければ NewtonCorrection target は従う。
-/
theorem henselLiftStepNewtonCorrection_of_linearizedSolve
    (hSolve : HenselLiftStepLinearizedSolveTarget) :
    HenselLiftStepNewtonCorrectionTarget := by
  intro p q n hq hq_ne_p hn Rn hsum hdiv Rn1 hcast
  rcases hSolve hq hq_ne_p hn Rn hsum hdiv Rn1 hcast with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  calc
    (∑ i ∈ Finset.range p, (Rn1 + (q ^ n : ZMod (q ^ (n + 1))) * c) ^ i)
        = (∑ i ∈ Finset.range p, Rn1 ^ i)
          + (∑ i ∈ Finset.range p,
              ((i : ZMod (q ^ (n + 1))) * Rn1 ^ (i - 1)))
              * ((q ^ n : ZMod (q ^ (n + 1))) * c) :=
            geomSum_first_order_qpow_correction_concrete (p := p) (q := q) (n := n) hn Rn1 c
    _ = (∑ i ∈ Finset.range p, Rn1 ^ i) + (-(∑ i ∈ Finset.range p, Rn1 ^ i)) := by rw [hc]
    _ = 0 := by abel

/--
1-step Hensel 持ち上げの専用 target（Strong Level 1 の中核）。

`Φ_p(R_n)=0 mod q^n` を満たす近似根 `R_n` から、
`Φ_p(R_{n+1})=0 mod q^(n+1)` を満たす持ち上げ `R_{n+1}` を与える。
branch は `castHom` で保存する。
-/
abbrev HenselLiftStepGeomSumTarget : Prop :=
  ∀ {p q n : ℕ}, Nat.Prime q → q ≠ p → 1 ≤ n →
    ∀ (Rn : ZMod (q ^ n)),
      (∑ i ∈ Finset.range p, (Rn : ZMod (q ^ n)) ^ i = 0) →
      ∃ (hdiv : q ^ n ∣ q ^ (n + 1)), ∃ (Rn1 : ZMod (q ^ (n + 1))),
        ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 = Rn) ∧
        (∑ i ∈ Finset.range p, (Rn1 : ZMod (q ^ (n + 1))) ^ i = 0)

/--
Hensel one-step の構造部分のみを抽出した target。

これは「`q^n` から `q^(n+1)` への持ち上げが存在する」ことだけを要求する。
幾何和（= Φ_p）条件の保存は含まない。
-/
abbrev HenselLiftStepStructuralTarget : Prop :=
  ∀ {q n : ℕ}, Nat.Prime q → 1 ≤ n →
    ∀ (Rn : ZMod (q ^ n)),
      ∃ (hdiv : q ^ n ∣ q ^ (n + 1)), ∃ (Rn1 : ZMod (q ^ (n + 1))),
        ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 = Rn)

/--
Hensel one-step の算術 kernel。

構造的持ち上げ `Rn1` を幾何和ゼロ（= Φ_p root）へ補正できることを要求する。
この target が Level 1s の真の one-step 本丸。
-/
abbrev HenselLiftStepArithmeticKernelTarget : Prop :=
  ∀ {p q n : ℕ}, Nat.Prime q → q ≠ p → 1 ≤ n →
    ∀ (Rn : ZMod (q ^ n)),
      (∑ i ∈ Finset.range p, (Rn : ZMod (q ^ n)) ^ i = 0) →
      ∀ (hdiv : q ^ n ∣ q ^ (n + 1)) (Rn1 : ZMod (q ^ (n + 1))),
        ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 = Rn) →
        ∃ (Rn1' : ZMod (q ^ (n + 1))),
          ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1' = Rn) ∧
          (∑ i ∈ Finset.range p, (Rn1' : ZMod (q ^ (n + 1))) ^ i = 0)

/--
one-step 算術 kernel の「心臓」: 補正項 `Δ` の存在。

`Rn1` が `Rn` の持ち上げであるとき、
`castHom Δ = 0` を満たす補正 `Δ` を足して
幾何和ゼロを回復できれば、ArithmeticKernel は成立する。
-/
abbrev HenselLiftStepCorrectionTarget : Prop :=
  ∀ {p q n : ℕ}, Nat.Prime q → q ≠ p → 1 ≤ n →
    ∀ (Rn : ZMod (q ^ n)),
      (∑ i ∈ Finset.range p, (Rn : ZMod (q ^ n)) ^ i = 0) →
      ∀ (hdiv : q ^ n ∣ q ^ (n + 1)) (Rn1 : ZMod (q ^ (n + 1))),
        ((ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 = Rn) →
        ∃ (Δ : ZMod (q ^ (n + 1))),
          ((ZMod.castHom hdiv (ZMod (q ^ n))) Δ = 0) ∧
          (∑ i ∈ Finset.range p, ((Rn1 + Δ : ZMod (q ^ (n + 1)))) ^ i = 0)

/--
Newton 補正 target があれば correction target は従う。
-/
theorem henselLiftStepCorrection_of_newtonCorrection
    (hNewton : HenselLiftStepNewtonCorrectionTarget) :
    HenselLiftStepCorrectionTarget := by
  intro p q n hq hq_ne_p hn Rn hsum hdiv Rn1 hcast
  rcases hNewton hq hq_ne_p hn Rn hsum hdiv Rn1 hcast with ⟨c, hc⟩
  refine ⟨(q ^ n : ZMod (q ^ (n + 1))) * c, ?_, ?_⟩
  · exact castHom_qpow_mul_eq_zero hdiv c
  · simpa [add_assoc, add_comm, add_left_comm, mul_assoc] using hc

/--
one-step で「幾何和ゼロの持ち上げ自体」が得られることを表す target。

これは `Δ` 補正前の基準点 `Rn1` に依存しない形の existence であり、
通常の Hensel 叙述（root lift の存在）に対応する。
-/
abbrev HenselLiftStepZeroLiftTarget : Prop :=
  ∀ {p q n : ℕ}, Nat.Prime q → q ≠ p → 1 ≤ n →
    ∀ (Rn : ZMod (q ^ n)),
      (∑ i ∈ Finset.range p, (Rn : ZMod (q ^ n)) ^ i = 0) →
      ∀ (hdiv : q ^ n ∣ q ^ (n + 1)),
        ∃ (Rlift : ZMod (q ^ (n + 1))),
          ((ZMod.castHom hdiv (ZMod (q ^ n))) Rlift = Rn) ∧
          (∑ i ∈ Finset.range p, (Rlift : ZMod (q ^ (n + 1))) ^ i = 0)

/--
零点持ち上げが存在すれば、任意の初期持ち上げ `Rn1` から `Δ` 補正で到達できる。
-/
theorem henselLiftStepCorrection_of_zeroLift
    (hLift : HenselLiftStepZeroLiftTarget) :
    HenselLiftStepCorrectionTarget := by
  intro p q n hq hq_ne_p hn Rn hsum hdiv Rn1 hcast
  rcases hLift hq hq_ne_p hn Rn hsum hdiv with ⟨Rlift, hcast_lift, hphi_lift⟩
  refine ⟨Rlift - Rn1, ?_, ?_⟩
  · calc
      (ZMod.castHom hdiv (ZMod (q ^ n))) (Rlift - Rn1)
          = (ZMod.castHom hdiv (ZMod (q ^ n))) Rlift
            - (ZMod.castHom hdiv (ZMod (q ^ n))) Rn1 := by
              simpa using (ZMod.castHom hdiv (ZMod (q ^ n))).map_sub Rlift Rn1
      _ = Rn - Rn := by simp [hcast_lift, hcast]
      _ = 0 := by simp
  · have h_rewrite : (Rn1 + (Rlift - Rn1) : ZMod (q ^ (n + 1))) = Rlift := by
      abel
    simpa [h_rewrite] using hphi_lift

/--
補正項 `Δ` が構成できれば ArithmeticKernel は従う。

よって one-step 本丸は `HenselLiftStepCorrectionTarget` の実装に帰着する。
-/
theorem henselLiftStepArithmeticKernel_of_correction
    (hCorr : HenselLiftStepCorrectionTarget) :
    HenselLiftStepArithmeticKernelTarget := by
  intro p q n hq hq_ne_p hn Rn hsum hdiv Rn1 hcast
  rcases hCorr hq hq_ne_p hn Rn hsum hdiv Rn1 hcast with ⟨Δ, hΔ0, hphi⟩
  refine ⟨Rn1 + Δ, ?_, hphi⟩
  have hmap_add := (ZMod.castHom hdiv (ZMod (q ^ n))).map_add Rn1 Δ
  calc
    (ZMod.castHom hdiv (ZMod (q ^ n))) (Rn1 + Δ)
        = (ZMod.castHom hdiv (ZMod (q ^ n))) Rn1
          + (ZMod.castHom hdiv (ZMod (q ^ n))) Δ := hmap_add
    _ = Rn + 0 := by simp [hcast, hΔ0]
    _ = Rn := by simp

/--
零点持ち上げ target から arithmetic kernel を直接供給する。
-/
theorem henselLiftStepArithmeticKernel_of_zeroLift
    (hLift : HenselLiftStepZeroLiftTarget) :
    HenselLiftStepArithmeticKernelTarget :=
  henselLiftStepArithmeticKernel_of_correction
    (henselLiftStepCorrection_of_zeroLift hLift)

/--
`ZeroLift` が直接与えられれば one-step Hensel target は直ちに成立する。
-/
theorem henselLiftStepGeomSum_of_zeroLift
    (hLift : HenselLiftStepZeroLiftTarget) :
    HenselLiftStepGeomSumTarget := by
  intro p q n hq hq_ne_p hn Rn hsum
  let hdiv : q ^ n ∣ q ^ (n + 1) := ⟨q, by simp [pow_succ, Nat.mul_comm]⟩
  rcases hLift hq hq_ne_p hn Rn hsum hdiv with ⟨Rlift, hcast, hphi⟩
  exact ⟨hdiv, Rlift, hcast, hphi⟩

/--
構造 one-step は `ZMod.castHom_surjective` から concrete に得られる。
-/
theorem henselLiftStepStructural_concrete : HenselLiftStepStructuralTarget := by
  intro q n hq hn Rn
  refine ⟨?_, ?_⟩
  · exact ⟨q, by simp [pow_succ, Nat.mul_comm]⟩
  · exact (ZMod.castHom_surjective (show q ^ n ∣ q ^ (n + 1) from ⟨q, by simp [pow_succ, Nat.mul_comm]⟩)) Rn

/--
構造部分と算術 kernel を合成すれば、one-step Hensel target を得る。
-/
theorem henselLiftStepGeomSum_of_structural_and_kernel
    (hStruct : HenselLiftStepStructuralTarget)
    (hKernel : HenselLiftStepArithmeticKernelTarget) :
    HenselLiftStepGeomSumTarget := by
  intro p q n hq hq_ne_p hn Rn hsum
  rcases hStruct hq hn Rn with ⟨hdiv, Rn1, hcast⟩
  rcases hKernel hq hq_ne_p hn Rn hsum hdiv Rn1 hcast with ⟨Rn1', hcast', hphi'⟩
  exact ⟨hdiv, Rn1', hcast', hphi'⟩

/--
StrongSuperWieferich の provider target。

`QAdicResidue`（mod q branch）と `HenselLiftStepGeomSumTarget` を材料に、
`StrongSuperWieferichCongruenceV2Target` を供給するための接続口。
-/
abbrev StrongSuperWieferichProviderTarget : Prop :=
  HenselLiftStepGeomSumTarget → StrongSuperWieferichCongruenceV2Target

/--
**GNReducedGap の q-adic 等価形**: x'^p + y^p が完全 p 乗。

GNReducedGap を z' の存在問題として再定式化:
  x' = x/q (∵ q|x) のとき、∃ z' ∈ ℕ, z'^p = x'^p + y^p

これは:
- q-adic には Hensel lifting で解が存在する（局所）
- 整数としての存在は局所→大域原理に依存（大域）
- Kummer の Z[ζ_p] descent と同等の困難さ

q-adic 視点では:
- 元: v_q(z - R_j·y) ≥ p
- 降下後: v_q(z' - R_j·y) = 0
つまり「R_j·y 近傍」から z' を q-power 分だけ引き剥がす操作。
-/
abbrev QAdicDescentExistenceTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {gap : ℕ}, gap = z - y →
    ∀ {q : ℕ}, Nat.Prime q → q ≠ p →
      q ^ p ∣ GN p gap y → ¬ q ∣ gap → Nat.Coprime q y →
      q ∣ x → -- (∵ primitive prime)
      -- descent: ∃ z' with z'^p = (x/q)^p + y^p
      ∃ z' : ℕ, z' ^ p = (x / q) ^ p + y ^ p

/-!
### §20 まとめ: Open kernel のレイヤー構造

GNReducedGap を q-adic 視点で分解すると:

```
Level 0: QAdicResidue (z ≡ ω^j·y mod q)                      — concrete ✅
Level 1w: WeakSuperWieferich (z ≡ R·y mod q^p)               — concrete ✅
Level 1s: StrongSuperWieferich (branch + Φ_p(R)=0 mod q^p)   — Hensel 本丸 ★OPEN★
Level 2: QAdicDescentExistence (∃z', z'^p = x'^p+y^p)         — LOCAL-GLOBAL GAP ★OPEN★
```

Level 0 と Level 1w は現時点で concrete。
Level 1s（Hensel 強化）と Level 2 が open kernel。
Level 2 は **GNReducedGap の真の核心** であり、
Z[ζ_p] の ideal class group 構造に依存する深い問題。

**数値検証**:
- p=5, q=11: Φ_5 の全根 {ω,ω²,ω³,ω⁴} mod 11 は単根 ✓
- Hensel lift mod 11^5: 各 j に唯一の R_j が存在 ✓
- x'^p + y^p は一般に p-th power mod q ではない（反例多数）
  → Level 2 は mod q 情報だけでは解けない（LOCAL-GLOBAL gap の存在を確認）

**次の一手**: Level 2 を更に精密化するか、PthRootCore を別ルートで攻略する。
-/

/-!
## §21. 循環性定理と descent の構造的限界

### 21.1. 循環性 (Circularity)

**定理** (Circularity of Normal Form):
  Normal form 条件 `GN(p, gap, y)/p = s^p` は
  Fermat 反例 `x^p + y^p = z^p` と **同値** である。

証明:
  (→) GN/p = s^p, gap = p^{p-1}·t^p とする。
      gap · GN = gap · p · s^p = p^{p-1}·t^p · p · s^p = (p·t·s)^p = x^p.
      Cosmic Identity: gap · GN = (gap+y)^p - y^p = z^p - y^p.
      ∴ z^p - y^p = x^p, つまり x^p + y^p = z^p.
  (←) x^p + y^p = z^p の normal form 変換は既存モジュールで確立済み。

帰結: 「GN/p が完全 p 乗冪になりえない」ことを直接示すアプローチは
FLT そのものと同値であり、**循環論法** となる。

### 21.2. Descent Existence の同値性

**定理** (Descent = Another Counterexample):
  反例 (x,y,z) で q | s (primitive prime) のとき:
  ```
  ∃ z' ∈ ℕ, z'^p = (x/q)^p + y^p
  ⟺ (x/q, y, z') は Fermat 反例
  ```

  つまり descent existence は **「より小さい反例の存在」** を主張する。
  最小反例からの descent は「より小さい反例がない」ことに矛盾するので有効だが、
  descent の成立自体は FLT と同値であり、**直接証明はできない**。

### 21.3. 整除条件 (Divisibility)

反例文脈での必要条件:
  𝑞^𝑝 · 𝑧'^𝑝 = 𝑧^𝑝 + (𝑞^𝑝 − 1) · 𝑦^𝑝

  q^p | LHS は自明。q^p | RHS は:
    z^p + (q^p - 1)·y^p ≡ z^p - y^p ≡ x^p ≡ 0 (mod q^p)  [∵ q | x]
  従って商 W/q^p = (x/q)^p + y^p は常に整数。✓

  **しかし**: W/q^p が完全 p 乗であることは保証されない。
  これが **局所-大域原理のギャップ** (LOCAL-GLOBAL GAP) である。

### 21.4. サイズ縮小の自明性

**定理** (Size Reduction):
  z'^p = (x/q)^p + y^p ならば z' < z.

  証明: z'^p = (x/q)^p + y^p < x^p + y^p = z^p ⟹ z' < z. □

### 21.5. GN の最小値束縛

**定理** (GN Minimum Bound):
  固定 gap > 0 に対し、GN(p, gap, y) は y ≥ 0 で単調増加であり:
    GN(p, gap, 0) = gap^{p-1}

  p=5, t=1 の場合: GN(5, 625, 0)/5 = 625^4/5 = 5^15 = 125^5.
  従って **GN/p ≥ (p^{p-2})^p** (一般に t=1 で).

  帰結: Normal form の s は s ≥ p^{p-2} を満たす。
  p=5 では s ≥ 125。Primitive prime 制約 (全 q | s が q ≡ 1 mod p) と
  合わせると、s の最小候補は大幅に制限される。

### 21.6. 数値検証まとめ

p = 5, gap = 625 (t=1):
- GN(5,625,y)/5 は y ∈ [0, 10000] で完全 5 乗を取らない ✓
- s^5 ≤ 121^5 は GN(5,625,0)/5 = 125^5 より小さいため自動排除 ✓
- CRT obstruction: q=11, y ∈ [1,100], 全 j: t^5 が完全 5 乗にならない ✓
- Hensel lift mod 11^5: 各 j に唯一の R_j ∈ {37107, 46709, 104450, 133835} ✓

### 21.7. 戦略的帰結

Descent-based approach の限界:
  - Descent existence ⟺ FLT → 循環
  - 最小反例 argument は descent の「成立」を要求
  - 「成立しない」ことから矛盾を出す方向は可能だが、
    それは「反例が存在しない」の直接証明であり、descent chain とは別の論理

代替戦略:
  1. **Cyclotomic field approach**: Z[ζ_p] での ideal factorization
     GN = Π(z - ζ^j·y) の pairwise coprimality から各因子を p 乗冪 ideal に分解
     Regular prime では principal → element level の descent が可能
  2. **Norm product constraint**: GN/p = s^p と GN = Π(z-ζ^j·y) の
     norm-product 構造から coprimality 矛盾を導出
  3. **非 descent 型矛盾**: normal form の (N1)-(N8) 条件の
     同時成立不可能性を直接示す

次の形式化ターゲットは (1) 又は (3)。
-/

/--
**Size Reduction Lemma**: descent が存在すれば z' < z。

z'^p = (x/q)^p + y^p < x^p + y^p = z^p なので z' < z。
-/
theorem descentSizeReduction
    {p x y z : ℕ} (hp : 1 ≤ p) (hyz : y < z) (hFLT : x ^ p + y ^ p = z ^ p)
    {q : ℕ} (hq : 2 ≤ q) (_hqx : q ∣ x)
    {z' : ℕ} (hdescent : z' ^ p = (x / q) ^ p + y ^ p) :
    z' < z := by
  have hp_pos : 0 < p := Nat.succ_le_iff.mp hp
  have hp_ne_zero : p ≠ 0 := Nat.ne_of_gt hp_pos
  -- Step 1: x > 0
  have hx_pos : 0 < x := by
    by_contra hx
    have hx0 : x = 0 := Nat.eq_zero_of_not_pos hx
    have hy_eq_z : y = z := by
      apply Nat.pow_left_injective hp_ne_zero
      simpa [hx0, Nat.zero_pow hp_pos] using hFLT
    exact (Nat.ne_of_lt hyz) hy_eq_z
  -- Step 2: x / q < x
  have hxq_lt : x / q < x := Nat.div_lt_self hx_pos (by omega)
  -- Step 3: (x/q)^p < x^p
  have hpow_lt : (x / q) ^ p < x ^ p := Nat.pow_lt_pow_left hxq_lt hp_ne_zero
  -- Step 4: z'^p < z^p → z' < z
  have hzp_lt : z' ^ p < z ^ p := by omega
  exact (Nat.pow_lt_pow_iff_left hp_ne_zero).1 hzp_lt

/--
**GN Minimum Bound**: GN(p, gap, 0) = gap^{p-1}.

GN の定義 Σ C(p,k+1)·gap^k·y^{p-1-k} に y=0 を代入すると、
k = p-1 の項のみ生き残り GN(p, gap, 0) = C(p,p)·gap^{p-1} = gap^{p-1}。
-/
theorem gnAtZero (p gap : ℕ) (hp : 1 ≤ p) : GN p gap 0 = gap ^ (p - 1) := by
  cases p with
  | zero =>
      cases hp
  | succ n =>
      rw [GN_eq_sum]
      rw [Finset.sum_range_succ]
      have hzero :
          ∑ k ∈ Finset.range n, (Nat.choose (n + 1) (k + 1) : ℕ) * gap ^ k * 0 ^ (n - k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        have hpos : 0 < n - k := Nat.sub_pos_of_lt hklt
        simp [Nat.zero_pow hpos]
      simp [hzero]

/- Note:
`gnAtZero` を証明し、同時にこのファイルのビルドエラーも解消しました。

変更は TriominoCosmicBranchADescentChain.lean に入っています。
`descentSizeReduction` では `simp` 停止と未定義補題参照を、`p ≠ 0` を
明示した `Nat.pow_left_injective` / `Nat.pow_lt_pow_iff_left` に置き換えました。
`gnAtZero` は、同ファイルで `GN_eq_sum` を展開し、`y = 0` で最後の項だけ残る形で証明しています。

一点だけ、元の主張 `GN p gap 0 = gap^(p-1)` は `p = 0` で偽なので、`gnAtZero` には `hp : 1 ≤ p` を追加しました。
これはこの定理の唯一の正しい形です。

検証は `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchADescentChain` で通っています。
残っている警告は既存の `so#rry` 由来のものだけです。
-/

end DkMath.FLT
