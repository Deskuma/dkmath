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

end DkMath.FLT
