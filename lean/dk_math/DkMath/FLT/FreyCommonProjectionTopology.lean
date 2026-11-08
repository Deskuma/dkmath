/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTailKernelVanishing

#print "file: DkMath.FLT.FreyCommonProjectionTopology"

/-! # 元の共通射影の開核
元の Krull 部分群位相と、既存の tame 値族の開核を接続する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の共通射影の核は、既存の tame 値族の核の逆像。 -/
theorem ResidualCyclicStage.commonProjection_kernel_eq_preimage :
    ((T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker : Set (inertiaSubgroupIn A ℚ)) =
      (QuotientGroup.mk : inertiaSubgroupIn A ℚ → tameInertiaQuotient A) ⁻¹'
        ((T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker : Set (tameInertiaQuotient A)) := by
  ext σ
  exact QuotientGroup.eq_one_iff _

/-- 追加の連続性 provider を要求せず、同じ慣性群の位相で開核を得る。 -/
theorem ResidualCyclicStage.commonProjection_kernel_isOpen :
    IsOpen ((T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker : Set (inertiaSubgroupIn A ℚ)) := by
  rw [T.commonProjection_kernel_eq_preimage A hp5 hq hqp haddr hA]
  exact (T.fixedKernelTameFamily_kernel_isOpen A hp5 hq hqp haddr hA).preimage QuotientGroup.continuous_mk
end
end DkMath.FLT.Frey.Source

