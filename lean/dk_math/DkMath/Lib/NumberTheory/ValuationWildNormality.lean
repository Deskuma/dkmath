/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationWildRigidity
import DkMath.Lib.NumberTheory.ValuationTameCharacter

#print "file: DkMath.Lib.NumberTheory.ValuationWildNormality"

/-!
# 同じ付値環の分解群による野生合同の保存

全非零元の合同を、分解群が非単元を保存することから共役で輸送する。
別の ramification filtration との同値や pro-q 性は仮定しない。
-/
namespace DkMath.Lib.NumberTheory.ValuationWildRigidity
open ValuationTameCharacter.TameCharacter
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- 同じ付値環の分解群による共役は、全非零元の野生合同を保存する。 -/
theorem IsWildAt.conjugate {σ g : L ≃ₐ[K] L} (hσ : IsWildAt A σ)
    (hg : g ∈ A.decompositionSubgroup K) : IsWildAt A (g * σ * g⁻¹) := by
  apply (isWildAt_iff A).mpr
  intro z hz
  have hz' : g⁻¹ z ≠ 0 := (map_ne_zero g⁻¹).mpr hz
  have h := (isWildAt_iff A).mp hσ (g⁻¹ z) hz'
  have hgg : g (g⁻¹ z) = z := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have he : (g * σ * g⁻¹) z * z⁻¹ - 1 = g (σ (g⁻¹ z) * (g⁻¹ z)⁻¹ - 1) := by
    rw [map_sub, map_mul, map_inv₀, map_one, hgg, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
  rw [he, apply_mem_nonunits_iff hg]
  exact h

/-- 野生合同部分群は、元の慣性群へ引き戻すと正規部分群になる。 -/
instance inertiaWild_normal :
    ((wildSubgroup (K := K) A).comap (ValuationInertia.inertiaSubgroupIn A K).subtype).Normal where
  conj_mem σ hσ g := by
    change IsWildAt A (g.val * σ.val * g.val⁻¹)
    exact IsWildAt.conjugate A hσ (mem_inertiaSubgroupIn_iff.mp g.property).1

end DkMath.Lib.NumberTheory.ValuationWildRigidity
