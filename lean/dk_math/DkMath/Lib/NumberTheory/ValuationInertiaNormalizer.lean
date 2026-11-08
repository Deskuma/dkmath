/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.InertiaKrullClosed

#print "file: DkMath.Lib.NumberTheory.ValuationInertiaNormalizer"

/-! # 元の分解群は元の慣性群を正規化する
全 Galois 群に対する正規性を主張せず、同じ付値環の分解群に限定する。 -/
namespace DkMath.Lib.NumberTheory.ValuationInertia
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- 実際の慣性群の元は同じ付値環の分解群に属する。 -/
theorem mem_decomposition_of_mem_inertia (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ inertiaSubgroupIn A K) : σ ∈ A.decompositionSubgroup K := by
  obtain ⟨s, _, rfl⟩ := hσ
  exact s.property

/-- 慣性の剰余作用の核としての正規性を、全自己同型群内の像へ輸送する。 -/
theorem decomposition_conj_mem_inertia (A : ValuationSubring L) (σ τ : L ≃ₐ[K] L)
    (hσ : σ ∈ A.decompositionSubgroup K) (hτ : τ ∈ inertiaSubgroupIn A K) :
    σ * τ * σ⁻¹ ∈ inertiaSubgroupIn A K := by
  obtain ⟨t, ht, he⟩ := hτ
  have hN : (A.inertiaSubgroup K).Normal := by
    delta ValuationSubring.inertiaSubgroup
    exact MonoidHom.normal_ker _
  let s : A.decompositionSubgroup K := ⟨σ, hσ⟩
  refine ⟨s * t * s⁻¹, hN.conj_mem t ht s, ?_⟩
  rw [map_mul, map_mul, map_inv, he]
  rfl

/-- 逆向きの共役も同じ慣性群に属する。 -/
theorem decomposition_inv_conj_mem_inertia (A : ValuationSubring L) (σ τ : L ≃ₐ[K] L)
    (hσ : σ ∈ A.decompositionSubgroup K) (hτ : τ ∈ inertiaSubgroupIn A K) :
    σ⁻¹ * τ * σ ∈ inertiaSubgroupIn A K := by
  simpa only [inv_inv] using decomposition_conj_mem_inertia A σ⁻¹ τ
    ((A.decompositionSubgroup K).inv_mem hσ) hτ
end DkMath.Lib.NumberTheory.ValuationInertia

