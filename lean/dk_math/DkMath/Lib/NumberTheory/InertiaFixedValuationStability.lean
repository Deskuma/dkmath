/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalTailField
import Mathlib.FieldTheory.Galois.Infinite

#print "file: DkMath.Lib.NumberTheory.InertiaFixedValuationStability"

/-! # 慣性固定体上の付値安定性
分解群の Krull 閉性から導く。安定性を新しい入力として要求しない。 -/
namespace DkMath.Lib.NumberTheory.InertiaStability
open scoped Pointwise
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
theorem isClosed_apply_mem [Algebra.IsIntegral K L] (A : ValuationSubring L) (x : L) :
    IsClosed {σ : L ≃ₐ[K] L | σ x ∈ A} := by
  rw [← isOpen_compl_iff]
  have hcompl : {σ : L ≃ₐ[K] L | σ x ∈ A}ᶜ =
      ⋃ σ₀ ∈ {σ : L ≃ₐ[K] L | σ x ∉ A},
        σ₀ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    ext σ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      refine ⟨σ, h, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
    · rintro ⟨σ₀, h₀, hmem⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem
      have hfix : (σ₀⁻¹ * σ) • x = x := hmem
      rw [mul_smul] at hfix
      have hx : σ • x = σ₀ • x := by
        have := congrArg (σ₀ • ·) hfix
        simpa [smul_smul] using this
      intro hA
      apply h₀
      have : σ₀ x = σ x := by simpa [AlgEquiv.smul_def] using hx.symm
      rwa [this]
  rw [hcompl]
  exact isOpen_biUnion fun σ₀ _ =>
    (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ₀

theorem isClosed_decompositionSubgroup [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    IsClosed ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) := by
  have hS : IsClosed {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} := by
    have hset : {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} =
        ⋂ x ∈ (A : Set L), {σ : L ≃ₐ[K] L | σ x ∈ A} := by
      ext σ; simp
    rw [hset]
    exact isClosed_biInter fun x _ => isClosed_apply_mem A x
  have hset : ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) =
      {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} ∩
        (fun σ : L ≃ₐ[K] L => σ⁻¹) ⁻¹' {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} := by
    ext σ
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro hσ
      have h : σ • A = A := hσ
      constructor
      · intro x hx
        have hmem : σ • x ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ x A hx
        rw [h] at hmem
        simpa [AlgEquiv.smul_def] using hmem
      · intro x hx
        rw [← h] at hx
        have := ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp hx
        simpa [AlgEquiv.smul_def] using this
    · rintro ⟨h₁, h₂⟩
      change σ • A = A
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      constructor
      · intro hy
        have := h₁ _ hy
        simpa [AlgEquiv.smul_def, smul_inv_smul] using this
      · intro hy
        simpa [AlgEquiv.smul_def] using h₂ y hy
  rw [hset]
  exact hS.inter (hS.preimage continuous_inv)

theorem fixingSubgroup_fixedField_map_inertia_le [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) :
    (IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype)).fixingSubgroup ≤
      A.decompositionSubgroup K := by
  have hle : (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ≤
      A.decompositionSubgroup K := by
    rintro σ ⟨τ, _, rfl⟩
    exact τ.2
  have hff : IntermediateField.fixedField (A.decompositionSubgroup K) ≤
      IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype) :=
    IntermediateField.fixedField_le hle
  have hfix := IntermediateField.fixingSubgroup_antitone hff
  refine hfix.trans (le_of_eq ?_)
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨A.decompositionSubgroup K, isClosed_decompositionSubgroup A⟩

theorem smul_eq_self_of_mem_fixingSubgroup [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ (IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype)).fixingSubgroup) :
    σ • A = A :=
  fixingSubgroup_fixedField_map_inertia_le A hσ


/-- 元の慣性固定体を含む中間体上の自己同型は、元の付値環を保存する。 -/
theorem overfield_stable (A : ValuationSubring (AlgebraicClosure ℚ))
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : InertiaResidue.fixedField A ≤ E)
    (σ : AlgebraicClosure ℚ ≃ₐ[E] AlgebraicClosure ℚ)
    (x : AlgebraicClosure ℚ) (hx : x ∈ A) : σ x ∈ A := by
  let σ₀ := σ.restrictScalars ℚ
  have hfix : σ₀ ∈ (InertiaResidue.fixedField A).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    change σ y = y
    have he : y = algebraMap E (AlgebraicClosure ℚ) ⟨y, hE hy⟩ := rfl
    rw [he, AlgEquiv.commutes]
  have hs : σ₀ • A = A := smul_eq_self_of_mem_fixingSubgroup A σ₀ hfix
  have hm := ValuationSubring.smul_mem_pointwise_smul σ₀ x A hx
  rw [hs] at hm
  exact hm
end DkMath.Lib.NumberTheory.InertiaStability

