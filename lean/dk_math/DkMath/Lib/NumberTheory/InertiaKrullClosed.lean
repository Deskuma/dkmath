/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: closed inertia, Kummer prime-to-p quotients and actual inertia-tail roots.
-/

import DkMath.Lib.NumberTheory.InertiaFixedValuationStability

#print "file: DkMath.Lib.NumberTheory.InertiaKrullClosed"

/-! # 慣性群の Krull 閉性と固定体の回収
根を固定する群から元の慣性へ戻すため、閉包との混同を排除する。 -/
namespace DkMath.Lib.NumberTheory.InertiaClosed
open scoped Pointwise
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
theorem fixedField_topologicalClosure_eq [Algebra.IsIntegral K L]
    (H : Subgroup (L ≃ₐ[K] L)) :
    IntermediateField.fixedField H.topologicalClosure = IntermediateField.fixedField H := by
  refine le_antisymm (IntermediateField.fixedField_le (Subgroup.le_topologicalClosure H)) ?_
  intro x hx
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro σ hσ
  have hstab : (↑H : Set (L ≃ₐ[K] L)) ⊆
      (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    intro τ hτ
    simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] using hx τ hτ
  have hclosed : IsClosed (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) :=
    Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral (K := K) x)
  have hsub : closure (↑H : Set (L ≃ₐ[K] L)) ⊆
      (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) :=
    closure_minimal hstab hclosed
  have hσ' : σ ∈ closure (↑H : Set (L ≃ₐ[K] L)) := by
    rwa [← Subgroup.topologicalClosure_coe]
  simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] using hsub hσ'

theorem fixingSubgroup_fixedField_eq_topologicalClosure [IsGalois K L]
    [Algebra.IsIntegral K L] (H : Subgroup (L ≃ₐ[K] L)) :
    (IntermediateField.fixedField H).fixingSubgroup = H.topologicalClosure := by
  rw [← fixedField_topologicalClosure_eq H]
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨H.topologicalClosure, Subgroup.isClosed_topologicalClosure H⟩

theorem exists_mem_apply_eq_of_mem_fixingSubgroup [IsGalois K L] [Algebra.IsIntegral K L]
    (H : Subgroup (L ≃ₐ[K] L)) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ (IntermediateField.fixedField H).fixingSubgroup) (x : L) :
    ∃ τ ∈ H, τ x = σ x := by
  have hσc : σ ∈ closure (↑H : Set (L ≃ₐ[K] L)) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact (fixingSubgroup_fixedField_eq_topologicalClosure H) ▸ hσ
  have hU : IsOpen (σ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L))) :=
    (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ
  have hσU : σ ∈ σ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp
  obtain ⟨τ, hτU, hτH⟩ := mem_closure_iff.mp hσc _ hU hσU
  refine ⟨τ, hτH, ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hτU
  have : (σ⁻¹ * τ) • x = x := hτU
  rw [mul_smul] at this
  have := congrArg (σ • ·) this
  simpa [smul_smul, AlgEquiv.smul_def] using this

theorem isOpen_setOf_apply [Algebra.IsIntegral K L] (Q : L → Prop) (x : L) :
    IsOpen {σ : L ≃ₐ[K] L | Q (σ x)} := by
  have h : {σ : L ≃ₐ[K] L | Q (σ x)} = ⋃ σ₀ ∈ {σ : L ≃ₐ[K] L | Q (σ x)},
      σ₀ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hσ
      refine ⟨σ, hσ, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
    · rintro ⟨σ₀, h₀, hmem⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem
      have hfix : (σ₀⁻¹ * σ) • x = x := hmem
      rw [mul_smul] at hfix
      have hx : σ • x = σ₀ • x := by
        have := congrArg (σ₀ • ·) hfix
        simpa [smul_smul] using this
      have : σ x = σ₀ x := by simpa [AlgEquiv.smul_def] using hx
      rw [this]
      exact h₀
  rw [h]
  exact isOpen_biUnion fun σ₀ _ => (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ₀

theorem isClosed_setOf_apply [Algebra.IsIntegral K L] (Q : L → Prop) (x : L) :
    IsClosed {σ : L ≃ₐ[K] L | Q (σ x)} := by
  rw [← isOpen_compl_iff]
  have : {σ : L ≃ₐ[K] L | Q (σ x)}ᶜ = {σ : L ≃ₐ[K] L | ¬ Q (σ x)} := by ext; simp
  rw [this]
  exact isOpen_setOf_apply (fun y => ¬ Q y) x

theorem mem_inertia_map_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ↔
      σ ∈ A.decompositionSubgroup K ∧ ∀ a : A, A.valuation (σ a - a) < 1 := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨τ.2, fun a => ?_⟩
    change τ ∈ MonoidHom.ker (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A)) at hτ
    rw [MonoidHom.mem_ker] at hτ
    have h1 : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := RingEquiv.congr_fun hτ _
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff] at h1
    exact h1
  · rintro ⟨hD, hv⟩
    refine ⟨⟨σ, hD⟩, ?_, rfl⟩
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) ∈ MonoidHom.ker (MulSemiringAction.toRingAut
      (A.decompositionSubgroup K) (IsLocalRing.ResidueField A))
    rw [MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    exact hv a

theorem isClosed_inertia_map [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    IsClosed (((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype : Subgroup (L ≃ₐ[K] L)) :
      Set (L ≃ₐ[K] L)) := by
  have hset : (((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype : Subgroup (L ≃ₐ[K] L)) :
      Set (L ≃ₐ[K] L)) =
      ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) ∩
        ⋂ a : A, {σ : L ≃ₐ[K] L | A.valuation (σ a - a) < 1} := by
    ext σ
    rw [SetLike.mem_coe, mem_inertia_map_iff, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter]
    rfl
  rw [hset]
  exact (InertiaStability.isClosed_decompositionSubgroup A).inter
    (isClosed_iInter fun a => isClosed_setOf_apply (fun y => A.valuation (y - a) < 1) a)

theorem topologicalClosure_inertia_map [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype).topologicalClosure =
      (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype :=
  le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_inertia_map A))
    (Subgroup.le_topologicalClosure _)


/-- 実際の慣性固定体の固定群は、閉包ではなく元の慣性群そのもの。 -/
theorem fixingSubgroup_fixedField_inertia [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) :
    (IntermediateField.fixedField (ValuationInertia.inertiaSubgroupIn A K)).fixingSubgroup =
      ValuationInertia.inertiaSubgroupIn A K := by
  rw [fixingSubgroup_fixedField_eq_topologicalClosure]
  exact topologicalClosure_inertia_map A
end DkMath.Lib.NumberTheory.InertiaClosed

