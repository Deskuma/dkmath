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

import DkMath.Lib.NumberTheory.InertiaKrullClosed
import Mathlib.FieldTheory.KummerExtension

#print "file: DkMath.Lib.NumberTheory.KummerPrimeQuotientExclusion"

/-! # 全有限上位体の冪根存在から有限 Galois 商の p 因子を排除
基礎体だけの p 可除性ではなく、全有限中間体での根の存在を使う。 -/
namespace DkMath.Lib.NumberTheory.KummerPrimeQuotient
open IntermediateField
/-- 全有限中間体が p 冪根を持てば、どの有限 Galois 商の位数にも p は現れない。 -/
theorem index_coprime_of_forall_pow_surjective
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : ∀ K' : IntermediateField K L, FiniteDimensional K K' →
      ∀ a : K', a ≠ 0 → ∃ b : K', b ^ p = a)
    (N : OpenNormalSubgroup (L ≃ₐ[K] L)) :
    (N.toSubgroup.index).Coprime p := by
  by_contra hcop
  have hdvd : p ∣ N.toSubgroup.index := by
    by_contra hnd
    exact hcop (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hnd))
  have hNc : IsClosed ((N.toSubgroup : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) :=
    N.toOpenSubgroup.isClosed
  set M : IntermediateField K L := IntermediateField.fixedField N.toSubgroup with hM
  have hfix : M.fixingSubgroup = N.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N.toSubgroup, hNc⟩
  have hfin : FiniteDimensional K M := by
    rw [← InfiniteGalois.isOpen_iff_finite M]
    rw [hfix]
    exact N.toOpenSubgroup.isOpen'
  have hgal : IsGalois K ↥M := by
    rw [← InfiniteGalois.normal_iff_isGalois M]
    rw [hfix]
    exact N.isNormal'
  have : (⟨N.toSubgroup, hNc⟩ : ClosedSubgroup (L ≃ₐ[K] L)).Normal := N.isNormal'
  have hcard : Nat.card (↥M ≃ₐ[K] ↥M) = N.toSubgroup.index := by
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient
      ⟨N.toSubgroup, hNc⟩).toEquiv).symm
  -- 有限商に p が現れると、Cauchy により位数 p の部分群が得られる。
  have hdvd' : p ∣ Fintype.card (↥M ≃ₐ[K] ↥M) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hdvd
  have := Fact.mk hp
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card p hdvd'
  set C : Subgroup (↥M ≃ₐ[K] ↥M) := Subgroup.zpowers τ with hC
  set K' : IntermediateField K ↥M := IntermediateField.fixedField C with hK'
  have hrank : Module.finrank ↥K' ↥M = p := by
    rw [hK', IntermediateField.finrank_fixedField_eq_card, hC, Nat.card_eq_fintype_card,
      Fintype.card_zpowers, hτ]
  have : IsCyclic ↥C := by
    rw [hC]
    infer_instance
  have hcyc : IsCyclic (↥M ≃ₐ[↥K'] ↥M) := by
    have hKc : IntermediateField.fixingSubgroup K' = C :=
      IntermediateField.fixingSubgroup_fixedField C
    have : IsCyclic ↥(IntermediateField.fixingSubgroup K') := by rw [hKc]; infer_instance
    exact isCyclic_of_surjective (IntermediateField.fixingSubgroupEquiv K').toMonoidHom
      (IntermediateField.fixingSubgroupEquiv K').surjective
  have hζ' : IsPrimitiveRoot (algebraMap K ↥K' ζ) p :=
    hζ.map_of_injective (algebraMap K ↥K').injective
  have hK : (primitiveRoots (Module.finrank ↥K' ↥M) ↥K').Nonempty := by
    rw [hrank]
    exact ⟨algebraMap K ↥K' ζ, (mem_primitiveRoots hp.pos).mpr hζ'⟩
  -- その固定体上の巡回 p 次拡大を Kummer 生成元で表示する。
  obtain ⟨α, hαmem, hadj⟩ := exists_root_adjoin_eq_top_of_isCyclic ↥K' ↥M hK
  rw [hrank] at hαmem
  obtain ⟨a₀, ha₀⟩ := hαmem
  have hbotM : α ∈ (⊥ : IntermediateField ↥K' ↥M) → False := by
    intro hα
    have htop : (⊤ : IntermediateField ↥K' ↥M) = ⊥ :=
      le_antisymm (hadj ▸ IntermediateField.adjoin_simple_le_iff.mpr hα) bot_le
    have h1 : Module.finrank ↥K' ↥M = 1 := by
      rw [← IntermediateField.finrank_bot' (F := ↥K') (E := ↥M), ← htop,
        IntermediateField.finrank_top]
    rw [hrank] at h1
    exact hp.one_lt.ne' h1
  by_cases ha₀0 : a₀ = 0
  · apply hbotM
    have : α ^ p = 0 := by rw [← ha₀, ha₀0, map_zero]
    have hα0 : α = 0 := pow_eq_zero_iff hp.ne_zero |>.mp this
    rw [hα0]
    exact zero_mem ⊥
  · have : FiniteDimensional K ↥(K'.map M.val) :=
      Module.Finite.equiv (IntermediateField.equivMap K' M.val).toLinearEquiv
    -- 正確な体内根を下の固定体から供給し、Kummer 生成元を降下させる。
    obtain ⟨b₁, hb₁⟩ := hdiv (K'.map M.val) inferInstance
      (IntermediateField.equivMap K' M.val a₀)
      (by simpa using (IntermediateField.equivMap K' M.val).injective.ne ha₀0)
    set b₀ : ↥K' := (IntermediateField.equivMap K' M.val).symm b₁ with hb₀
    have hb₀p : b₀ ^ p = a₀ := by
      apply (IntermediateField.equivMap K' M.val).injective
      rw [map_pow, hb₀, AlgEquiv.apply_symm_apply, hb₁]
    have hb₀0 : b₀ ≠ 0 := by
      intro h
      apply ha₀0
      rw [← hb₀p, h, zero_pow hp.ne_zero]
    set β : ↥M := algebraMap ↥K' ↥M b₀ with hβdef
    have hβ0 : β ≠ 0 := by
      simpa [hβdef] using (algebraMap ↥K' ↥M).injective.ne hb₀0
    have hβp : β ^ p = α ^ p := by
      rw [hβdef, ← map_pow, hb₀p, ha₀]
    have hα0 : α ≠ 0 := by
      intro h
      apply ha₀0
      apply (algebraMap ↥K' ↥M).injective
      rw [ha₀, h, zero_pow hp.ne_zero, map_zero]
    have hquot : (α / β) ^ p = 1 := by
      rw [div_pow, hβp, div_self (pow_ne_zero p hα0)]
    have : NeZero p := ⟨hp.ne_zero⟩
    have hζM : IsPrimitiveRoot (algebraMap K ↥M ζ) p :=
      hζ.map_of_injective (algebraMap K ↥M).injective
    obtain ⟨i, _, hi⟩ := hζM.eq_pow_of_pow_eq_one hquot
    apply hbotM
    rw [IntermediateField.mem_bot]
    refine ⟨algebraMap K ↥K' ζ ^ i * b₀, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply K ↥K' ↥M, hi, ← hβdef,
      div_mul_cancel₀ α hβ0]


end DkMath.Lib.NumberTheory.KummerPrimeQuotient

