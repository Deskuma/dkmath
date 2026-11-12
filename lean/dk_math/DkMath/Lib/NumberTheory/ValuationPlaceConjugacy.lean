/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Place-transitivity argument adapted from S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean,
blob bd12adb9f848a63454efd82d8e4797dd594826c3.
Modified: derive actual valuation-ring conjugacy; transport the actual inertia subgroups.
-/

import DkMath.Lib.NumberTheory.ValuationTameCharacter

#print "file: DkMath.Lib.NumberTheory.ValuationPlaceConjugacy"

/-!
# NOTE-031-004D: 同じ素数上の付値環と慣性群は共役である

整数閉包の中心素イデアルについてprofinite群の推移性を使い、中心の共役を得る。
031-001の整数分数表示によって、中心の共役を付値環そのものの共役へ戻す。
慣性は付値環の保存と全整元の剰余合同で特徴づけ、共役後も同じ合同が成立することを示す。
付値環と慣性群の住所を一緒に運ぶための数論的な接続である。
-/
namespace DkMath.Lib.NumberTheory.ValuationPlaceConjugacy
open ValuationInertia ValuationFrobenius.PlaceTransitivity
open ValuationTameCharacter.TameCharacter
open scoped Pointwise
local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "ℤ̄" => Zbar

/-- 同じq上の整数閉包の中心素イデアルは絶対ガロア群で共役となる。 -/
theorem exists_smul_center_eq {q : ℕ} (hq : q.Prime) {A A₀ : ValuationSubring ℚ̄}
    (hA : LiesOverPrime A q) (hA₀ : LiesOverPrime A₀ q) :
    ∃ g : ℚ̄ ≃ₐ[ℚ] ℚ̄, center A₀ = g • center A := by
  classical
  have := isGalois_Qbar
  have := isAlgebraic_Qbar
  have : Algebra.IsIntegral ℚ ℚ̄ := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  let : TopologicalSpace ℤ̄ := ⊥
  have : DiscreteTopology ℤ̄ := ⟨rfl⟩
  have : ContinuousSMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) ℤ̄ := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(b : ℚ̄)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : ℚ̄))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {(b : ℚ̄)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g • (b : ℚ̄) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ (b : ℚ̄))
  have : Algebra.IsInvariant ℤ ℤ̄ (ℚ̄ ≃ₐ[ℚ] ℚ̄) := ⟨fun b hb => by
    have hb' : (b : ℚ̄) ∈ Set.range (algebraMap ℚ ℚ̄) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : ℤ̄ => (z : ℚ̄)) (hb g)
    obtain ⟨r, hr⟩ := hb'
    have hrint : IsIntegral ℤ r := by
      have h := b.2
      rw [mem_integralClosure_iff, ← hr] at h
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℚ̄)
        (algebraMap ℚ ℚ̄).injective).mp h
    obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hrint
    refine ⟨n, Subtype.ext ?_⟩
    rw [← hr, ← hn]
    simp⟩
  have hu : (center A).under ℤ = (center A₀).under ℤ := by
    rw [center_under hq hA, center_under hq hA₀]
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := ℤ) (G := ℚ̄ ≃ₐ[ℚ] ℚ̄) (center A) (center A₀) hu


/-- 同じ素数qの上の二つの付値環自体が絶対ガロア群で共役となる。 -/
theorem exists_smul_eq {q : ℕ} (hq : q.Prime) {A B : ValuationSubring ℚ̄}
    (hA : LiesOverPrime A q) (hB : LiesOverPrime B q) :
    ∃ g : ℚ̄ ≃ₐ[ℚ] ℚ̄, g • A = B := by
  obtain ⟨g, hg⟩ := exists_smul_center_eq hq hA hB
  refine ⟨g, ?_⟩
  have key : ∀ s : Zbar, (s : ℚ̄) ∈ (g • A).nonunits ↔ (s : ℚ̄) ∈ B.nonunits := by
    intro s
    rw [mem_smul_nonunits_iff, ← mem_center_iff (A := B), hg,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_center_iff]
    have he : ((g⁻¹ • s : Zbar) : ℚ̄) = g.symm s := by
      rw [integralClosure.coe_smul, AlgEquiv.smul_def, AlgEquiv.aut_inv]
    rw [he]
  have hgA : LiesOverPrime (g • A) q := by
    change (q : ℚ̄) ∈ (g • A).nonunits
    rw [mem_smul_nonunits_iff, map_natCast]
    exact hA
  exact le_antisymm
    (le_of_forall_not_mem_nonunits hq hgA (fun s hs hb => hs ((key s).mpr hb)))
    (le_of_forall_not_mem_nonunits hq hB (fun s hs ha => hs ((key s).mp ha)))

/-- 付値環と自己同型を同時に共役すると、元の慣性所属は新しい慣性所属へ移る。 -/
theorem conj_mem_inertia_smul {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (g τ : L ≃ₐ[K] L) (hτ : τ ∈ inertiaSubgroupIn A K) :
    g * τ * g⁻¹ ∈ inertiaSubgroupIn (g • A) K := by
  have hd := (mem_inertiaSubgroupIn_iff.mp hτ).1
  have he (z : L) : g.symm ((g * τ * g⁻¹) z) = τ (g.symm z) := by
    change g.symm (g (τ (g.symm z))) = _
    rw [g.symm_apply_apply]
  apply mem_inertiaSubgroupIn_of_forall
  · intro z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change g.symm ((g * τ * g⁻¹) z) ∈ A ↔ g.symm z ∈ A
    rw [he, apply_mem_iff hd]
  · intro z hz
    rw [mem_smul_nonunits_iff, map_sub, he]
    exact apply_sub_self_mem_nonunits hτ
      (by
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hz
        exact hz)

/-- 同時共役した付値環の慣性群は、元の慣性群の共役像そのものである。 -/
theorem inertia_smul {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (g : L ≃ₐ[K] L) :
    inertiaSubgroupIn (g • A) K =
      (inertiaSubgroupIn A K).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · intro τ hτ
    have hback := conj_mem_inertia_smul (g • A) g⁻¹ τ hτ
    rw [inv_smul_smul] at hback
    refine ⟨g⁻¹ * τ * g, ?_, ?_⟩
    · change g⁻¹ * τ * g ∈ inertiaSubgroupIn A K at hback
      exact hback
    · change g * (g⁻¹ * τ * g) * g⁻¹ = τ
      group
  · rintro _ ⟨τ, hτ, rfl⟩
    exact conj_mem_inertia_smul A g τ hτ

end DkMath.Lib.NumberTheory.ValuationPlaceConjugacy
