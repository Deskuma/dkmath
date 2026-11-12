/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_pow_eq_of_kummer_descent.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.InertiaFixedValuationStability
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

#print "file: DkMath.Lib.NumberTheory.StableValuationHenselian"

/-! # 安定付値の Hensel 性
単根の全ての共役を比較し、唯一の剰余根を固定体へ降下する。 -/
namespace DkMath.Lib.NumberTheory.StableValuation
noncomputable section
open Polynomial
variable {L : Type*} [Field L]

theorem isUnit_iff_inv_mem (P : ValuationSubring L) (y : P) (hy : (y : L) ≠ 0) :
    IsUnit y ↔ (y : L)⁻¹ ∈ P := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : Pˣ) : P) * y = 1 := by rw [← hu, Units.inv_mul]
    have h1' := congrArg ((↑) : P → L) h1
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1'
    have h2 : (((u⁻¹ : Pˣ) : P) : L) = (y : L)⁻¹ := eq_inv_of_mul_eq_one_left h1'
    rw [← h2]; exact SetLike.coe_mem _
  · intro h
    exact IsUnit.of_mul_eq_one ⟨(y : L)⁻¹, h⟩ (Subtype.ext (mul_inv_cancel₀ hy))

theorem mem_maximalIdeal_iff (P : ValuationSubring L) (y : P) :
    y ∈ IsLocalRing.maximalIdeal P ↔ (y : L) = 0 ∨ (y : L)⁻¹ ∉ P := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hy : (y : L) = 0
  · have : y = 0 := Subtype.ext hy
    simp [this]
  · rw [isUnit_iff_inv_mem P y hy]; simp [hy]

variable {K : Type*} [Field K] [Algebra K L]

theorem mem_maximalIdeal_iff_map (P : ValuationSubring L)
    (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P) (σ : L ≃ₐ[K] L) (y : L) (hy : y ∈ P) :
    (⟨y, hy⟩ : P) ∈ IsLocalRing.maximalIdeal P ↔ (⟨σ y, hstab σ y hy⟩ : P) ∈ IsLocalRing.maximalIdeal P := by
  rw [mem_maximalIdeal_iff, mem_maximalIdeal_iff]
  change (y = 0 ∨ y⁻¹ ∉ P) ↔ (σ y = 0 ∨ (σ y)⁻¹ ∉ P)
  have h0 : σ y = 0 ↔ y = 0 := ⟨fun h => σ.injective (h.trans (map_zero σ).symm), fun h => by rw [h, map_zero]⟩
  rw [h0, ← map_inv₀]
  apply or_congr Iff.rfl
  rw [not_iff_not]
  constructor
  · exact hstab σ _
  · intro h
    have := hstab σ.symm _ h
    rwa [AlgEquiv.symm_apply_apply] at this

theorem hensel_of_stable [IsAlgClosed L] [IsGalois K L] (P : ValuationSubring L)
    (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P) (R : ValuationSubring K)
    (hR : ∀ k : K, k ∈ R ↔ algebraMap K L k ∈ P) (f : R[X]) (hf : f.Monic) (a₀ : R)
    (ha₀ : f.eval a₀ ∈ IsLocalRing.maximalIdeal R) (hunit : IsUnit (f.derivative.eval a₀)) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal R := by
  classical
  let ψ : R →+* P :=
    { toFun := fun k => ⟨algebraMap K L k, (hR k).mp k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hψ : ∀ k : R, ((ψ k : P) : L) = algebraMap K L k := fun k => rfl
  let θ : R →+* L := P.subtype.comp ψ
  have hθ : ∀ k : R, θ k = algebraMap K L k := fun k => rfl
  have hθinj : Function.Injective θ := fun a b h => Subtype.ext ((algebraMap K L).injective h)
  have hrefl : ∀ k : R, IsUnit (ψ k) → IsUnit k := by
    intro k hk
    have hk0 : ((ψ k : P) : L) ≠ 0 := by
      intro h0
      have : ψ k = 0 := Subtype.ext h0
      rw [this] at hk
      exact not_isUnit_zero hk
    have hinv : (algebraMap K L k)⁻¹ ∈ P := (isUnit_iff_inv_mem P (ψ k) hk0).mp hk
    have hk0' : (k : K) ≠ 0 := by
      intro h; apply hk0; rw [hψ, h, map_zero]
    have hmem : (k : K)⁻¹ ∈ R := by
      rw [hR, map_inv₀]; exact hinv
    exact IsUnit.of_mul_eq_one ⟨(k : K)⁻¹, hmem⟩ (Subtype.ext (mul_inv_cancel₀ hk0'))
  have hmax : ∀ k : R, k ∈ IsLocalRing.maximalIdeal R → ψ k ∈ IsLocalRing.maximalIdeal P := by
    intro k hk
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hk ⊢
    exact fun h => hk (hrefl k h)
  set fP : P[X] := f.map ψ with hfP
  set fL : L[X] := f.map θ with hfL
  have hfLP : fL = fP.map P.subtype := by rw [hfP, Polynomial.map_map]
  have hfLmonic : fL.Monic := hf.map θ
  have hfL0 : fL ≠ 0 := hfLmonic.ne_zero
  have hsplit : fL.Splits := IsAlgClosed.splits fL
  have hInt : P.valuation.Integers P :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => P.valuation_le_one x
      exists_of_le_one := fun r hr => ⟨⟨r, (P.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  have hrootP : ∀ α ∈ fL.roots, α ∈ P := by
    intro α hα
    have hint : IsIntegral P α := by
      refine ⟨fP, hf.map ψ, ?_⟩
      have := (mem_roots hfL0).mp hα
      rwa [IsRoot.def, hfLP, eval_map] at this
    have := hInt.mem_of_integral hint
    rw [Valuation.mem_integer_iff] at this
    exact (P.valuation_le_one_iff α).mp this
  set S : Multiset L := fL.roots with hS
  obtain ⟨SP, hSPmap⟩ : ∃ SP : Multiset P, SP.map P.subtype = S :=
    ⟨S.attach.map fun x => (⟨x.1, hrootP x.1 x.2⟩ : P), by
      rw [Multiset.map_map]; exact Multiset.attach_map_val S⟩
  have hmemSP : ∀ (x : L) (hx : x ∈ P), x ∈ S → (⟨x, hx⟩ : P) ∈ SP := by
    intro x hx hxS
    rw [← hSPmap, Multiset.mem_map] at hxS
    obtain ⟨b, hb, hbx⟩ := hxS
    have : b = ⟨x, hx⟩ := Subtype.ext hbx
    rwa [this] at hb
  have hfPprod : fP = (SP.map fun b => X - C b).prod := by
    apply Polynomial.map_injective P.subtype Subtype.val_injective
    rw [← hfLP, Polynomial.map_multiset_prod, Multiset.map_map]
    have hcomp : ((fun x => Polynomial.map P.subtype x) ∘ fun b : P => X - C b) =
        (fun a : L => X - C a) ∘ P.subtype := by
      funext b; simp
    rw [hcomp, ← Multiset.map_map, hSPmap]
    exact hsplit.eq_prod_roots_of_monic hfLmonic
  let π : P →+* IsLocalRing.ResidueField P := IsLocalRing.residue P
  set fk := fP.map π with hfk
  have hfkprod : fk = ((SP.map π).map fun c => X - C c).prod := by
    rw [hfk, hfPprod, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp
  have hfkroots : fk.roots = SP.map π := by rw [hfkprod, roots_multiset_prod_X_sub_C]
  have hfk0 : fk ≠ 0 := ((hf.map ψ).map π).ne_zero
  set abar := π (ψ a₀) with habar
  have heval : fk.eval abar = 0 := by
    rw [hfk, eval_map, eval₂_hom, hfP, eval_map, eval₂_hom]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hmax _ ha₀)
  have hderiv : fk.derivative.eval abar ≠ 0 := by
    rw [hfk, derivative_map, eval_map, eval₂_hom, hfP, derivative_map, eval_map, eval₂_hom, Ne,
      IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hunit.map ψ
  have hmult : fk.rootMultiplicity abar = 1 := by
    have hpos : 0 < fk.rootMultiplicity abar := (rootMultiplicity_pos hfk0).mpr heval
    have hle : ¬ 1 < fk.rootMultiplicity abar := by
      rw [one_lt_rootMultiplicity_iff_isRoot hfk0, not_and_or]
      exact Or.inr hderiv
    omega
  have hcount : (SP.map π).count abar = 1 := by rw [← hfkroots, count_roots, hmult]
  rw [Multiset.count_map] at hcount
  obtain ⟨b₁, hb₁⟩ := Multiset.card_eq_one.mp hcount
  have hb₁mem : b₁ ∈ SP.filter (fun b => abar = π b) := by rw [hb₁]; exact Multiset.mem_singleton_self _
  rw [Multiset.mem_filter] at hb₁mem
  obtain ⟨hb₁S, hb₁red⟩ := hb₁mem
  have hb₁root : (b₁ : L) ∈ S := by rw [← hSPmap]; exact Multiset.mem_map_of_mem _ hb₁S
  have hb₁sub : b₁ - ψ a₀ ∈ IsLocalRing.maximalIdeal P := Ideal.Quotient.eq.mp hb₁red.symm
  have hfix : ∀ σ : L ≃ₐ[K] L, σ (b₁ : L) = b₁ := by
    intro σ
    have hmapfL : fL.map (σ : L →+* L) = fL := by
      rw [hfL, Polynomial.map_map]
      congr 1
      ext k
      simp [hθ]
    have hσroot : σ (b₁ : L) ∈ S := by
      have hSσ : S.map (σ : L →+* L) = S := by
        rw [hS, ← hsplit.roots_map_of_injective (σ : L →+* L).injective, hmapfL]
      rw [← hSσ]
      exact Multiset.mem_map_of_mem _ hb₁root
    have hσP : σ (b₁ : L) ∈ P := hstab σ _ b₁.2
    have hσred : π ⟨σ (b₁ : L), hσP⟩ = abar := by
      have h2 := (mem_maximalIdeal_iff_map P hstab σ ((b₁ - ψ a₀ : P) : L) (b₁ - ψ a₀).2).mp
        (by
          simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb₁sub
          exact hb₁sub)
      have h3 : (⟨σ (b₁ : L), hσP⟩ : P) - ψ a₀ ∈ IsLocalRing.maximalIdeal P := by
        convert h2 using 1
        apply Subtype.ext
        simp [hψ, map_sub]
      exact (Ideal.Quotient.eq.mpr h3)
    have hmemT : (⟨σ (b₁ : L), hσP⟩ : P) ∈ SP.filter (fun b => abar = π b) := by
      rw [Multiset.mem_filter]
      refine ⟨?_, hσred.symm⟩
      exact hmemSP _ hσP hσroot
    rw [hb₁, Multiset.mem_singleton] at hmemT
    exact congrArg Subtype.val hmemT
  have hbot : (b₁ : L) ∈ (⊥ : IntermediateField K L) := by
    rw [← InfiniteGalois.fixedField_bot, IntermediateField.mem_fixedField_iff]
    exact fun σ _ => hfix σ
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hbot
  have hkR : k ∈ R := by
    rw [hR, hk]; exact b₁.2
  have hψk : ψ ⟨k, hkR⟩ = b₁ := Subtype.ext hk
  refine ⟨⟨k, hkR⟩, ?_, ?_⟩
  · apply hθinj
    rw [map_zero, ← eval₂_hom, ← eval_map]
    change fL.eval (algebraMap K L k) = 0
    rw [hk]
    exact (mem_roots hfL0).mp hb₁root
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hm : ψ (⟨k, hkR⟩ - a₀) ∈ IsLocalRing.maximalIdeal P := by
      rw [map_sub, hψk]; exact hb₁sub
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm (hu.map ψ)

theorem henselianLocalRing_comap [IsAlgClosed L] [IsGalois K L] (P : ValuationSubring L)
    (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P) :
    HenselianLocalRing (P.comap (algebraMap K L)) where
  is_henselian f hf a₀ ha₀ hunit :=
    hensel_of_stable P hstab (P.comap (algebraMap K L)) (fun _ => Iff.rfl) f hf a₀ ha₀ hunit


/-- 実際の慣性固定体の上位体で Hensel 性を内部供給する。 -/
theorem overfield_henselian (A : ValuationSubring (AlgebraicClosure ℚ))
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : InertiaResidue.fixedField A ≤ E) :
    HenselianLocalRing (A.comap (algebraMap E (AlgebraicClosure ℚ))) :=
  henselianLocalRing_comap A (InertiaStability.overfield_stable A E hE)
end
end DkMath.Lib.NumberTheory.StableValuation

