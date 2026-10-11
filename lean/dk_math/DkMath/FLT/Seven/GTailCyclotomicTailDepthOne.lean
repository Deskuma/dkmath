/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailFactorProduct

#print "file: DkMath.FLT.Seven.GTailCyclotomicTailDepthOne"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula DkMath.Lib.NumberTheory SevenCyclotomicDegreeSixInt

/-- Nonzero integral scalar multiplication is injective in the actual six-coordinate carrier. -/
theorem cyclotomic_natCast_mul_injective (q : ℕ) (hq : q ≠ 0) :
    Function.Injective (fun z : SevenCyclotomicDegreeSixInt.Ring => (q : _) * z) := by
  intro x y h
  apply coordinates.injective
  funext j
  apply (mul_right_inj' (show (q : ℤ) ≠ 0 by exact_mod_cast hq)).mp
  simpa only [← coordinates_natCast_mul] using congrArg (fun z => coordinates z j) h

/-- Only scalar elements are contracted: this does not identify the product ideal with (q²). -/
theorem natCast_mem_scalar_mul_sixRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (j : Fin 6) (n : ℕ) :
    (n : SevenCyclotomicDegreeSixInt.Ring) ∈
      cyclotomicScalarIdeal q * sixRootKernel r hr0 hr7 hr1 j ↔ q ^ 2 ∣ n := by
  rw [cyclotomicScalarIdeal, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨y, hy, hmul⟩
    have hcoord := congrArg (fun z => coordinates z 0) hmul
    rw [coordinates_natCast_mul] at hcoord
    have hd : (q : ℤ) ∣ (n : ℤ) := ⟨coordinates y 0, by
      simpa [coordinates] using hcoord.symm⟩
    have hdn : q ∣ n := by exact_mod_cast hd
    obtain ⟨m, hm⟩ := hdn
    have hycast : y = (m : SevenCyclotomicDegreeSixInt.Ring) := by
      apply cyclotomic_natCast_mul_injective q (Fact.out : Nat.Prime q).ne_zero
      rw [hm, Nat.cast_mul] at hmul
      exact hmul
    rw [hycast, mem_sixRootKernel_iff] at hy
    simp only [map_natCast] at hy
    obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff m q).mp hy
    refine ⟨k, ?_⟩
    rw [hm, hk, pow_two, mul_assoc]
  · rintro ⟨k, hk⟩
    refine ⟨((q * k : ℕ) : SevenCyclotomicDegreeSixInt.Ring), ?_, ?_⟩
    · rw [mem_sixRootKernel_iff]
      simp only [map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr ⟨k, rfl⟩
    · rw [hk, pow_two]
      push_cast
      ring

/-- A selected squared membership contributes one extra ideal copy to the finite product. -/
theorem prod_mem_prod_mul_of_mem_square {A ι : Type*} [CommRing A] [Fintype ι]
    (J : ι → Ideal A) (x : ι → A) (hx : ∀ j, x j ∈ J j) (i : ι)
    (hi : x i ∈ J i ^ 2) : (∏ j, x j) ∈ (∏ j, J j) * J i := by
  classical
  rw [← Finset.prod_erase_mul Finset.univ x (Finset.mem_univ i)]
  rw [← Finset.prod_erase_mul Finset.univ J (Finset.mem_univ i), mul_assoc]
  exact Ideal.mul_mem_mul
    (Ideal.prod_mem_prod (fun j _ => hx j)) (by simpa only [pow_two] using hi)

/-- The oriented kernel family is precisely the same six slots after reindexing. -/
theorem prod_inverseSlot_sixRootKernel_eq_scalarIdeal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (∏ i : Fin 6, sixRootKernel r hr0 hr7 hr1 (sixInverseSlot i)) =
      cyclotomicScalarIdeal q := by
  let e : Fin 6 ≃ Fin 6 :=
    ⟨sixInverseSlot, sixInverseSlot, sixInverseSlot_involutive, sixInverseSlot_involutive⟩
  have h := e.prod_comp (sixRootKernel r hr0 hr7 hr1)
  exact h.trans (prod_sixRootKernel_eq_scalarIdeal r hr0 hr7 hr1)


/-- An excess selected kernel copy in a factor forces scalar Tail into (q) times that kernel. -/
theorem GTail_mem_scalar_mul_kernel_of_factor_mem_square {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6)
    (hi : gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2) :
    ((GTail 7 1 g c : ℕ) : SevenCyclotomicDegreeSixInt.Ring) ∈
      cyclotomicScalarIdeal q * sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) := by
  have h := prod_mem_prod_mul_of_mem_square
    (fun j => sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot j))
    (gtailCyclotomicFactor c g)
    (fun j => (gtailCyclotomicFactor_unique_slot c g hc hg hT j _).mpr rfl) i hi
  rw [prod_six_gtailCyclotomicFactor_eq_GTail,
    prod_inverseSlot_sixRootKernel_eq_scalarIdeal] at h
  exact h

/-- Scalar squarefree-at-q input excludes the square of the factor's selected kernel. -/
theorem gtailCyclotomicFactor_not_mem_square {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (hT2 : ¬ q ^ 2 ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∉
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2 := by
  intro hi
  exact hT2 ((natCast_mem_scalar_mul_sixRootKernel_iff _ _ _ _ _ _).mp
    (GTail_mem_scalar_mul_kernel_of_factor_mem_square c g hc hg hT i hi))

/-- First-power membership paired with the guarded second-power exclusion. -/
theorem gtailCyclotomicFactor_depth_one {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (hT2 : ¬ q ^ 2 ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ∧
    gtailCyclotomicFactor c g i ∉
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2 :=
  ⟨(gtailCyclotomicFactor_unique_slot c g hc hg hT i _).mpr rfl,
    gtailCyclotomicFactor_not_mem_square c g hc hg hT hT2 i⟩

end DkMath.FLT.Seven
