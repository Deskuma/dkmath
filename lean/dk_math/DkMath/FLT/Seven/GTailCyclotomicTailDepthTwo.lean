/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailDepthOne

#print "file: DkMath.FLT.Seven.GTailCyclotomicTailDepthTwo"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula DkMath.Lib.NumberTheory SevenCyclotomicDegreeSixInt

/-- Saturation at power two uses maximality, not merely primality or domain cancellation. -/
theorem mem_maximal_square_of_mul_mem {A : Type*} [CommRing A] (J : Ideal A)
    (hJ : J.IsMaximal) (U x : A) (hU : U ∉ J) (hProd : U * x ∈ J ^ 2) :
    x ∈ J ^ 2 := by
  let : J.IsMaximal := hJ
  exact (Ideal.IsMaximal.mul_mem_pow J hProd).resolve_left hU


/-- The actual product of the other five factors, with the selected factor erased. -/
def gtailCyclotomicCofactor (c g : ℕ) (i : Fin 6) : SevenCyclotomicDegreeSixInt.Ring :=
  ∏ h ∈ Finset.univ.erase i, gtailCyclotomicFactor c g h

/-- Reinsert the selected factor to recover the original natural Tail as a source element. -/
theorem gtailCyclotomicCofactor_mul_factor (c g : ℕ) (i : Fin 6) :
    gtailCyclotomicCofactor c g i * gtailCyclotomicFactor c g i =
      ((GTail 7 1 g c : ℕ) : SevenCyclotomicDegreeSixInt.Ring) := by
  rw [gtailCyclotomicCofactor, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact prod_six_gtailCyclotomicFactor_eq_GTail c g

/-- All five other factors, hence their cofactor, are outside the selected prime kernel. -/
theorem gtailCyclotomicCofactor_not_mem_selected {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    gtailCyclotomicCofactor c g i ∉
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) := by
  let J := sixRootKernel (gtailSevenTailRatio q c g)
    (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
    (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i)
  let : J.IsPrime := sixRootKernel_isPrime _ _ _ _ _
  intro hmem
  change (∏ h ∈ Finset.univ.erase i, gtailCyclotomicFactor c g h) ∈ J at hmem
  obtain ⟨h, hh, hf⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
  have he : sixInverseSlot i = sixInverseSlot h :=
    (gtailCyclotomicFactor_unique_slot c g hc hg hT h _).mp hf
  have hi : i = h := sixInverseSlot_involutive.injective he
  exact (Finset.mem_erase.mp hh).1 hi.symm


/-- A scalar square multiple belongs to the square of every supplied root kernel. -/
theorem natCast_mem_sixRootKernel_square_of_sq_dvd {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (j : Fin 6) (n : ℕ) (hn : q ^ 2 ∣ n) :
    (n : SevenCyclotomicDegreeSixInt.Ring) ∈ sixRootKernel r hr0 hr7 hr1 j ^ 2 := by
  have hq : (q : SevenCyclotomicDegreeSixInt.Ring) ∈ sixRootKernel r hr0 hr7 hr1 j := by
    rw [mem_sixRootKernel_iff]
    simp only [map_natCast]
    exact (ZMod.natCast_eq_zero_iff q q).mpr (dvd_refl q)
  have hq2 := Ideal.pow_mem_pow hq 2
  obtain ⟨k, hk⟩ := hn
  rw [hk, Nat.cast_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ hq2

/-- Square divisibility of the scalar Tail gives genuine selected factor square membership. -/
theorem gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (hT2 : q ^ 2 ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2 := by
  apply mem_maximal_square_of_mul_mem _ (sixRootKernel_isMaximal _ _ _ _ _)
    (gtailCyclotomicCofactor c g i) _ (gtailCyclotomicCofactor_not_mem_selected c g hc hg hT i)
  rw [gtailCyclotomicCofactor_mul_factor]
  exact natCast_mem_sixRootKernel_square_of_sq_dvd _ _ _ _ _ _ hT2

/-- Exact second-level membership, retaining the canonical Tail unit and support premises. -/
theorem gtailCyclotomicFactor_mem_square_iff {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2 ↔
      q ^ 2 ∣ GTail 7 1 g c := by
  constructor
  · intro hi
    exact (natCast_mem_scalar_mul_sixRootKernel_iff _ _ _ _ _ _).mp
      (GTail_mem_scalar_mul_kernel_of_factor_mem_square c g hc hg hT i hi)
  · intro hT2
    exact gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail c g hc hg hT hT2 i

end DkMath.FLT.Seven
