/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailDepthThree

#print "file: DkMath.FLT.Seven.GTailCyclotomicTailDepthFour"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula DkMath.Lib.NumberTheory SevenCyclotomicDegreeSixInt

private theorem pow_inf_mul_of_comaximal {A : Type*} [CommRing A]
    (I J : Ideal A) (h : I ⊔ J = ⊤) (n : ℕ) (hn : n ≠ 0) :
    I ^ n ⊓ (I * J) = I ^ n * J := by
  have he : I ^ n ⊓ J = I ^ n * J :=
    (Ideal.mul_eq_inf_of_isCoprime
      (Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_eq_top h))).symm
  apply le_antisymm
  · rw [← he]
    exact inf_le_inf_left _ Ideal.mul_le_right
  · exact le_inf Ideal.mul_le_left (Ideal.mul_mono (Ideal.pow_le_self hn) le_rfl)

theorem sixRootKernel_fourth_inf_scalar {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) :
    sixRootKernel r hr0 hr7 hr1 j ^ 4 ⊓ cyclotomicScalarIdeal q =
      cyclotomicScalarIdeal q * sixRootKernel r hr0 hr7 hr1 j ^ 3 := by
  rw [← sixRootKernel_mul_complement r hr0 hr7 hr1 j,
    pow_inf_mul_of_comaximal _ _ (sixRootKernel_sup_complement r hr0 hr7 hr1 j) 4 (by decide)]
  simp only [pow_succ, pow_zero]
  ac_rfl

private theorem scalar_support_of_kernel_mem {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6)
    (n : ℕ) (hn : (n : Ring) ∈ sixRootKernel r hr0 hr7 hr1 j) :
    q ∣ n ∧ (n : Ring) ∈ cyclotomicScalarIdeal q := by
  have hz := (mem_sixRootKernel_iff _ _ _ _ _ _).mp hn
  simp only [map_natCast] at hz
  have hd := (ZMod.natCast_eq_zero_iff n q).mp hz
  refine ⟨hd, ?_⟩
  obtain ⟨m, hm⟩ := hd
  rw [cyclotomicScalarIdeal, Ideal.mem_span_singleton]
  exact ⟨(m : Ring), by rw [hm, Nat.cast_mul]⟩

/-- Scalar contraction of a supplied kernel fourth power uses actual coordinate cancellation. -/
theorem natCast_mem_sixRootKernel_fourth_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) (n : ℕ) :
    (n : Ring) ∈ sixRootKernel r hr0 hr7 hr1 j ^ 4 ↔ q ^ 4 ∣ n := by
  constructor
  · intro hn
    obtain ⟨hd, hs⟩ := scalar_support_of_kernel_mem r hr0 hr7 hr1 j n
      ((Ideal.pow_le_self (by decide : 4 ≠ 0)) hn)
    have hi : (n : Ring) ∈ sixRootKernel r hr0 hr7 hr1 j ^ 4 ⊓ cyclotomicScalarIdeal q :=
      ⟨hn, hs⟩
    rw [sixRootKernel_fourth_inf_scalar, cyclotomicScalarIdeal, Ideal.mem_span_singleton_mul] at hi
    obtain ⟨y, hy, hmul⟩ := hi
    obtain ⟨m, hm⟩ := hd
    have he : y = (m : Ring) := by
      apply cyclotomic_natCast_mul_injective q (Fact.out : Nat.Prime q).ne_zero
      rw [hm, Nat.cast_mul] at hmul
      exact hmul
    rw [he] at hy
    obtain ⟨k, hk⟩ := (natCast_mem_sixRootKernel_cube_iff r hr0 hr7 hr1 j m).mp hy
    refine ⟨k, ?_⟩
    rw [hm, hk]
    ring
  · rintro ⟨k, hk⟩
    have hq : (q : Ring) ∈ sixRootKernel r hr0 hr7 hr1 j := by
      rw [mem_sixRootKernel_iff]
      simp only [map_natCast, ZMod.natCast_self]
    rw [hk, Nat.cast_mul, Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hq 4)

/-- Selected actual factor fourth-power membership is precisely scalar fourth-power Tail support. -/
theorem gtailCyclotomicFactor_mem_fourth_iff {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 4 ↔
      q ^ 4 ∣ GTail 7 1 g c := by
  let K := sixRootKernel (gtailSevenTailRatio q c g)
    (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
    (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i)
  let : K.IsMaximal := sixRootKernel_isMaximal _ _ _ _ _
  have he : gtailCyclotomicFactor c g i ∈ K ^ 4 ↔
      gtailCyclotomicCofactor c g i * gtailCyclotomicFactor c g i ∈ K ^ 4 := by
    constructor
    · exact Ideal.mul_mem_left _ _
    · intro h
      exact (Ideal.IsMaximal.mul_mem_pow K h).resolve_left
        (gtailCyclotomicCofactor_not_mem_selected c g hc hg hT i)
  rw [he, gtailCyclotomicCofactor_mul_factor]
  exact natCast_mem_sixRootKernel_fourth_iff _ _ _ _ _ _

/-- Exact bounded third-power cutoff, without introducing a valuation function. -/
theorem gtailCyclotomicFactor_depth_three {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (hT3 : q ^ 3 ∣ GTail 7 1 g c) (hT4 : ¬ q ^ 4 ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 3 ∧
    gtailCyclotomicFactor c g i ∉
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 4 :=
  ⟨(gtailCyclotomicFactor_mem_cube_iff c g hc hg hT i).mpr hT3,
    fun hi => hT4 ((gtailCyclotomicFactor_mem_fourth_iff c g hc hg hT i).mp hi)⟩

end DkMath.FLT.Seven
