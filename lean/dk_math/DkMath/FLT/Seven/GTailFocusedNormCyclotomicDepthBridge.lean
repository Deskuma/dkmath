/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailDepthFour
import DkMath.FLT.Seven.GTailPrimeAllocationAudit
import DkMath.FLT.Seven.GTailNormReadoutAudit
import DkMath.Lib.NumberTheory.GTailSevenIdealSquareAddress

#print "file: DkMath.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula DkMath.Lib.NumberTheory DkMath.NumberTheory.TraceOneQuadratic

/-- A gap unit removes its contribution from an explicitly supplied scalar budget. -/
theorem scalar_budget_tail_double (q g T Q : ℕ) (hgu : ¬ q ∣ g)
    (hbudget : padicValNat q g + padicValNat q T = 2 * padicValNat q Q) :
    padicValNat q T = 2 * padicValNat q Q := by
  simpa only [padicValNat.eq_zero_of_not_dvd hgu, zero_add] using hbudget

/-- Bounded readouts of the doubled scalar budget, with nonzero values explicit. -/
theorem scalar_budget_depth_readouts (q g T Q : ℕ) (hq : Nat.Prime q)
    (hT0 : T ≠ 0) (hQ0 : Q ≠ 0) (hgu : ¬ q ∣ g)
    (hbudget : padicValNat q g + padicValNat q T = 2 * padicValNat q Q) :
    (q ^ 2 ∣ T ↔ q ∣ Q) ∧ (q ^ 4 ∣ T ↔ q ^ 2 ∣ Q) ∧
      (q ^ 3 ∣ T ↔ q ^ 4 ∣ T) ∧ ¬ (q ^ 3 ∣ T ∧ ¬ q ^ 4 ∣ T) := by
  have he := scalar_budget_tail_double q g T Q hgu hbudget
  have h2 : q ^ 2 ∣ T ↔ q ∣ Q := by
    rw [← padicValNat_le_iff_dvd hq hT0 2, ← Vp_ge_one_iff hq hQ0, he]
    omega
  have h4 : q ^ 4 ∣ T ↔ q ^ 2 ∣ Q := by
    rw [← padicValNat_le_iff_dvd hq hT0 4, ← padicValNat_le_iff_dvd hq hQ0 2, he]
    omega
  have h34 : q ^ 3 ∣ T ↔ q ^ 4 ∣ T := by
    rw [← padicValNat_le_iff_dvd hq hT0 3, ← padicValNat_le_iff_dvd hq hT0 4, he]
    omega
  exact ⟨h2, h4, h34, fun h => h.2 (h34.mp h.1)⟩

/-- All coordinate, endpoint and gap units are consequences of the exact focused contract. -/
theorem focused_norm_depth_guards {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    (¬ q ∣ a) ∧ (¬ q ∣ b) ∧ (¬ q ∣ a + b) ∧ (¬ q ∣ c) ∧ (¬ q ∣ g) ∧ q ≠ 3 := by
  have hu := not_prime_dvd_coordinate_product_of_quadratic (Fact.out : Nat.Prime q) hcop hQ
  have ha : ¬ q ∣ a := fun hd => hu (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _)
  have hb : ¬ q ∣ b := fun hd => hu (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
  have hab : ¬ q ∣ a + b := fun hd => hu (dvd_mul_of_dvd_right hd _)
  have hc := not_prime_dvd_endpoint_of_quadratic (Fact.out : Nat.Prime q) hcop hEq hQ
  have hg : ¬ q ∣ g := by
    rcases prime_focused_support_exclusive (Fact.out : Nat.Prime q) hq7 hcop hEq hsum hQ with h | h
    · exact (h.2 hT).elim
    · exact h.2
  exact ⟨ha, hb, hab, hc, hg, prime_ne_three_of_gtail (Fact.out : Nat.Prime q) hq7 hc hg hT⟩

private theorem focused_positive_nonzero {a b c g : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) :
    g ≠ 0 ∧ GTail 7 1 g c ≠ 0 ∧ a ^ 2 + a * b + b ^ 2 ≠ 0 := by
  have hpos : 0 < g * GTail 7 1 g c := by
    rw [gtail_seven_eq_of_fermat7Equation hEq hsum]
    positivity
  refine ⟨?_, ?_, by positivity⟩
  · intro hz
    simp only [hz, zero_mul, lt_self_iff_false] at hpos
  · intro hz
    simp only [hz, mul_zero, lt_self_iff_false] at hpos

/-- Conditional scalar synchronization, reusing the preexisting focused valuation budget. -/
theorem focused_norm_scalar_depth_readouts {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    padicValNat q (GTail 7 1 g c) = 2 * padicValNat q (a ^ 2 + a * b + b ^ 2) ∧
    q ^ 2 ∣ GTail 7 1 g c ∧
    (q ^ 4 ∣ GTail 7 1 g c ↔ q ^ 2 ∣ a ^ 2 + a * b + b ^ 2) ∧
    (q ^ 3 ∣ GTail 7 1 g c ↔ q ^ 4 ∣ GTail 7 1 g c) := by
  have hu := focused_norm_depth_guards hcop hEq hsum hq7 hQ hT
  have hn := focused_positive_nonzero ha hb hEq hsum
  have hbgt := padicValNat_focused_quadratic_budget ha hb hcop hEq hsum
    (Fact.out : Nat.Prime q) hq7 hQ
  have hr := scalar_budget_depth_readouts q g (GTail 7 1 g c) (a ^ 2 + a * b + b ^ 2)
    (Fact.out : Nat.Prime q) hn.2.1 hn.2.2 hu.2.2.2.2.1 hbgt
  have hT2 : q ^ 2 ∣ GTail 7 1 g c := by
    rcases prime_square_focused_allocation ha hb hcop hEq hsum (Fact.out : Nat.Prime q) hq7 hQ with h | h
    · exact (h.2 hT).elim
    · exact h.1
  exact ⟨scalar_budget_tail_double _ _ _ _ hu.2.2.2.2.1 hbgt, hT2, hr.2.1, hr.2.2.1⟩

/-- The Eisenstein endpoint remains in the quadratic integral ring. -/
theorem focused_eisenstein_norm_square_endpoint {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    let hu := focused_norm_depth_guards hcop hEq hsum hq7 hQ hT
    norm (gtailSevenNormCoord a b) = ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ) ∧
    ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∈
      eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_polynomial hQ hu.2.1) *
      eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_polynomial hQ hu.2.1) ∧
    (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∉
      eisensteinResidueIdeal (1 - gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_conjugate_polynomial hQ hu.2.1) ∧
    (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∉ eisensteinScalarIdeal q) ∧
    (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) := by
  have hu := focused_norm_depth_guards hcop hEq hsum hq7 hQ hT
  have _ := focused_positive_nonzero ha hb hEq hsum
  exact ⟨norm_gtailSevenNormCoord a b,
    gtailSevenNormCoord_split_square_address hu.2.2.2.2.2 hQ hu.2.1,
    focused_gtail_eq_norm_square hEq hsum⟩

/-- The cyclotomic endpoint shares scalar hypotheses, not an integral ring map. -/
theorem focused_cyclotomic_depth_endpoint {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) (i : Fin 6) :
    let hu := focused_norm_depth_guards hcop hEq hsum hq7 hQ hT
    let K := sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hu.2.2.2.1 hT)
      (gtailSevenTailRatio_pow_seven hu.2.2.2.1 hT)
      (gtailSevenTailRatio_ne_one hu.2.2.2.1 hu.2.2.2.2.1) (sixInverseSlot i)
    gtailCyclotomicFactor c g i ∈ K ^ 2 ∧
      (gtailCyclotomicFactor c g i ∈ K ^ 3 ↔ gtailCyclotomicFactor c g i ∈ K ^ 4) ∧
      ¬ (gtailCyclotomicFactor c g i ∈ K ^ 3 ∧ gtailCyclotomicFactor c g i ∉ K ^ 4) := by
  have hu := focused_norm_depth_guards hcop hEq hsum hq7 hQ hT
  have hr := focused_norm_scalar_depth_readouts ha hb hcop hEq hsum hq7 hQ hT
  have h2 := (gtailCyclotomicFactor_mem_square_iff c g hu.2.2.2.1 hu.2.2.2.2.1 hT i).mpr hr.2.1
  have he := (gtailCyclotomicFactor_mem_cube_iff c g hu.2.2.2.1 hu.2.2.2.2.1 hT i).trans
    (hr.2.2.2.trans (gtailCyclotomicFactor_mem_fourth_iff c g hu.2.2.2.1 hu.2.2.2.2.1 hT i).symm)
  exact ⟨h2, he, fun h => h.2 (he.mp h.1)⟩

/-- Cross-carrier synchronization is an integer norm-value divisibility statement. -/
theorem focused_tail_fourth_iff_norm_square_dvd {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    q ^ 4 ∣ GTail 7 1 g c ↔ (q : ℤ) ^ 2 ∣ norm (gtailSevenNormCoord a b) := by
  rw [norm_gtailSevenNormCoord]
  have h := (focused_norm_scalar_depth_readouts ha hb hcop hEq hsum hq7 hQ hT).2.2.1
  exact h.trans (by norm_cast)

end DkMath.FLT.Seven
