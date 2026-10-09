/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenRamifiedThreeIdeal

#print "file: DkMath.Lib.NumberTheory.GTailSevenIdealSquareAddress"

/-!
# Ideal-square support of the selected Eisenstein element

Ramified three yields scalar divisibility of a square; an oriented split
slot yields ideal-square membership without scalar divisibility. No exact
ideal-adic exponent, cyclotomic transfer or descent is asserted.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.TraceOneQuadratic

/-- The two norm-divisor addresses coincide at the repeated root modulo three. -/
theorem three_dvd_norm_iff_mem_ramifiedIdeal (z : TraceOneInt (-1)) :
    (3 : ℤ) ∣ norm z ↔ z ∈ eisensteinThreeRamifiedIdeal := by
  have h := prime_dvd_norm_iff_mem_eisensteinResidueIdeals
    (by decide : Nat.Prime 3) (2 : ZMod 3) eisensteinThreeRoot z
  rw [mem_eisensteinResidueIdeal_iff, mem_eisensteinResidueIdeal_iff] at h
  rw [show 1 - (2 : ZMod 3) = 2 by decide, or_self] at h
  rw [eisensteinThreeRamifiedIdeal, mem_eisensteinResidueIdeal_iff]
  exact h

/-- Ramified norm support lifts to embedded scalar divisibility of the actual element square. -/
theorem scalar_three_dvd_square_of_dvd_norm (z : TraceOneInt (-1))
    (hnorm : (3 : ℤ) ∣ norm z) : ofInt (-1) 3 ∣ z * z := by
  have hp := (three_dvd_norm_iff_mem_ramifiedIdeal z).mp hnorm
  have hs := Ideal.mul_mem_mul hp hp
  rw [eisensteinThreeRamifiedIdeal_mul_self] at hs
  change z * z ∈ Ideal.span ({ofInt (-1) 3} : Set (TraceOneInt (-1))) at hs
  exact Ideal.mem_span_singleton.mp hs

/-- Neutral adapter for the element square appearing in the selected GTail Body. -/
theorem scalar_three_dvd_gtailSevenNormCoord_sq {a b : ℕ}
    (hQ : 3 ∣ a ^ 2 + a * b + b ^ 2) :
    ofInt (-1) 3 ∣ (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 := by
  rw [pow_two]
  apply scalar_three_dvd_square_of_dvd_norm
  exact (dvd_quadratic_iff_dvd_gtailSevenNormCoord 3 a b).mp hQ

/-- Ideal-square membership uses the actual product of ideals, without prime assumptions. -/
theorem square_mem_eisensteinResidueIdeal_mul_self {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1))
    (hz : z ∈ eisensteinResidueIdeal t ht) :
    z * z ∈ eisensteinResidueIdeal t ht * eisensteinResidueIdeal t ht :=
  Ideal.mul_mem_mul hz hz

/-- Primality of the conjugate kernel excludes a square whenever its base is excluded. -/
theorem square_not_mem_conjugate_eisensteinResidueIdeal {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1))
    (hnot : z ∉ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)) :
    z * z ∉ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) := by
  let : (eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)).IsMaximal :=
    eisensteinResidueIdeal_isMaximal hq _ _
  have hp : (eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)).IsPrime :=
    inferInstance
  intro hs
  exact hnot ((hp.mem_or_mem hs).elim id id)

/-- Oriented split support keeps the square out of the conjugate and scalar ideals. -/
theorem split_eisenstein_square_address {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) (htdiff : t ≠ 1 - t)
    (z : TraceOneInt (-1)) (hz : z ∈ eisensteinResidueIdeal t ht)
    (hnot : z ∉ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)) :
    z * z ∈ eisensteinResidueIdeal t ht * eisensteinResidueIdeal t ht ∧
      z * z ∉ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) ∧
      z * z ∉ eisensteinScalarIdeal q := by
  have hn := square_not_mem_conjugate_eisensteinResidueIdeal hq t ht z hnot
  refine ⟨square_mem_eisensteinResidueIdeal_mul_self t ht z hz, hn, ?_⟩
  intro hs
  rw [← eisensteinResidueIdeals_inf_eq_scalar hq t ht htdiff] at hs
  exact hn hs.2

/-- Canonical natural-coordinate orientation supplies the selected element's square address. -/
theorem gtailSevenNormCoord_split_square_address {q a b : ℕ} [Fact (Nat.Prime q)]
    (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∈
        eisensteinResidueIdeal (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hb) *
          eisensteinResidueIdeal (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hb) ∧
      (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∉
        eisensteinResidueIdeal (1 - gtailSevenResidueRoot q a b)
          (gtailSevenResidueRoot_conjugate_polynomial hQ hb) ∧
      (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∉ eisensteinScalarIdeal q := by
  simpa only [pow_two] using split_eisenstein_square_address
    (Fact.out : Nat.Prime q) (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hb)
    (gtailSevenResidueRoot_ne_conjugate hq3 hQ hb) (gtailSevenNormCoord a b)
    (gtailSevenNormCoord_mem_residueIdeal hQ hb)
    (gtailSevenNormCoord_not_mem_conjugate_residueIdeal hq3 hQ hb)

end DkMath.Lib.NumberTheory
