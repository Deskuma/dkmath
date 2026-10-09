/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenIdealSquareAddress

#print "file: DkMathTest.NumberTheory.GTailSevenIdealSquareAddress"

namespace DkMathTest.NumberTheory.GTailSevenIdealSquareAddress

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory

local notation "π" => eisensteinThreeGenerator
local notation "P3" => eisensteinThreeRamifiedIdeal
local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

private theorem root37 : (37 : ZMod 43) ^ 2 - 37 + 1 = 0 := by decide
private theorem root7 : (7 : ZMod 43) ^ 2 - 7 + 1 = 0 := by decide
local notation "P37" => eisensteinResidueIdeal (37 : ZMod 43) root37
local notation "P7" => eisensteinResidueIdeal (7 : ZMod 43) root7
local notation "α" => gtailSevenNormCoord 5 8

private theorem conjugate37_eq7 :
    eisensteinResidueIdeal (1 - (37 : ZMod 43)) (eisensteinResidue_conjugate_root _ root37) = P7 := by
  ext z
  simp only [mem_eisensteinResidueIdeal_iff]
  rw [show 1 - (37 : ZMod 43) = 7 by decide]

-- Ramified support strengthens scalar divisibility only after squaring.
example : norm π = 3 := norm_eisensteinThreeGenerator
example : ¬ ofInt (-1) 3 ∣ π := by
  rw [scalar_dvd_traceOne_neg_one_iff, eisensteinThreeGenerator_eq]
  decide

example : ofInt (-1) 3 ∣ π * π := by
  apply scalar_three_dvd_square_of_dvd_norm
  rw [norm_eisensteinThreeGenerator]

example : π ∈ P3 ∧ π ∉ eisensteinScalarIdeal 3 := by
  refine ⟨eisensteinThreeGenerator_mem_ramifiedIdeal, ?_⟩
  rw [mem_eisensteinScalarIdeal_iff, eisensteinThreeGenerator_eq]
  decide

example : π * π ∈ P3 * P3 ∧ P3 * P3 = eisensteinScalarIdeal 3 :=
  ⟨Ideal.mul_mem_mul eisensteinThreeGenerator_mem_ramifiedIdeal
    eisensteinThreeGenerator_mem_ramifiedIdeal, eisensteinThreeRamifiedIdeal_mul_self⟩

example : norm (⟨-2, 1⟩ : TraceOneInt (-1)) = 3 := by decide
example : ofInt (-1) 3 ∣ (⟨-2, 1⟩ : TraceOneInt (-1)) * ⟨-2, 1⟩ := by
  apply scalar_three_dvd_square_of_dvd_norm
  decide

example : (⟨-2, 1⟩ : TraceOneInt (-1)) * ⟨-2, 1⟩ = ⟨3, -3⟩ := by decide
example : ofInt (-1) 3 ∣ (gtailSevenNormCoord 1 1 : TraceOneInt (-1)) ^ 2 :=
  scalar_three_dvd_gtailSevenNormCoord_sq (by decide)

-- Actual split calibration, without any Fermat premise.
example : norm α = 129 ∧ (129 : ℕ) = 3 * 43 := by
  rw [norm_gtailSevenNormCoord]
  norm_num

example : (α : TraceOneInt (-1)) ^ 2 = ⟨-39, 144⟩ := by decide
example : norm ((α : TraceOneInt (-1)) ^ 2) = (129 : ℤ) ^ 2 := by
  rw [norm_gtailSevenNormCoord_sq]
  norm_num

example : α ∈ P37 ∧ α ∉ P7 := by
  simp only [mem_eisensteinResidueIdeal_iff]
  decide

private theorem split43_address :
    α * α ∈ P37 * P37 ∧ α * α ∉ P7 ∧ α * α ∉ eisensteinScalarIdeal 43 := by
  have h := split_eisenstein_square_address (by decide : Nat.Prime 43)
    (37 : ZMod 43) root37 (by decide) α
    (by rw [mem_eisensteinResidueIdeal_iff]; decide)
    (by rw [mem_eisensteinResidueIdeal_iff]; decide)
  rw [conjugate37_eq7] at h
  exact h

example : α * α ∈ P37 * P37 ∧ α * α ∉ P7 ∧ α * α ∉ eisensteinScalarIdeal 43 := split43_address

example : ¬ ofInt (-1) 43 ∣ (α : TraceOneInt (-1)) ^ 2 := by
  rw [scalar_dvd_traceOne_neg_one_iff]
  decide

example : ¬ (43 : ℤ) ∣ (-39 : ℤ) ∧ ¬ (43 : ℤ) ∣ (144 : ℤ) := by decide

-- The norm has q and q² support, but the scalar ring element does not divide the square.
example : (43 : ℤ) ∣ norm α ∧ (43 : ℤ) ^ 2 ∣ norm ((α : TraceOneInt (-1)) ^ 2) ∧
    ¬ ofInt (-1) 43 ∣ (α : TraceOneInt (-1)) ^ 2 := by
  constructor
  · exact (dvd_quadratic_iff_dvd_gtailSevenNormCoord 43 5 8).mp (by decide)
  · constructor
    · rw [norm_gtailSevenNormCoord_sq]
      norm_num
    · rw [scalar_dvd_traceOne_neg_one_iff]
      decide

example : ofInt (-1) 3 ∣ (α : TraceOneInt (-1)) ^ 2 :=
  scalar_three_dvd_gtailSevenNormCoord_sq (by decide)

example : (α : TraceOneInt (-1)) ^ 2 ∈
      eisensteinResidueIdeal (gtailSevenResidueRoot 43 5 8)
        (gtailSevenResidueRoot_polynomial (by decide) (by decide)) *
      eisensteinResidueIdeal (gtailSevenResidueRoot 43 5 8)
        (gtailSevenResidueRoot_polynomial (by decide) (by decide)) ∧
    (α : TraceOneInt (-1)) ^ 2 ∉
      eisensteinResidueIdeal (1 - gtailSevenResidueRoot 43 5 8)
        (gtailSevenResidueRoot_conjugate_polynomial (by decide) (by decide)) ∧
    (α : TraceOneInt (-1)) ^ 2 ∉ eisensteinScalarIdeal 43 :=
  gtailSevenNormCoord_split_square_address (by decide) (by decide) (by decide)

-- Repeated-root and inert boundaries stay explicit.
example : (2 : ZMod 3) = 1 - 2 := by decide
example : ¬ ∃ t : ZMod 5, t ^ 2 - t + 1 = 0 := by decide

example (z : TraceOneInt (-1)) (hn : (3 : ℤ) ∣ norm z) : ofInt (-1) 3 ∣ z * z :=
  scalar_three_dvd_square_of_dvd_norm z hn

#print axioms DkMath.Lib.NumberTheory.three_dvd_norm_iff_mem_ramifiedIdeal
#print axioms DkMath.Lib.NumberTheory.scalar_three_dvd_square_of_dvd_norm
#print axioms DkMath.Lib.NumberTheory.scalar_three_dvd_gtailSevenNormCoord_sq
#print axioms DkMath.Lib.NumberTheory.square_mem_eisensteinResidueIdeal_mul_self
#print axioms DkMath.Lib.NumberTheory.square_not_mem_conjugate_eisensteinResidueIdeal
#print axioms DkMath.Lib.NumberTheory.split_eisenstein_square_address
#print axioms DkMath.Lib.NumberTheory.gtailSevenNormCoord_split_square_address

end DkMathTest.NumberTheory.GTailSevenIdealSquareAddress
