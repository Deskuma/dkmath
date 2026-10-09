/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenSplitIdeal

#print "file: DkMathTest.NumberTheory.GTailSevenSplitIdeal"

namespace DkMathTest.NumberTheory.GTailSevenSplitIdeal

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory

private theorem root37 : (37 : ZMod 43) ^ 2 - 37 + 1 = 0 := by decide
private theorem root7 : (7 : ZMod 43) ^ 2 - 7 + 1 = 0 := by decide
private theorem root2 : (2 : ZMod 3) ^ 2 - 2 + 1 = 0 := by decide

local notation "P37" => eisensteinResidueIdeal (37 : ZMod 43) root37
local notation "P7" => eisensteinResidueIdeal (7 : ZMod 43) root7
local notation "I43" => eisensteinScalarIdeal 43

private theorem conjugate37_eq7 :
    eisensteinResidueIdeal (1 - (37 : ZMod 43)) (eisensteinResidue_conjugate_root _ root37) = P7 := by
  ext z
  simp only [mem_eisensteinResidueIdeal_iff]
  rw [show 1 - (37 : ZMod 43) = 7 by decide]

example : P37 ⊓ P7 = I43 := by
  have h := eisensteinResidueIdeals_inf_eq_scalar (by decide : Nat.Prime 43)
    (37 : ZMod 43) root37 (by decide)
  rw [conjugate37_eq7] at h
  exact h

example : P37 * P7 = I43 := by
  have h := eisensteinResidueIdeals_mul_eq_scalar (by decide : Nat.Prime 43)
    (37 : ZMod 43) root37 (by decide)
  rw [conjugate37_eq7] at h
  exact h

example : P37 ⊔ P7 = ⊤ := by
  have h := eisensteinResidueIdeals_sup_eq_top (by decide : Nat.Prime 43)
    (37 : ZMod 43) root37 (by decide)
  rw [conjugate37_eq7] at h
  exact h

example : (37 : ZMod 43) ≠ 1 - 37 :=
  eisensteinResidue_root_ne_conjugate (by decide) (by decide) _ root37

example : norm (gtailSevenNormCoord 5 8) = 129 ∧ (129 : ℕ) = 3 * 43 := by
  rw [norm_gtailSevenNormCoord]
  norm_num

example : gtailSevenNormCoord 5 8 ∈ P37 ∧ gtailSevenNormCoord 5 8 ∉ P7 := by
  simp only [mem_eisensteinResidueIdeal_iff]
  decide

example : gtailSevenNormCoord 5 8 ∉ I43 := by
  rw [mem_eisensteinScalarIdeal_iff, gtailSevenNormCoord_eq]
  decide

example : ofInt (-1) ((43 : ℕ) : ℤ) ∈ P37 ∧
    ofInt (-1) ((43 : ℕ) : ℤ) ∈ P7 ∧
    ofInt (-1) ((43 : ℕ) : ℤ) ∈ I43 ∧
    ¬ ofInt (-1) ((43 : ℕ) : ℤ) ∣ gtailSevenNormCoord 5 8 := by
  refine ⟨scalar_mem_eisensteinResidueIdeal _ _, scalar_mem_eisensteinResidueIdeal _ _, ?_, ?_⟩
  · rw [mem_eisensteinScalarIdeal_iff]
    norm_num [ofInt]
  · rw [scalar_dvd_gtailSevenNormCoord_iff]
    decide

-- The generic reconstruction lemma, rather than finite evaluation, supplies both memberships.
example : (⟨-43, 86⟩ : TraceOneInt (-1)) ∈ P37 ∧
    (⟨-43, 86⟩ : TraceOneInt (-1)) ∈ P7 := by
  have h := (mem_eisensteinResidueIdeals_iff_coordinates (by decide : Nat.Prime 43)
    (37 : ZMod 43) root37 (by decide) (⟨-43, 86⟩ : TraceOneInt (-1))).mpr
    (by norm_num)
  rw [conjugate37_eq7] at h
  exact h

example : (⟨-43, 86⟩ : TraceOneInt (-1)) ∈ I43 := by
  rw [mem_eisensteinScalarIdeal_iff]
  norm_num

example : ofInt (-1) 43 ∣ (⟨-43, 86⟩ : TraceOneInt (-1)) := by
  rw [scalar_dvd_traceOne_neg_one_iff]
  norm_num

-- The scalar criterion also handles zero and negative scalar inputs.
example : ofInt (-1) (-43) ∣ (⟨-43, 86⟩ : TraceOneInt (-1)) := by
  rw [scalar_dvd_traceOne_neg_one_iff]
  norm_num

example : ofInt (-1) 0 ∣ (⟨0, 0⟩ : TraceOneInt (-1)) := by
  rw [scalar_dvd_traceOne_neg_one_iff]
  norm_num

-- Characteristic three: coincident kernels and a genuine failed intersection formula.
example : (2 : ZMod 3) = 1 - 2 := by decide

example : eisensteinResidueIdeal (2 : ZMod 3) root2 =
    eisensteinResidueIdeal (1 - (2 : ZMod 3)) (eisensteinResidue_conjugate_root _ root2) := by
  ext z
  simp only [mem_eisensteinResidueIdeal_iff]
  rw [show 1 - (2 : ZMod 3) = 2 by decide]

example : (⟨1, 1⟩ : TraceOneInt (-1)) ∈ eisensteinResidueIdeal (2 : ZMod 3) root2 ∧
    norm (⟨1, 1⟩ : TraceOneInt (-1)) = 3 ∧
    ¬ ofInt (-1) 3 ∣ (⟨1, 1⟩ : TraceOneInt (-1)) := by
  rw [mem_eisensteinResidueIdeal_iff, scalar_dvd_traceOne_neg_one_iff]
  decide

example : eisensteinResidueIdeal (2 : ZMod 3) root2 ⊓
    eisensteinResidueIdeal (1 - (2 : ZMod 3)) (eisensteinResidue_conjugate_root _ root2) ≠
      eisensteinScalarIdeal 3 := by
  intro heq
  have hm : (⟨1, 1⟩ : TraceOneInt (-1)) ∈ eisensteinResidueIdeal (2 : ZMod 3) root2 ⊓
      eisensteinResidueIdeal (1 - (2 : ZMod 3)) (eisensteinResidue_conjugate_root _ root2) := by
    simp only [Ideal.mem_inf, mem_eisensteinResidueIdeal_iff]
    decide
  have hn : (⟨1, 1⟩ : TraceOneInt (-1)) ∉ eisensteinScalarIdeal 3 := by
    rw [mem_eisensteinScalarIdeal_iff]
    decide
  exact hn (heq ▸ hm)

-- A small inert boundary; no root is fabricated at q=5.
example : ¬ ∃ t : ZMod 5, t ^ 2 - t + 1 = 0 := by decide

example {q : ℕ} (hq : Nat.Prime q) (hq3 : q ≠ 3) (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) :
    eisensteinResidueIdeal t ht *
      eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) =
        eisensteinScalarIdeal q :=
  eisensteinResidueIdeals_mul_eq_scalar_of_ne_three hq hq3 t ht

#print axioms DkMath.Lib.NumberTheory.eisensteinResidue_root_ne_conjugate
#print axioms DkMath.Lib.NumberTheory.scalar_dvd_traceOne_neg_one_iff
#print axioms DkMath.Lib.NumberTheory.eisensteinScalarIdeal
#print axioms DkMath.Lib.NumberTheory.mem_eisensteinScalarIdeal_iff
#print axioms DkMath.Lib.NumberTheory.mem_eisensteinResidueIdeals_iff_coordinates
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueIdeals_inf_eq_scalar
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueIdeals_ne_of_root_ne_conjugate
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueIdeals_sup_eq_top
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueIdeals_mul_eq_scalar
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueIdeals_mul_eq_scalar_of_ne_three

end DkMathTest.NumberTheory.GTailSevenSplitIdeal
