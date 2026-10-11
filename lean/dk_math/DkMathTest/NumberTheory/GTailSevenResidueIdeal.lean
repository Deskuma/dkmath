/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenResidueIdeal

#print "file: DkMathTest.NumberTheory.GTailSevenResidueIdeal"

namespace DkMathTest.NumberTheory.GTailSevenResidueIdeal

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem root37 : (37 : ZMod 43) ^ 2 - 37 + 1 = 0 := by decide
private theorem root7 : (7 : ZMod 43) ^ 2 - 7 + 1 = 0 := by decide
private theorem root2 : (2 : ZMod 3) ^ 2 - 2 + 1 = 0 := by decide

local notation "P37" => eisensteinResidueIdeal (37 : ZMod 43) root37
local notation "P7" => eisensteinResidueIdeal (7 : ZMod 43) root7

-- Numeric ratio calibration uses the field equation rather than reducing division.
example : gtailSevenResidueRoot 43 5 8 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (8 : ZMod 43) ≠ 0)).mpr
  decide

example : (1 - (37 : ZMod 43)) = 7 := by decide
example : norm (gtailSevenNormCoord 5 8) = 129 ∧ (129 : ℕ) = 3 * 43 := by
  rw [norm_gtailSevenNormCoord]
  norm_num

-- Membership now lives in bundled hom kernels, rather than only scalar evaluations.
example : gtailSevenNormCoord 5 8 ∈ P37 := by
  rw [mem_eisensteinResidueIdeal_iff]
  decide

example : gtailSevenNormCoord 5 8 ∉ P7 := by
  rw [mem_eisensteinResidueIdeal_iff]
  decide

example : P37 ≠ P7 := by
  intro heq
  have hm : gtailSevenNormCoord 5 8 ∈ P37 := by
    rw [mem_eisensteinResidueIdeal_iff]
    decide
  have hn : gtailSevenNormCoord 5 8 ∉ P7 := by
    rw [mem_eisensteinResidueIdeal_iff]
    decide
  exact hn (heq ▸ hm)

example : eisensteinResidueRingHom (37 : ZMod 43) root37
    (conj (gtailSevenNormCoord 5 8)) = 18 := by
  rw [eisensteinResidueRingHom_apply]
  decide

example : eisensteinResidueRingHom (7 : ZMod 43) root7
    (conj (gtailSevenNormCoord 5 8)) = 0 := by
  rw [eisensteinResidueRingHom_apply]
  decide

example : conj (gtailSevenNormCoord 5 8) ∈ P7 ∧ conj (gtailSevenNormCoord 5 8) ∉ P37 := by
  simp only [mem_eisensteinResidueIdeal_iff]
  decide

-- Scalar membership in the kernels is distinct from scalar element divisibility.
example : ofInt (-1) ((43 : ℕ) : ℤ) ∈ P37 ∧
    ofInt (-1) ((43 : ℕ) : ℤ) ∈ P7 ∧
    ¬ ofInt (-1) ((43 : ℕ) : ℤ) ∣ gtailSevenNormCoord 5 8 := by
  refine ⟨scalar_mem_eisensteinResidueIdeal _ _, scalar_mem_eisensteinResidueIdeal _ _, ?_⟩
  rw [scalar_dvd_gtailSevenNormCoord_iff]
  decide

example : (43 : ℤ) ∣ norm (gtailSevenNormCoord 5 8) := by
  apply (prime_dvd_norm_iff_mem_eisensteinResidueIdeals
    (by decide : Nat.Prime 43) (37 : ZMod 43) root37 _).mpr
  left
  rw [mem_eisensteinResidueIdeal_iff]
  decide

-- Arbitrary signed coordinates are accepted by the norm-product endpoint.
example : (norm (⟨-2, 3⟩ : TraceOneInt (-1)) : ZMod 43) =
    eisensteinResidueEval (37 : ZMod 43) ⟨-2, 3⟩ *
      eisensteinResidueEval (7 : ZMod 43) ⟨-2, 3⟩ := by
  have h := norm_cast_eq_eisensteinResidue_product (37 : ZMod 43) root37
    (⟨-2, 3⟩ : TraceOneInt (-1))
  rw [show 1 - (37 : ZMod 43) = 7 by decide] at h
  exact h

-- Optional maximality gate and its prime consequence are actually instantiated.
example : (P37).IsMaximal := eisensteinResidueIdeal_isMaximal (by decide) _ _
example : (P37).IsPrime := by
  let : (P37).IsMaximal := eisensteinResidueIdeal_isMaximal (by decide) _ _
  infer_instance

-- The characteristic-three slots coincide; root proof terms are irrelevant.
example : gtailSevenResidueRoot 3 1 1 = 2 ∧ 1 - gtailSevenResidueRoot 3 1 1 = 2 := by
  norm_num [gtailSevenResidueRoot]
  decide

example : eisensteinResidueIdeal (2 : ZMod 3) root2 =
    eisensteinResidueIdeal (1 - (2 : ZMod 3)) (eisensteinResidue_conjugate_root _ root2) := by
  ext z
  simp only [mem_eisensteinResidueIdeal_iff]
  rw [show 1 - (2 : ZMod 3) = 2 by decide]

example : gtailSevenNormCoord 1 1 ∈ eisensteinResidueIdeal (2 : ZMod 3) root2 := by
  rw [mem_eisensteinResidueIdeal_iff]
  decide

-- Without a root proof, evaluation fails multiplication preservation at the generator.
example : (0 : ZMod 43) ^ 2 - 0 + 1 ≠ 0 ∧
    eisensteinResidueEval (0 : ZMod 43) (tau (-1) * tau (-1)) ≠
      eisensteinResidueEval (0 : ZMod 43) (tau (-1)) *
        eisensteinResidueEval (0 : ZMod 43) (tau (-1)) := by
  decide

example {q : ℕ} (hq : Nat.Prime q) (t : ZMod q) (ht : t ^ 2 - t + 1 = 0)
    (z : TraceOneInt (-1)) :
    (q : ℤ) ∣ norm z ↔ z ∈ eisensteinResidueIdeal t ht ∨
      z ∈ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) :=
  prime_dvd_norm_iff_mem_eisensteinResidueIdeals hq t ht z

example : eisensteinResidueIdeal (gtailSevenResidueRoot 43 5 8)
      (gtailSevenResidueRoot_polynomial (by decide) (by decide)) ≠
    eisensteinResidueIdeal (1 - gtailSevenResidueRoot 43 5 8)
      (gtailSevenResidueRoot_conjugate_polynomial (by decide) (by decide)) :=
  gtailSevenResidueIdeals_ne_conjugate (by decide) (by decide) (by decide)

#print axioms DkMath.Lib.NumberTheory.eisensteinResidueRingHom
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueRingHom_apply
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueRingHom_ofInt
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueRingHom_tau
#print axioms DkMath.Lib.NumberTheory.eisensteinResidue_conjugate_root
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueRingHom_conj
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueIdeal
#print axioms DkMath.Lib.NumberTheory.mem_eisensteinResidueIdeal_iff
#print axioms DkMath.Lib.NumberTheory.norm_cast_eq_eisensteinResidue_product
#print axioms DkMath.Lib.NumberTheory.prime_dvd_norm_iff_mem_eisensteinResidueIdeals
#print axioms DkMath.Lib.NumberTheory.scalar_mem_eisensteinResidueIdeal
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueRingHom_surjective
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueIdeal_isMaximal
#print axioms DkMath.Lib.NumberTheory.gtailSevenNormCoord_mem_residueIdeal
#print axioms DkMath.Lib.NumberTheory.gtailSevenNormCoord_not_mem_conjugate_residueIdeal
#print axioms DkMath.Lib.NumberTheory.gtailSevenResidueIdeals_ne_conjugate

end DkMathTest.NumberTheory.GTailSevenResidueIdeal
