/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenEisensteinResidue

#print "file: DkMathTest.NumberTheory.GTailSevenEisensteinResidue"

namespace DkMathTest.NumberTheory.GTailSevenEisensteinResidue

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- The norm divisor is not a scalar ring divisor.
example : (43 : ℤ) ∣ norm (gtailSevenNormCoord 5 8) ∧
    ¬ ofInt (-1) ((43 : ℕ) : ℤ) ∣ gtailSevenNormCoord 5 8 := by
  constructor
  · exact (dvd_quadratic_iff_dvd_gtailSevenNormCoord 43 5 8).mp (by decide)
  · rw [scalar_dvd_gtailSevenNormCoord_iff]
    decide

private theorem root43 : gtailSevenResidueRoot 43 5 8 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (8 : ZMod 43) ≠ 0)).mpr
  decide

example : gtailSevenResidueRoot 43 5 8 = 37 := root43
example : 1 - gtailSevenResidueRoot 43 5 8 = 7 := by
  rw [root43]
  decide
example : (129 : ℕ) = 3 * 43 ∧ norm (gtailSevenNormCoord 5 8) = 129 := by
  rw [norm_gtailSevenNormCoord]
  norm_num

example : eisensteinResidueEval (gtailSevenResidueRoot 43 5 8)
    (gtailSevenNormCoord 5 8) = 0 :=
  eisensteinResidueEval_gtailSevenNormCoord_zero (by decide)

example : eisensteinResidueEval (1 - gtailSevenResidueRoot 43 5 8)
    (gtailSevenNormCoord 5 8) = 18 := by
  rw [eisensteinResidueEval_gtailSevenNormCoord_conjugate (by decide)]
  decide

example : eisensteinResidueEval (1 - gtailSevenResidueRoot 43 5 8)
    (gtailSevenNormCoord 5 8) ≠ 0 :=
  eisensteinResidueEval_gtailSevenNormCoord_conjugate_ne_zero
    (by decide) (by decide) (by decide)

example : gtailSevenResidueRoot 43 5 8 ≠ 1 - gtailSevenResidueRoot 43 5 8 :=
  gtailSevenResidueRoot_ne_conjugate (by decide) (by decide) (by decide)

-- Actual computations independently confirm both slots, including negative casts.
example : (5 + 8 * 37 : ZMod 43) = 0 ∧ (5 + 8 * 7 : ZMod 43) = 18 ∧
    (18 : ZMod 43) ≠ 0 := by decide

example : eisensteinResidueEval (37 : ZMod 43) (conj (gtailSevenNormCoord 5 8)) = 18 := by
  decide

-- The coordinate square has a negative first coordinate; evaluation is still coherent.
example : eisensteinResidueEval (gtailSevenResidueRoot 43 5 8)
    (gtailSevenNormCoord 5 8 * gtailSevenNormCoord 5 8) = 0 := by
  rw [eisensteinResidueEval_mul _ (gtailSevenResidueRoot_polynomial (by decide) (by decide)),
    eisensteinResidueEval_gtailSevenNormCoord_zero (by decide), mul_zero]

-- Characteristic three has a repeated root and two zero evaluations.
example : gtailSevenResidueRoot 3 1 1 = 2 ∧
    1 - gtailSevenResidueRoot 3 1 1 = 2 ∧
    eisensteinResidueEval (gtailSevenResidueRoot 3 1 1) (gtailSevenNormCoord 1 1) = 0 ∧
    eisensteinResidueEval (1 - gtailSevenResidueRoot 3 1 1) (gtailSevenNormCoord 1 1) = 0 := by
  norm_num [gtailSevenResidueRoot, eisensteinResidueEval, gtailSevenNormCoord, eisensteinCoord]
  decide

example : gtailSevenResidueRoot 3 1 1 ^ 2 - gtailSevenResidueRoot 3 1 1 + 1 = 0 :=
  gtailSevenResidueRoot_polynomial (by decide) (by decide)

-- Harmless b=0 boundary: no nonzero-denominator theorem is invoked.
example : gtailSevenNormCoord 5 0 * conj (gtailSevenNormCoord 5 0) = ofInt (-1) 25 := by
  have h := gtailSevenNormCoord_mul_conj 5 0
  norm_num at h
  exact h

example : ¬ (¬ (43 : ℕ) ∣ 0) := by simp

example {q a b : ℕ} [Fact (Nat.Prime q)] (hq3 : q ≠ 3)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    (gtailSevenResidueRoot q a b ^ 2 - gtailSevenResidueRoot q a b + 1 = 0) ∧
    ((1 - gtailSevenResidueRoot q a b) ^ 2 - (1 - gtailSevenResidueRoot q a b) + 1 = 0) ∧
    gtailSevenResidueRoot q a b ≠ 1 - gtailSevenResidueRoot q a b :=
  ⟨gtailSevenResidueRoot_polynomial hQ hb,
    gtailSevenResidueRoot_conjugate_polynomial hQ hb,
    gtailSevenResidueRoot_ne_conjugate hq3 hQ hb⟩

#print axioms DkMath.Lib.NumberTheory.gtailSevenNormCoord_mul_conj
#print axioms DkMath.Lib.NumberTheory.conj_gtailSevenNormCoord
#print axioms DkMath.Lib.NumberTheory.scalar_dvd_gtailSevenNormCoord_iff
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueEval
#print axioms DkMath.Lib.NumberTheory.gtailSevenResidueRoot
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueEval_add
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueEval_mul
#print axioms DkMath.Lib.NumberTheory.gtailSevenResidueRoot_polynomial
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueEval_gtailSevenNormCoord_zero
#print axioms DkMath.Lib.NumberTheory.gtailSevenResidueRoot_conjugate_polynomial
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueEval_gtailSevenNormCoord_conjugate
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueEval_conj
#print axioms DkMath.Lib.NumberTheory.gtailSevenResidue_trace_ne_zero
#print axioms DkMath.Lib.NumberTheory.eisensteinResidueEval_gtailSevenNormCoord_conjugate_ne_zero
#print axioms DkMath.Lib.NumberTheory.gtailSevenResidueRoot_ne_conjugate

end DkMathTest.NumberTheory.GTailSevenEisensteinResidue
