/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenPairedResidue
import DkMath.FLT.Seven.Basic

#print "file: DkMathTest.NumberTheory.GTailSevenPairedResidue"

namespace DkMathTest.NumberTheory.GTailSevenPairedResidue

open DkMath.CosmicFormula DkMath.Lib.NumberTheory DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem root37 : (37 : ZMod 43) ^ 2 - 37 + 1 = 0 := by decide
private theorem root7 : (7 : ZMod 43) ^ 2 - 7 + 1 = 0 := by decide
local notation "P37" => eisensteinResidueIdeal (37 : ZMod 43) root37
local notation "P7" => eisensteinResidueIdeal (7 : ZMod 43) root7
local notation "α" => gtailSevenNormCoord 5 8

-- Satisfiable Tail-side data; the exact Fermat equation is false.
example : (5 : ℕ) + 8 = 9 + 4 ∧ Nat.Coprime 5 8 := by decide
example : (5 : ℕ) ^ 2 + 5 * 8 + 8 ^ 2 = 129 ∧ (129 : ℕ) = 3 * 43 := by decide
example : (43 : ℕ) ∣ 5 ^ 2 + 5 * 8 + 8 ^ 2 ∧ 43 ∣ GTail 7 1 4 9 := by decide
example : ¬ (43 : ℕ) ∣ 5 * 8 * 9 * 4 := by decide
example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide

private theorem quadratic_ratio43 : gtailSevenResidueRoot 43 5 8 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (8 : ZMod 43) ≠ 0)).mpr
  decide

private theorem tail_ratio43 : gtailSevenTailRatio 43 9 4 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide

example : gtailSevenResidueRoot 43 5 8 = 37 ∧ 1 - (37 : ZMod 43) = 7 :=
  ⟨quadratic_ratio43, by decide⟩
example : gtailSevenTailRatio 43 9 4 = 11 := tail_ratio43

example : (37 : ZMod 43) ^ 2 - 37 + 1 = 0 ∧ (11 : ZMod 43) ^ 7 = 1 ∧
    (11 : ZMod 43) ≠ 1 ∧ (11 : ZMod 43) ≠ 0 ∧
    (11 : ZMod 43) ^ 6 + 11 ^ 5 + 11 ^ 4 + 11 ^ 3 + 11 ^ 2 + 11 + 1 = 0 := by decide

-- Apply the general paired receiver and reuse the oriented address APIs.
example : 43 ≠ 3 ∧
    gtailSevenResidueRoot 43 5 8 ^ 2 - gtailSevenResidueRoot 43 5 8 + 1 = 0 ∧
    gtailSevenTailRatio 43 9 4 ^ 7 = 1 ∧ gtailSevenTailRatio 43 9 4 ≠ 1 ∧
    gtailSevenTailRatio 43 9 4 ≠ 0 ∧
    (gtailSevenTailRatio 43 9 4 ^ 6 + gtailSevenTailRatio 43 9 4 ^ 5 +
      gtailSevenTailRatio 43 9 4 ^ 4 + gtailSevenTailRatio 43 9 4 ^ 3 +
      gtailSevenTailRatio 43 9 4 ^ 2 + gtailSevenTailRatio 43 9 4 + 1 = 0) :=
  gtailSeven_paired_residue (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

example : α ∈ P37 ∧ α ∉ P7 := by
  simp only [mem_eisensteinResidueIdeal_iff]
  decide

example : (α : TraceOneInt (-1)) ^ 2 ∈ P37 * P37 ∧
    (α : TraceOneInt (-1)) ^ 2 ∉ P7 ∧
    (α : TraceOneInt (-1)) ^ 2 ∉ eisensteinScalarIdeal 43 := by
  have h := gtailSevenNormCoord_split_square_address
    (q := 43) (a := 5) (b := 8) (by decide) (by decide) (by decide)
  have hp : eisensteinResidueIdeal (1 - (37 : ZMod 43))
      (eisensteinResidue_conjugate_root _ root37) = P7 := by
    ext z
    simp only [mem_eisensteinResidueIdeal_iff]
    rw [show 1 - (37 : ZMod 43) = 7 by decide]
  simp only [quadratic_ratio43] at h
  rw [hp] at h
  exact h

example : (21 : ℕ) ∣ 43 - 1 :=
  twentyOne_dvd_prime_sub_one_of_quadratic_gtail (by decide) (by decide)
    (by decide : (43 : ℕ) ∣ 5 ^ 2 + 5 * 8 + 8 ^ 2)
    (by decide : (43 : ℕ) ∣ GTail 7 1 4 9)
    (by decide) (by decide) (by decide) (by decide)

-- A thin conjunction keeps the ideal address in its original integral ring.
example {q a b c g : ℕ} [Fact (Nat.Prime q)] (hq7 : q ≠ 7)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c)
    (hb : ¬ q ∣ b) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) :
    gtailSevenNormCoord a b ∈ eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_polynomial hQ hb) ∧
    gtailSevenNormCoord a b ∉ eisensteinResidueIdeal (1 - gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_conjugate_polynomial hQ hb) ∧
    gtailSevenNormCoord a b ^ 2 ∈
      eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
          (gtailSevenResidueRoot_polynomial hQ hb) *
        eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
          (gtailSevenResidueRoot_polynomial hQ hb) ∧
    gtailSevenNormCoord a b ^ 2 ∉ eisensteinScalarIdeal q ∧
    gtailSevenTailRatio q c g ^ 7 = 1 ∧ gtailSevenTailRatio q c g ≠ 1 := by
  have hpair := gtailSeven_paired_residue hq7 hQ hT hb hc hg
  have hsquare := gtailSevenNormCoord_split_square_address hpair.1 hQ hb
  exact ⟨gtailSevenNormCoord_mem_residueIdeal hQ hb,
    gtailSevenNormCoord_not_mem_conjugate_residueIdeal hpair.1 hQ hb,
    hsquare.1, hsquare.2.2, hpair.2.2.1, hpair.2.2.2.1⟩

-- Gap support does not supply the nonzero gap premise.
example : (14 : ℕ) + 29 = 30 + 13 ∧ (13 : ℕ) ∣ 14 ^ 2 + 14 * 29 + 29 ^ 2 ∧
    (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : gtailSevenTailRatio 13 30 13 = 1 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (30 : ZMod 13) ≠ 0)).mpr
  decide

-- Repeated, inert, and excluded-characteristic boundaries.
example : (2 : ZMod 3) ^ 2 - 2 + 1 = 0 ∧ (2 : ZMod 3) = 1 - 2 := by decide
example : ¬ ∃ t : ZMod 5, t ^ 2 - t + 1 = 0 := by decide
example : (7 : ℕ) ∣ GTail 7 1 7 1 ∧ (7 : ℕ) ∣ 7 := by decide
example : gtailSevenTailRatio 7 1 7 = 1 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (1 : ZMod 7) ≠ 0)).mpr
  decide

-- The seventh-power identity alone does not imply the geometric sum vanishes.
example : (1 : ZMod 43) ^ 7 = 1 ∧
    (1 : ZMod 43) ^ 6 + 1 ^ 5 + 1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1 ≠ 0 := by decide

#print axioms DkMath.Lib.NumberTheory.gtailSevenTailRatio
#print axioms DkMath.Lib.NumberTheory.gtailSevenTailRatio_pow_seven
#print axioms DkMath.Lib.NumberTheory.gtailSevenTailRatio_ne_one
#print axioms DkMath.Lib.NumberTheory.gtailSevenTailRatio_ne_zero
#print axioms DkMath.Lib.NumberTheory.seven_geom_sum_eq_zero_of_pow_eq_one
#print axioms DkMath.Lib.NumberTheory.gtailSeven_paired_residue

end DkMathTest.NumberTheory.GTailSevenPairedResidue
