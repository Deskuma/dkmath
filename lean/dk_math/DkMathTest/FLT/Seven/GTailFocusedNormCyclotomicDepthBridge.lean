/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge

#print "file: DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge"

namespace DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula
open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

-- Abstract scalar allocation: Q=43 and T=43², not a native Fermat tuple.
private theorem abstract_budget : padicValNat 43 4 + padicValNat 43 (43 ^ 2) =
    2 * padicValNat 43 43 := by
  rw [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (43 : ℕ) ∣ 4),
    padicValNat.prime_pow, padicValNat_self]

example : padicValNat 43 (43 ^ 2) = 2 * padicValNat 43 43 :=
  scalar_budget_tail_double _ _ _ _ (by decide) abstract_budget
example : ((43 : ℕ) ^ 2 ∣ 43 ^ 2 ↔ (43 : ℕ) ∣ 43) ∧
    ((43 : ℕ) ^ 4 ∣ 43 ^ 2 ↔ (43 : ℕ) ^ 2 ∣ 43) ∧
    ((43 : ℕ) ^ 3 ∣ 43 ^ 2 ↔ (43 : ℕ) ^ 4 ∣ 43 ^ 2) ∧
    ¬ ((43 : ℕ) ^ 3 ∣ 43 ^ 2 ∧ ¬ (43 : ℕ) ^ 4 ∣ 43 ^ 2) :=
  scalar_budget_depth_readouts 43 4 (43 ^ 2) 43 (by decide)
    (by decide) (by decide) (by decide) abstract_budget
-- Failed gap-unit control: genuine budget, but the Tail valuation is odd.
example : padicValNat 43 43 + padicValNat 43 43 = 2 * padicValNat 43 43 := by omega
example : (43 : ℕ) ∣ 43 ∧ padicValNat 43 43 = 1 := by
  exact ⟨by decide, padicValNat_self⟩


-- Odd exact depth three also satisfies the budget when the gap is not a unit.
example : padicValNat 43 43 + padicValNat 43 (43 ^ 3) =
    2 * padicValNat 43 (43 ^ 2) := by
  rw [padicValNat_self, padicValNat.prime_pow, padicValNat.prime_pow]
example : (43 : ℕ) ^ 3 ∣ 43 ^ 3 ∧ ¬ (43 : ℕ) ^ 4 ∣ 43 ^ 3 := by decide

private theorem root37 : (37 : ZMod 43) ^ 2 - 37 + 1 = 0 := by decide
private theorem root7 : (7 : ZMod 43) ^ 2 - 7 + 1 = 0 := by decide
local notation "P37" => eisensteinResidueIdeal (37 : ZMod 43) root37
local notation "P7" => eisensteinResidueIdeal (7 : ZMod 43) root7
local notation "α" => gtailSevenNormCoord 5 8
local notation "K43" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)

private theorem conjugate37_eq7 :
    eisensteinResidueIdeal (1 - (37 : ZMod 43)) (eisensteinResidue_conjugate_root _ root37) = P7 := by
  ext z
  simp only [mem_eisensteinResidueIdeal_iff]
  rw [show 1 - (37 : ZMod 43) = 7 by decide]

-- Honest mixed-carrier calibration: this tuple fails the Fermat equation and balance.
example : norm α = 129 ∧ (43 : ℕ) ∣ 5 ^ 2 + 5 * 8 + 8 ^ 2 := by
  rw [norm_gtailSevenNormCoord]
  norm_num
example : gtailSevenResidueRoot 43 5 8 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (8 : ZMod 43) ≠ 0)).mpr
  decide
example : (α : TraceOneInt (-1)) ^ 2 ∈ P37 * P37 ∧
    (α : TraceOneInt (-1)) ^ 2 ∉ P7 ∧ (α : TraceOneInt (-1)) ^ 2 ∉ eisensteinScalarIdeal 43 := by
  have h := split_eisenstein_square_address (by decide : Nat.Prime 43)
    (37 : ZMod 43) root37 (by decide) α
    (by rw [mem_eisensteinResidueIdeal_iff]; decide)
    (by rw [mem_eisensteinResidueIdeal_iff]; decide)
  rw [conjugate37_eq7] at h
  simpa only [pow_two] using h

private theorem ratio (g : ℕ) (hg : g = 4 ∨ g = 32598) :
    gtailSevenTailRatio 43 9 g = 11 := by
  rcases hg with rfl | rfl <;> dsimp [gtailSevenTailRatio] <;>
    apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr <;> decide
example : gtailSevenTailRatio 43 9 4 = 11 := ratio _ (by decide)
example : (43 : ℕ) ∣ GTail 7 1 4 9 ∧ ¬ (43 : ℕ) ∣ 8 ∧
    ¬ (43 : ℕ) ∣ 9 ∧ ¬ (43 : ℕ) ∣ 4 := by decide
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∈ K43 (sixInverseSlot i) ∧
    gtailCyclotomicFactor 9 4 i ∉ K43 (sixInverseSlot i) ^ 2 := by
  intro i
  have h := gtailCyclotomicFactor_depth_one (q := 43) 9 4
    (by decide) (by decide) (by decide) (by decide) i
  simpa only [ratio 4 (by decide)] using h
example : ¬ ((4 : ℕ) * GTail 7 1 4 9 =
    7 * 5 * 8 * (5 + 8) * (5 ^ 2 + 5 * 8 + 8 ^ 2) ^ 2) := by decide
example : ¬ Fermat7Equation 5 8 9 := by unfold Fermat7Equation; decide

-- The bounded third-depth control is outside the focused tuple relation.
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 32598 i ∈ K43 (sixInverseSlot i) ^ 3 ∧
    gtailCyclotomicFactor 9 32598 i ∉ K43 (sixInverseSlot i) ^ 4 := by
  intro i
  have h := gtailCyclotomicFactor_depth_three (q := 43) 9 32598
    (by decide) (by decide) (by decide) (by decide) (by decide) i
  simpa only [ratio 32598 (by decide)] using h
example : ¬ (5 + 8 : ℕ) = 9 + 32598 := by decide

-- Excluded characteristic, gap-only and zero-coordinate boundaries.
example : (2 : ZMod 3) = 1 - 2 := by decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : Fermat7Equation 0 3 3 ∧ ¬ (0 < (0 : ℕ)) := by
  norm_num [Fermat7Equation]

-- padicValNat q 0 is zero: nonzero premises cannot be erased from divisibility readouts.
example : padicValNat 43 4 + padicValNat 43 0 = 2 * padicValNat 43 1 ∧
    ¬ ((43 : ℕ) ^ 2 ∣ 0 ↔ (43 : ℕ) ∣ 1) := by
  rw [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (43 : ℕ) ∣ 4)]
  simp
example : padicValNat 43 4 + padicValNat 43 1 = 2 * padicValNat 43 0 ∧
    ¬ ((43 : ℕ) ^ 2 ∣ 1 ↔ (43 : ℕ) ∣ 0) := by
  rw [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (43 : ℕ) ∣ 4)]
  simp

-- Universal contract tests retain every FLT-facing hypothesis; no numeric Fermat fiction.
example {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    padicValNat q (GTail 7 1 g c) = 2 * padicValNat q (a ^ 2 + a * b + b ^ 2) ∧
    q ^ 2 ∣ GTail 7 1 g c ∧
    (q ^ 4 ∣ GTail 7 1 g c ↔ q ^ 2 ∣ a ^ 2 + a * b + b ^ 2) ∧
    (q ^ 3 ∣ GTail 7 1 g c ↔ q ^ 4 ∣ GTail 7 1 g c) :=
  focused_norm_scalar_depth_readouts ha hb hcop hEq hsum hq7 hQ hT

example {q a b c g : ℕ} [Fact (Nat.Prime q)]
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
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) :=
  focused_eisenstein_norm_square_endpoint ha hb hcop hEq hsum hq7 hQ hT

example {q a b c g : ℕ} [Fact (Nat.Prime q)]
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
      ¬ (gtailCyclotomicFactor c g i ∈ K ^ 3 ∧ gtailCyclotomicFactor c g i ∉ K ^ 4) :=
  focused_cyclotomic_depth_endpoint ha hb hcop hEq hsum hq7 hQ hT i

example {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    q ^ 4 ∣ GTail 7 1 g c ↔ (q : ℤ) ^ 2 ∣ norm (gtailSevenNormCoord a b) :=
  focused_tail_fourth_iff_norm_square_dvd ha hb hcop hEq hsum hq7 hQ hT

#print axioms DkMath.FLT.Seven.scalar_budget_tail_double
#print axioms DkMath.FLT.Seven.scalar_budget_depth_readouts
#print axioms DkMath.FLT.Seven.focused_norm_depth_guards
#print axioms DkMath.FLT.Seven.focused_norm_scalar_depth_readouts
#print axioms DkMath.FLT.Seven.focused_eisenstein_norm_square_endpoint
#print axioms DkMath.FLT.Seven.focused_cyclotomic_depth_endpoint
#print axioms DkMath.FLT.Seven.focused_tail_fourth_iff_norm_square_dvd

end DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge
