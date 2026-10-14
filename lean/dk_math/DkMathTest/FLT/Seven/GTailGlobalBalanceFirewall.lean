/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailGlobalBalanceFirewall

#print "file: DkMathTest.FLT.Seven.GTailGlobalBalanceFirewall"

namespace DkMathTest.FLT.Seven.GTailGlobalBalanceFirewall

open DkMath.FLT.Seven DkMath.CosmicFormula DkMath.Lib.NumberTheory
open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local notation "Q43" => (1166 ^ 2 + 1166 * 1857 + 1857 ^ 2 : ℕ)
local notation "T43" => GTail 7 1 1165 1858
local notation "α43" => gtailSevenNormCoord 1166 1857

example (a b c g : ℕ) (hfocus : a + b = c + g) :
    Fermat7Equation a b c ↔ g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  fermat7Equation_iff_focused_scalar_balance hfocus
example (a b c g : ℕ) (hfocus : a + b = c + g) :
    Fermat7Equation a b c ↔ (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) :=
  fermat7Equation_iff_focused_norm_balance hfocus
example (a b c g : ℕ) (hfocus : a + b = c + g) (hEq : Fermat7Equation a b c) :
    g * GTail 7 1 g c = 7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  (fermat7Equation_iff_focused_scalar_balance hfocus).mp hEq

-- Positive primitive additive focus and all strict geometry, without a Fermat premise.
private theorem geometry : 0 < (1166 : ℕ) ∧ 0 < (1857 : ℕ) ∧
    max (1166 : ℕ) 1857 < 1858 ∧ (1858 : ℕ) < 1166 + 1857 ∧
    0 < (1165 : ℕ) ∧ (1165 : ℕ) < min 1166 1857 ∧
    (1166 + 1857 : ℕ) = 1858 + 1165 := by decide
example : 0 < (1166 : ℕ) ∧ 0 < (1857 : ℕ) ∧ max (1166 : ℕ) 1857 < 1858 ∧
    (1858 : ℕ) < 1166 + 1857 ∧ 0 < (1165 : ℕ) ∧ (1165 : ℕ) < min 1166 1857 ∧
    (1166 + 1857 : ℕ) = 1858 + 1165 := geometry
example : Nat.Coprime 1166 1857 := by decide
example : (1166 + 1857 : ℕ) = 3023 ∧ (1858 + 1165 : ℕ) = 3023 := by decide
example : Q43 = 6973267 := by decide
example : T43 = 1914732507483487090603 := by decide

private theorem units : ¬ (43 : ℕ) ∣ 1166 ∧ ¬ (43 : ℕ) ∣ 1857 ∧
    ¬ (43 : ℕ) ∣ 1166 + 1857 ∧ ¬ (43 : ℕ) ∣ 1858 ∧ ¬ (43 : ℕ) ∣ 1165 := by decide
example : ¬ (43 : ℕ) ∣ 1166 ∧ ¬ (43 : ℕ) ∣ 1857 ∧
    ¬ (43 : ℕ) ∣ 1166 + 1857 ∧ ¬ (43 : ℕ) ∣ 1858 ∧ ¬ (43 : ℕ) ∣ 1165 := units
private theorem support : (43 : ℕ) ∣ Q43 ∧ ¬ (43 : ℕ) ^ 2 ∣ Q43 ∧
    (43 : ℕ) ^ 2 ∣ T43 ∧ ¬ (43 : ℕ) ^ 3 ∣ T43 := by decide
example : (43 : ℕ) ∣ Q43 ∧ ¬ (43 : ℕ) ^ 2 ∣ Q43 ∧
    (43 : ℕ) ^ 2 ∣ T43 ∧ ¬ (43 : ℕ) ^ 3 ∣ T43 := support

private theorem valueQ : padicValNat 43 Q43 = 1 := by
  have hlo := (padicValNat_le_iff_dvd (by decide : Nat.Prime 43) (by decide : Q43 ≠ 0) 1).mpr
    (by simpa only [pow_one] using support.1)
  have hhi : ¬ 2 ≤ padicValNat 43 Q43 := by
    rw [padicValNat_le_iff_dvd (by decide : Nat.Prime 43) (by decide : Q43 ≠ 0) 2]
    exact support.2.1
  omega
private theorem valueT : padicValNat 43 T43 = 2 := by
  have hlo := (padicValNat_le_iff_dvd (by decide : Nat.Prime 43) (by decide : T43 ≠ 0) 2).mpr
    support.2.2.1
  have hhi : ¬ 3 ≤ padicValNat 43 T43 := by
    rw [padicValNat_le_iff_dvd (by decide : Nat.Prime 43) (by decide : T43 ≠ 0) 3]
    exact support.2.2.2
  omega
private theorem budget : padicValNat 43 1165 + padicValNat 43 T43 = 2 * padicValNat 43 Q43 := by
  rw [padicValNat.eq_zero_of_not_dvd units.2.2.2.2, valueQ, valueT]
example : padicValNat 43 1165 = 0 ∧ padicValNat 43 Q43 = 1 ∧ padicValNat 43 T43 = 2 :=
  ⟨padicValNat.eq_zero_of_not_dvd units.2.2.2.2, valueQ, valueT⟩
example : padicValNat 43 1165 + padicValNat 43 T43 = 2 * padicValNat 43 Q43 := budget
example : (43 : ℕ) ^ 3 ∣ T43 ↔ (43 : ℕ) ^ 4 ∣ T43 :=
  (scalar_budget_depth_readouts 43 1165 T43 Q43 (by decide) (by decide) (by decide)
    units.2.2.2.2 budget).2.2.1
example : (3 : ℕ) ∣ 42 ∧ (7 : ℕ) ∣ 42 ∧ (21 : ℕ) ∣ 42 := by decide

private theorem not_fermat : ¬ Fermat7Equation 1166 1857 1858 := by
  unfold Fermat7Equation
  decide
example : ¬ Fermat7Equation 1166 1857 1858 := not_fermat
example : ¬ ((1165 : ℕ) * T43 = 7 * 1166 * 1857 * (1166 + 1857) * Q43 ^ 2) :=
  fun h => not_fermat ((fermat7Equation_iff_focused_scalar_balance (by decide)).mpr h)
example : ¬ ((1165 : ℕ) * T43 = 7 * 1166 * 1857 * (1166 + 1857) * Q43 ^ 2) := by decide
example : ¬ ((1165 : ℤ) * ((T43 : ℕ) : ℤ) =
    7 * 1166 * 1857 * ((1166 + 1857 : ℕ) : ℤ) * norm ((α43 : TraceOneInt (-1)) ^ 2)) :=
  fun h => not_fermat ((fermat7Equation_iff_focused_norm_balance (by decide)).mpr h)

-- An existential countermodel to sufficiency of this explicitly bounded local contract.
example : ∃ a b c g : ℕ,
    (0 < a ∧ 0 < b ∧ max a b < c ∧ c < a + b ∧ 0 < g ∧ g < min a b ∧ a + b = c + g) ∧
    Nat.Coprime a b ∧
    (¬ (43 : ℕ) ∣ a ∧ ¬ (43 : ℕ) ∣ b ∧ ¬ (43 : ℕ) ∣ a + b ∧
      ¬ (43 : ℕ) ∣ c ∧ ¬ (43 : ℕ) ∣ g) ∧
    ((43 : ℕ) ∣ a ^ 2 + a * b + b ^ 2 ∧ ¬ (43 : ℕ) ^ 2 ∣ a ^ 2 + a * b + b ^ 2 ∧
      (43 : ℕ) ^ 2 ∣ GTail 7 1 g c ∧ ¬ (43 : ℕ) ^ 3 ∣ GTail 7 1 g c) ∧
    padicValNat 43 g + padicValNat 43 (GTail 7 1 g c) =
      2 * padicValNat 43 (a ^ 2 + a * b + b ^ 2) ∧ ¬ Fermat7Equation a b c := by
  exact ⟨1166, 1857, 1858, 1165, geometry, by decide, units, support, budget, not_fermat⟩

private theorem root37 : (37 : ZMod 43) ^ 2 - 37 + 1 = 0 := by decide
private theorem root7 : (7 : ZMod 43) ^ 2 - 7 + 1 = 0 := by decide
local notation "P37" => eisensteinResidueIdeal (37 : ZMod 43) root37
local notation "P7" => eisensteinResidueIdeal (7 : ZMod 43) root7
local notation "K43" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)
private theorem eroot : gtailSevenResidueRoot 43 1166 1857 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (1857 : ZMod 43) ≠ 0)).mpr
  decide
private theorem rroot : gtailSevenTailRatio 43 1858 1165 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (1858 : ZMod 43) ≠ 0)).mpr
  decide
example : gtailSevenResidueRoot 43 1166 1857 = 37 := eroot
example : gtailSevenTailRatio 43 1858 1165 = 11 := rroot
example : (37 : ZMod 43) ≠ 11 ∧ (11 : ZMod 43) ^ 7 = 1 ∧ (11 : ZMod 43) ≠ 1 := by decide
example : norm α43 = (6973267 : ℤ) := by
  rw [norm_gtailSevenNormCoord]
  norm_num
example : (α43 : TraceOneInt (-1)) ^ 2 ∈ P37 * P37 ∧
    (α43 : TraceOneInt (-1)) ^ 2 ∉ P7 ∧ (α43 : TraceOneInt (-1)) ^ 2 ∉ eisensteinScalarIdeal 43 := by
  have h := gtailSevenNormCoord_split_square_address (q := 43) (a := 1166) (b := 1857)
    (by decide) support.1 units.2.1
  simpa only [eroot, show 1 - (37 : ZMod 43) = 7 by decide] using h
example : ∀ i : Fin 6, gtailCyclotomicFactor 1858 1165 i ∈ K43 (sixInverseSlot i) ^ 2 ∧
    gtailCyclotomicFactor 1858 1165 i ∉ K43 (sixInverseSlot i) ^ 3 := by
  intro i
  have h2 := gtailCyclotomicFactor_mem_square_iff (q := 43) 1858 1165
    units.2.2.2.1 units.2.2.2.2 (by decide) i
  have h3 := gtailCyclotomicFactor_mem_cube_iff (q := 43) 1858 1165
    units.2.2.2.1 units.2.2.2.2 (by decide) i
  simp only [rroot] at h2 h3
  exact ⟨h2.mpr support.2.2.1, fun h => support.2.2.2 (h3.mp h)⟩
example : ∀ i j : Fin 6, j ≠ sixInverseSlot i → gtailCyclotomicFactor 1858 1165 i ∉ K43 j := by
  intro i j hj
  have h := gtailCyclotomicFactor_unique_slot (q := 43) 1858 1165
    units.2.2.2.1 units.2.2.2.2 (by decide) i j
  simp only [rroot] at h
  exact fun hm => hj (h.mp hm)
example : sixInverseSlot = ![0, 3, 4, 1, 2, 5] := rfl

-- Earlier samples and excluded boundaries retain their exact missing premises.
-- The instruction's old-focus failure claim is false: 13=13, with strict geometry too.
example : (5 + 8 : ℕ) = 9 + 4 ∧ max (5 : ℕ) 8 < 9 ∧ (9 : ℕ) < 5 + 8 ∧
    0 < (4 : ℕ) ∧ (4 : ℕ) < min 5 8 := by decide
example : gtailSevenResidueRoot 43 5 8 = 37 ∧ gtailSevenTailRatio 43 9 4 = 11 := by
  constructor
  · dsimp [gtailSevenResidueRoot]
    apply (div_eq_iff (by decide : (8 : ZMod 43) ≠ 0)).mpr
    decide
  · dsimp [gtailSevenTailRatio]
    apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
    decide
example : (43 : ℕ) ∣ GTail 7 1 4 9 ∧ ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 4 9 := by decide
example : ¬ (padicValNat 43 4 + padicValNat 43 (GTail 7 1 4 9) =
    2 * padicValNat 43 (5 ^ 2 + 5 * 8 + 8 ^ 2)) := by
  intro hbgt
  have hr := scalar_budget_depth_readouts 43 4 (GTail 7 1 4 9)
    (5 ^ 2 + 5 * 8 + 8 ^ 2) (by decide) (by decide) (by decide) (by decide) hbgt
  exact (by decide : ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 4 9) (hr.1.mpr (by decide))
example : ¬ (5 + 8 : ℕ) = 9 + 32598 := by decide
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 32598 i ∈ K43 (sixInverseSlot i) ^ 3 ∧
    gtailCyclotomicFactor 9 32598 i ∉ K43 (sixInverseSlot i) ^ 4 := by
  intro i
  have h := gtailCyclotomicFactor_depth_three (q := 43) 9 32598
    (by decide) (by decide) (by decide) (by decide) (by decide) i
  have hr : gtailSevenTailRatio 43 9 32598 = 11 := by
    dsimp [gtailSevenTailRatio]
    apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
    decide
  simpa only [hr] using h
example : (2 : ZMod 3) = 1 - 2 := by decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : Fermat7Equation 0 3 3 ∧ ¬ (0 < (0 : ℕ)) := by norm_num [Fermat7Equation]
-- This witness does not satisfy every other known necessary FLT condition either.
example : ¬ (7 : ℕ) ∣ 1165 := by decide

#print axioms DkMath.FLT.Seven.fermat7Equation_iff_focused_scalar_balance
#print axioms DkMath.FLT.Seven.fermat7Equation_iff_focused_norm_balance

end DkMathTest.FLT.Seven.GTailGlobalBalanceFirewall
