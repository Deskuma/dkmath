/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedCapacityIndependence

#print "file: DkMathTest.FLT.Seven.GTailFocusedCapacityIndependence"

namespace DkMathTest.FLT.Seven.GTailFocusedCapacityIndependence

open DkMath.FLT.Seven DkMath.CosmicFormula DkMath.Lib.NumberTheory
open DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall
open DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity
open DkMath.FLT.Seven.GTailFocusedCapacityIndependence
open DkMath.FLT.Seven.GTailGenericPrimeReceiver DkMath.FLT.Seven.GTailPrimeGrid

private theorem supportA :
    Nat.primeFactors (13 ^ 2 + 13 * 35 + 35 ^ 2) = {43} := by
  have hp : Nat.Prime 43 := by norm_num
  rw [show 13 ^ 2 + 13 * 35 + 35 ^ 2 = 43 * 43 from by decide,
    Nat.primeFactors_mul (by decide : 43 ≠ 0) (by decide : 43 ≠ 0),
    hp.primeFactors]
  decide

private theorem supportB :
    Nat.primeFactors (1497 ^ 2 + 1497 * 2797 + 2797 ^ 2) = {37, 385171} := by
  have hp : Nat.Prime 37 := by norm_num
  have hr : Nat.Prime 385171 := by norm_num
  rw [show 1497 ^ 2 + 1497 * 2797 + 2797 ^ 2 = 37 * 385171 from by decide,
    Nat.primeFactors_mul (by decide : 37 ≠ 0) (by decide : 385171 ≠ 0),
    hp.primeFactors, hr.primeFactors]
  decide

example : 13 ^ 2 + 13 * 35 + 35 ^ 2 = 1849 := by decide

example : focusedFermatDefect 13 35 46 = (-371415611824 : ℤ) := by decide

example : focusedFermatDefect 13 35 46 < 0 := by decide

example : (focusedFermatDefect 13 35 46).natAbs = 371415611824 := by decide

example : 0 < 13 ∧ 0 < 35 ∧ Nat.Coprime 13 35 ∧ 13 + 35 = 46 + 2 ∧
    0 < 2 ∧ 2 < 13 ∧ 2 < 35 ∧
    13 < 46 ∧ 35 < 46 ∧ 46 < 13 + 35 := by decide

example : squarePrimeSupportModulus (Nat.primeFactors (13 ^ 2 + 13 * 35 + 35 ^ 2)) = 1849 := by
  rw [supportA]
  decide

example : ¬ Fermat7Equation 13 35 46 := by
  intro h
  exact (by decide : focusedFermatDefect 13 35 46 ≠ 0)
    (focusedFermatDefect_zero_iff.mpr h)

example : ¬ 2 * GTail 7 1 2 46 = 7 * 13 * 35 * (13 + 35) * (13 ^ 2 + 13 * 35 + 35 ^ 2) ^ 2 := by
  intro h
  have he := (fermat7Equation_iff_focused_scalar_balance (by decide : 13 + 35 = 46 + 2)).mpr h
  exact (by decide : focusedFermatDefect 13 35 46 ≠ 0)
    (focusedFermatDefect_zero_iff.mpr he)

example : 1497 ^ 2 + 1497 * 2797 + 2797 ^ 2 = 14251327 := by decide

example : focusedFermatDefect 1497 2797 2802 = (-179820312066002 : ℤ) := by decide

example : focusedFermatDefect 1497 2797 2802 < 0 := by decide

example : (focusedFermatDefect 1497 2797 2802).natAbs = 179820312066002 := by decide

example : 0 < 1497 ∧ 0 < 2797 ∧ Nat.Coprime 1497 2797 ∧ 1497 + 2797 = 2802 + 1492 ∧
    0 < 1492 ∧ 1492 < 1497 ∧ 1492 < 2797 ∧
    1497 < 2802 ∧ 2797 < 2802 ∧ 2802 < 1497 + 2797 := by decide

example : squarePrimeSupportModulus (Nat.primeFactors (1497 ^ 2 + 1497 * 2797 + 2797 ^ 2)) =
    203100321260929 := by
  rw [supportB]
  decide

example : ¬ Fermat7Equation 1497 2797 2802 := by
  intro h
  exact (by decide : focusedFermatDefect 1497 2797 2802 ≠ 0)
    (focusedFermatDefect_zero_iff.mpr h)

example : ¬ 1492 * GTail 7 1 1492 2802 =
    7 * 1497 * 2797 * (1497 + 2797) * (1497 ^ 2 + 1497 * 2797 + 2797 ^ 2) ^ 2 := by
  intro h
  have he := (fermat7Equation_iff_focused_scalar_balance (by decide : 1497 + 2797 = 2802 + 1492)).mpr h
  exact (by decide : focusedFermatDefect 1497 2797 2802 ≠ 0)
    (focusedFermatDefect_zero_iff.mpr he)

example : squarePrimeSupportModulus (Nat.primeFactors (13 ^ 2 + 13 * 35 + 35 ^ 2)) <
    (13 ^ 2 + 13 * 35 + 35 ^ 2) ^ 2 := by
  rw [supportA]
  decide

example : squarePrimeSupportModulus (Nat.primeFactors (13 ^ 2 + 13 * 35 + 35 ^ 2)) <
    (focusedFermatDefect 13 35 46).natAbs := by
  rw [supportA]
  decide

example : ∀ p ∈ Nat.primeFactors (13 ^ 2 + 13 * 35 + 35 ^ 2),
    (p : ℤ) ^ 2 ∣ focusedFermatDefect 13 35 46 := by
  rw [supportA]
  intro p hp
  simp only [Finset.mem_singleton] at hp
  subst p
  decide

example : (focusedFermatDefect 1497 2797 2802).natAbs <
    squarePrimeSupportModulus (Nat.primeFactors (1497 ^ 2 + 1497 * 2797 + 2797 ^ 2)) := by
  rw [supportB]
  decide

example : GTail 7 1 2 46 = 75625342528 := by decide

example : 43 ^ 2 ∣ GTail 7 1 2 46 ∧ ¬ 43 ∣ 2 ∧ ¬ 43 ∣ 35 ∧ ¬ 43 ∣ 46 := by decide

example : ¬ (37 : ℤ) ∣ focusedFermatDefect 1497 2797 2802 := by decide

example : ¬ (385171 : ℤ) ∣ focusedFermatDefect 1497 2797 2802 := by decide

example : ¬ (37 : ℤ) ^ 2 ∣ focusedFermatDefect 1497 2797 2802 := by decide

example : ¬ (385171 : ℤ) ^ 2 ∣ focusedFermatDefect 1497 2797 2802 := by decide

private instance : Fact (Nat.Prime 43) := ⟨by norm_num⟩

example : (43 ^ 2 ∣ 2 ∧ ¬ 43 ∣ GTail 7 1 2 46 ∧ gtailSevenTailRatio 43 46 2 = 1) ∨
    (43 ^ 2 ∣ GTail 7 1 2 46 ∧ ¬ 43 ∣ 2) :=
  defect_square_prime_route (a := 13) (b := 35) (q := 43)
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem row : gtailSevenResidueRoot 43 13 35 = (7 : ZMod 43) := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (35 : ZMod 43) ≠ 0)).mpr
  decide

private theorem column : gtailSevenTailRatio 43 46 2 = (16 : ZMod 43) := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (46 : ZMod 43) ≠ 0)).mpr
  decide

example : (7 : ZMod 43) ^ 2 - 7 + 1 = 0 ∧ (16 : ZMod 43) ^ 7 = 1 ∧
    (16 : ZMod 43) ≠ 0 ∧ (16 : ZMod 43) ≠ 1 := by decide

example : nativeKernel (q := 43) 13 35 46 2 (by decide) (by decide) (by decide) (by decide) (by decide) =
    M (1 : Fin 2) (4 : Fin 6) := by
  unfold nativeKernel nativeEval
  simp only [row, column]
  apply congrArg RingHom.ker
  ext x
  rfl

example : ¬ (∀ p ∈ Nat.primeFactors (1166 ^ 2 + 1166 * 1857 + 1857 ^ 2),
    (p : ℤ) ^ 2 ∣ focusedFermatDefect 1166 1857 1858) := by
  intro h
  exact (by decide : ¬ (7 : ℤ) ^ 2 ∣ focusedFermatDefect 1166 1857 1858)
    (h 7 (Nat.mem_primeFactors.mpr ⟨by decide, by decide, by decide⟩))

example : ¬ (focusedFermatDefect 1166 1857 1858).natAbs <
    squarePrimeSupportModulus (Nat.primeFactors (1166 ^ 2 + 1166 * 1857 + 1857 ^ 2)) := by
  have hc := quadratic_modulus_le_square 1166 1857 (by decide)
  have hd : (1166 ^ 2 + 1166 * 1857 + 1857 ^ 2) ^ 2 <
      (focusedFermatDefect 1166 1857 1858).natAbs := by decide
  exact not_lt.mpr (hc.trans (le_of_lt hd))

example : ¬ (∀ p ∈ Nat.primeFactors (196 ^ 2 + 196 * 211 + 211 ^ 2),
    (p : ℤ) ^ 2 ∣ focusedFermatDefect 196 211 238) := by
  intro h
  exact (by decide : ¬ (3 : ℤ) ^ 2 ∣ focusedFermatDefect 196 211 238)
    (h 3 (Nat.mem_primeFactors.mpr ⟨by decide, by decide, by decide⟩))

example : ¬ (focusedFermatDefect 196 211 238).natAbs <
    squarePrimeSupportModulus (Nat.primeFactors (196 ^ 2 + 196 * 211 + 211 ^ 2)) := by
  have hc := quadratic_modulus_le_square 196 211 (by decide)
  have hd : (196 ^ 2 + 196 * 211 + 211 ^ 2) ^ 2 <
      (focusedFermatDefect 196 211 238).natAbs := by decide
  exact not_lt.mpr (hc.trans (le_of_lt hd))

example : eisenstein43Root (1 : Fin 2) = 7 ∧ seven43Root (4 : Fin 6) = 16 := by decide

example : ¬ (∀ p ∈ Nat.primeFactors (1497 ^ 2 + 1497 * 2797 + 2797 ^ 2),
    (p : ℤ) ^ 2 ∣ focusedFermatDefect 1497 2797 2802) := by
  rw [supportB]
  intro h
  exact (by decide : ¬ (37 : ℤ) ^ 2 ∣ focusedFermatDefect 1497 2797 2802)
    (h 37 (by decide))

-- The missing fourth non-Fermat row is excluded by the existing conditional theorem.
example (a b c : ℕ) (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0)
    (hs : ∀ p ∈ Nat.primeFactors (a ^ 2 + a * b + b ^ 2),
      (p : ℤ) ^ 2 ∣ focusedFermatDefect a b c)
    (hz : ¬ Fermat7Equation a b c) :
    ¬ (focusedFermatDefect a b c).natAbs <
      squarePrimeSupportModulus (Nat.primeFactors (a ^ 2 + a * b + b ^ 2)) := by
  intro hsize
  exact hz (full_quadratic_defect_zero_certificate a b c hQ0 hs hsize)

private theorem value_two (q n : ℕ) (hq : Nat.Prime q) (hn : n ≠ 0)
    (h2 : q ^ 2 ∣ n) (h3 : ¬ q ^ 3 ∣ n) : padicValNat q n = 2 := by
  have hlo := (padicValNat_le_iff_dvd hq hn 2).mpr h2
  have hhi : ¬ 3 ≤ padicValNat q n := by
    rw [padicValNat_le_iff_dvd hq hn 3]
    exact h3
  omega

example : padicValNat 43 (13 ^ 2 + 13 * 35 + 35 ^ 2) = 2 :=
  value_two _ _ (by norm_num) (by decide) (by decide) (by decide)

example : padicValNat 43 (GTail 7 1 2 46) = 2 :=
  value_two _ _ (by norm_num) (by decide) (by decide) (by decide)

example : padicValNat 43 2 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)

example : padicValNat 43 2 + padicValNat 43 (GTail 7 1 2 46) ≠
    2 * padicValNat 43 (13 ^ 2 + 13 * 35 + 35 ^ 2) := by
  rw [value_two 43 (GTail 7 1 2 46) (by norm_num) (by decide) (by decide) (by decide),
    value_two 43 (13 ^ 2 + 13 * 35 + 35 ^ 2) (by norm_num) (by decide) (by decide) (by decide),
    padicValNat.eq_zero_of_not_dvd (by decide : ¬ 43 ∣ 2)]
  decide

#check DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_full_support_without_size
#print axioms DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_full_support_without_size
#check DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_size_without_full_support
#print axioms DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_size_without_full_support
#check Nat.primeFactors_mul
#check Nat.Prime.primeFactors
#check Nat.mem_primeFactors_of_ne_zero

end DkMathTest.FLT.Seven.GTailFocusedCapacityIndependence
