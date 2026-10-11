/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall

#print "file: DkMathTest.FLT.Seven.GTailFocusedDefectSquareFirewall"

namespace DkMathTest.FLT.Seven.GTailFocusedDefectSquareFirewall

open DkMath.CosmicFormula DkMath.Lib.NumberTheory DkMath.FLT.Seven
open DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall
open DkMath.FLT.Seven.GTailFocusedPrimeRoute DkMath.FLT.Seven.GTailGenericPrimeReceiver
open DkMath.FLT.Seven.GTailCommonReceiver DkMath.NumberTheory.TraceOneQuadratic

section Symbolic

variable {q a b c g : ℕ}

example (hfocus : a + b = c + g) :
    focusedFermatDefect a b c = (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) -
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) * ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ) ^ 2 :=
  focusedFermatDefect_eq hfocus
example (hfocus : a + b = c + g) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q : ℤ) ^ 2 ∣ focusedFermatDefect a b c ↔
      (q : ℤ) ^ 2 ∣ (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) :=
  defect_square_iff_product_int hfocus hQ
example (hfocus : a + b = c + g) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q : ℤ) ^ 2 ∣ focusedFermatDefect a b c ↔ q ^ 2 ∣ g * GTail 7 1 g c :=
  defect_square_iff_product_nat hfocus hQ
example (hq : Nat.Prime q) (hcop : Nat.Coprime a b) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hD : (q : ℤ) ∣ focusedFermatDefect a b c) : ¬ q ∣ c :=
  endpoint_unit_of_defect hq hcop hQ hD
example [Fact (Nat.Prime q)] (hq7 : q ≠ 7) (hcop : Nat.Coprime a b)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hfocus : a + b = c + g)
    (hD2 : (q : ℤ) ^ 2 ∣ focusedFermatDefect a b c) :
    (q ^ 2 ∣ g ∧ ¬ q ∣ GTail 7 1 g c ∧ gtailSevenTailRatio q c g = 1) ∨
      (q ^ 2 ∣ GTail 7 1 g c ∧ ¬ q ∣ g) :=
  defect_square_prime_route hq7 hcop hQ hfocus hD2
example : focusedFermatDefect a b c = 0 ↔ Fermat7Equation a b c := focusedFermatDefect_zero_iff
example (hfocus : a + b = c + g) :
    focusedFermatDefect a b c = 0 ↔ g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  focusedFermatDefect_zero_iff.trans (fermat7Equation_iff_focused_scalar_balance hfocus)

end Symbolic

private theorem value_one (q n : ℕ) (hq : Nat.Prime q) (hn : n ≠ 0)
    (h1 : q ∣ n) (h2 : ¬ q ^ 2 ∣ n) : padicValNat q n = 1 := by
  have hlo := (padicValNat_le_iff_dvd hq hn 1).mpr (by simpa only [pow_one] using h1)
  have hhi : ¬ 2 ≤ padicValNat q n := by rw [padicValNat_le_iff_dvd hq hn 2]; exact h2
  omega

private theorem value_two (q n : ℕ) (hq : Nat.Prime q) (hn : n ≠ 0)
    (h2 : q ^ 2 ∣ n) (h3 : ¬ q ^ 3 ∣ n) : padicValNat q n = 2 := by
  have hlo := (padicValNat_le_iff_dvd hq hn 2).mpr h2
  have hhi : ¬ 3 ≤ padicValNat q n := by rw [padicValNat_le_iff_dvd hq hn 3]; exact h3
  omega

namespace Tail43

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local notation "Q" => (1166 ^ 2 + 1166 * 1857 + 1857 ^ 2 : ℕ)
local notation "T" => GTail 7 1 (1165 : ℕ) 1858
local notation "Δ" => focusedFermatDefect 1166 1857 1858

example : (1166 + 1857 : ℕ) = 1858 + 1165 ∧ Nat.Coprime 1166 1857 ∧
    0 < (1165 : ℕ) ∧ (1165 : ℕ) < 1166 ∧ (1165 : ℕ) < 1857 ∧
    (1166 : ℕ) < 1858 ∧ (1857 : ℕ) < 1858 ∧ (1858 : ℕ) < 1166 + 1857 := by decide
example : Q = 6973267 ∧ T = 1914732507483487090603 := by decide
example : Δ = (2642627963860178152897 : ℤ) := by decide
example : 0 < Δ := by decide
example : (43 : ℕ) ≠ 7 ∧ (43 : ℕ) ∣ Q ∧ ¬ (43 : ℕ) ^ 2 ∣ Q := by decide
example : (43 : ℤ) ^ 2 ∣ Δ ∧ ¬ (43 : ℤ) ^ 3 ∣ Δ ∧ Δ ≠ 0 := by decide
example : ¬ (43 : ℕ) ∣ 1858 :=
  endpoint_unit_of_defect (a := 1166) (b := 1857) (by decide) (by decide) (by decide) (by decide)
example : ((43 : ℕ) ^ 2 ∣ 1165 ∧ ¬ (43 : ℕ) ∣ T ∧ gtailSevenTailRatio 43 1858 1165 = 1) ∨
    ((43 : ℕ) ^ 2 ∣ T ∧ ¬ (43 : ℕ) ∣ 1165) :=
  defect_square_prime_route (a := 1166) (b := 1857) (by decide) (by decide) (by decide) (by decide) (by decide)
example : ¬ Fermat7Equation 1166 1857 1858 :=
  fun h => (by decide : Δ ≠ 0) (focusedFermatDefect_zero_iff.mpr h)
example : ¬ ((1165 : ℕ) * T = 7 * 1166 * 1857 * (1166 + 1857) * Q ^ 2) := by
  intro h
  have he := (fermat7Equation_iff_focused_scalar_balance (by decide : (1166 + 1857 : ℕ) = 1858 + 1165)).mpr h
  exact (by decide : Δ ≠ 0) (focusedFermatDefect_zero_iff.mpr he)
private theorem vQ : padicValNat 43 Q = 1 := value_one _ _ (by decide) (by decide) (by decide) (by decide)
private theorem vD : padicValNat 43 (Δ).natAbs = 2 :=
  value_two _ _ (by decide) (by decide) (by decide) (by decide)
example : padicValNat 43 Q = 1 ∧ padicValNat 43 (Δ).natAbs = 2 := ⟨vQ, vD⟩
private theorem vT : padicValNat 43 T = 2 := value_two _ _ (by decide) (by decide) (by decide) (by decide)
example : (43 : ℕ) ^ 2 ∣ T ∧ ¬ (43 : ℕ) ∣ 1165 := by decide
example : padicValNat 43 1165 = 0 ∧ padicValNat 43 T = 2 :=
  ⟨padicValNat.eq_zero_of_not_dvd (by decide), vT⟩
example : padicValNat 43 1165 + padicValNat 43 T = 2 * padicValNat 43 Q := by
  rw [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (43 : ℕ) ∣ 1165), vT, vQ]
local notation "J" => nativeKernel 1166 1857 1858 1165 (by decide : (43 : ℕ) ∣ Q)
  (by decide) (by decide) (by decide) (by decide)
example : (J).IsMaximal := nativeKernel_isMaximal _ _ _ _ _ _ _ _ _
example : fromEisenstein ((gtailSevenNormCoord 1166 1857 : TraceOneInt (-1)) ^ 2) ∈ J ^ 2 ∧
    fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) ∈ J ^ 2 ∧
    fromEisenstein (gtailSevenNormCoord 1166 1857) * fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) ∈ J ^ 3 ∧
    fromEisenstein ((gtailSevenNormCoord 1166 1857 : TraceOneInt (-1)) ^ 2) *
      fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) ∈ J ^ 4 :=
  native_square_support _ _ _ _ _ _ _ _ _ (by decide) (by decide)

end Tail43

namespace Gap13

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local notation "Q" => (196 ^ 2 + 196 * 211 + 211 ^ 2 : ℕ)
local notation "T" => GTail 7 1 (169 : ℕ) 238
local notation "Δ" => focusedFermatDefect 196 211 238

example : (196 + 211 : ℕ) = 238 + 169 ∧ Nat.Coprime 196 211 ∧
    0 < (169 : ℕ) ∧ (169 : ℕ) < 196 ∧ (169 : ℕ) < 211 ∧
    (196 : ℕ) < 238 ∧ (211 : ℕ) < 238 ∧ (238 : ℕ) < 196 + 211 := by decide
example : Q = 124293 ∧ T = 10690523583988879 := by decide
example : Δ = (-13523337259569605 : ℤ) := by decide
example : Δ < 0 := by decide
example : (13 : ℕ) ≠ 7 ∧ (13 : ℕ) ∣ Q ∧ ¬ (13 : ℕ) ^ 2 ∣ Q := by decide
example : (13 : ℤ) ^ 2 ∣ Δ ∧ ¬ (13 : ℤ) ^ 3 ∣ Δ ∧ Δ ≠ 0 := by decide
example : ¬ (13 : ℕ) ∣ 238 :=
  endpoint_unit_of_defect (a := 196) (b := 211) (by decide) (by decide) (by decide) (by decide)
example : ((13 : ℕ) ^ 2 ∣ 169 ∧ ¬ (13 : ℕ) ∣ T ∧ gtailSevenTailRatio 13 238 169 = 1) ∨
    ((13 : ℕ) ^ 2 ∣ T ∧ ¬ (13 : ℕ) ∣ 169) :=
  defect_square_prime_route (a := 196) (b := 211) (by decide) (by decide) (by decide) (by decide) (by decide)
example : ¬ Fermat7Equation 196 211 238 :=
  fun h => (by decide : Δ ≠ 0) (focusedFermatDefect_zero_iff.mpr h)
example : ¬ ((169 : ℕ) * T = 7 * 196 * 211 * (196 + 211) * Q ^ 2) := by
  intro h
  have he := (fermat7Equation_iff_focused_scalar_balance (by decide : (196 + 211 : ℕ) = 238 + 169)).mpr h
  exact (by decide : Δ ≠ 0) (focusedFermatDefect_zero_iff.mpr he)
private theorem vQ : padicValNat 13 Q = 1 := value_one _ _ (by decide) (by decide) (by decide) (by decide)
private theorem vD : padicValNat 13 (Δ).natAbs = 2 :=
  value_two _ _ (by decide) (by decide) (by decide) (by decide)
example : padicValNat 13 Q = 1 ∧ padicValNat 13 (Δ).natAbs = 2 := ⟨vQ, vD⟩
private theorem vg : padicValNat 13 169 = 2 := value_two _ _ (by decide) (by decide) (by decide) (by decide)
example : (13 : ℕ) ^ 2 ∣ 169 ∧ ¬ (13 : ℕ) ∣ T := by decide
example : gtailSevenTailRatio 13 238 169 = 1 := gap_ratio_eq_one (by decide) (by decide)
example : ¬ (gtailSevenTailRatio 13 238 169 ≠ 1) := gap_nonidentity_guard_unavailable (by decide) (by decide)
example : padicValNat 13 169 = 2 ∧ padicValNat 13 T = 0 :=
  ⟨vg, padicValNat.eq_zero_of_not_dvd (by decide)⟩
example : padicValNat 13 169 + padicValNat 13 T = 2 * padicValNat 13 Q := by
  rw [vg, padicValNat.eq_zero_of_not_dvd (by decide : ¬ (13 : ℕ) ∣ T), vQ]

end Gap13

-- The earlier small controls fail the new square-defect premise.
example : ¬ (13 : ℤ) ^ 2 ∣ focusedFermatDefect 14 29 30 := by decide
example : ¬ (43 : ℤ) ^ 2 ∣ focusedFermatDefect 5 8 9 := by decide
example : (5 + 8 : ℕ) = 9 + 4 ∧ (43 : ℕ) ∣ 5 ^ 2 + 5 * 8 + 8 ^ 2 ∧
    ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 4 9 := by decide
example : (14 + 29 : ℕ) = 30 + 13 ∧ (13 : ℕ) ∣ 14 ^ 2 + 14 * 29 + 29 ^ 2 ∧
    ¬ (13 : ℕ) ^ 2 ∣ 13 := by decide

-- A further focused congruence control separates square support from budget equality.
namespace BudgetCountermodel
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local notation "Q" => (2198 ^ 2 + 2198 * 2213 + 2213 ^ 2 : ℕ)
local notation "T" => GTail 7 1 (2197 : ℕ) 2214
example : (2198 + 2213 : ℕ) = 2214 + 2197 ∧ Nat.Coprime 2198 2213 ∧
    0 < (2197 : ℕ) ∧ (2197 : ℕ) < 2198 ∧ (2197 : ℕ) < 2213 ∧
    (2198 : ℕ) < 2214 ∧ (2213 : ℕ) < 2214 ∧ (2214 : ℕ) < 2198 + 2213 := by decide
example : (13 : ℕ) ∣ Q ∧ (13 : ℤ) ^ 2 ∣ focusedFermatDefect 2198 2213 2214 ∧
    focusedFermatDefect 2198 2213 2214 ≠ 0 := by decide
example : ¬ (padicValNat 13 2197 + padicValNat 13 T = 2 * padicValNat 13 Q) := by
  have hQv : padicValNat 13 Q = 1 := value_one _ _ (by decide) (by decide) (by decide) (by decide)
  have hg3 : 3 ≤ padicValNat 13 2197 :=
    (padicValNat_le_iff_dvd (by decide : Nat.Prime 13) (by decide : (2197 : ℕ) ≠ 0) 3).mpr (by decide)
  rw [hQv]
  omega
end BudgetCountermodel

#check DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect
#print axioms DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect
#check DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect_eq
#print axioms DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect_eq
#check DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_iff_product_int
#print axioms DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_iff_product_int
#check DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_iff_product_nat
#print axioms DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_iff_product_nat
#check DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.endpoint_unit_of_defect
#print axioms DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.endpoint_unit_of_defect
#check DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_prime_route
#print axioms DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_prime_route
#check DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect_zero_iff
#print axioms DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect_zero_iff

end DkMathTest.FLT.Seven.GTailFocusedDefectSquareFirewall
