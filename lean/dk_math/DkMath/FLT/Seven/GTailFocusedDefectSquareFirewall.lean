/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedPrimeRoute

#print "file: DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall"

/-!
# Signed defect stability at square depth

The exact signed Fermat defect is retained in ℤ. Square divisibility transports
through the existing focused identity without an equation premise. Finite local
support does not reconstruct exact global balance or a signed descent provider.
-/

namespace DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall

open DkMath.CosmicFormula DkMath.Lib.NumberTheory
open GTailFocusedPrimeRoute

/-- The signed degree-seven defect; natural subtraction is deliberately avoided. -/
def focusedFermatDefect (a b c : ℕ) : ℤ := (a : ℤ) ^ 7 + (b : ℤ) ^ 7 - (c : ℤ) ^ 7

/-- Focus identifies the signed defect with the difference of the two scalar terms. -/
theorem focusedFermatDefect_eq {a b c g : ℕ} (hfocus : a + b = c + g) :
    focusedFermatDefect a b c = (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) -
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) * ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ) ^ 2 := by
  have hf : (a : ℤ) + b = c + g := by exact_mod_cast hfocus
  have hs := gtail_seven_defect (a : ℤ) b c g hf
  have ht : ((GTail 7 1 g c : ℕ) : ℤ) = GTail 7 1 (g : ℤ) c := by simp [GTail]
  rw [ht]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  unfold focusedFermatDefect
  linear_combination -hs

/-- Quadratic support makes square defect divisibility equivalent to square product support. -/
theorem defect_square_iff_product_int {q a b c g : ℕ}
    (hfocus : a + b = c + g) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q : ℤ) ^ 2 ∣ focusedFermatDefect a b c ↔
      (q : ℤ) ^ 2 ∣ (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) := by
  have hQi : (q : ℤ) ∣ ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ) := by exact_mod_cast hQ
  have hterm : (q : ℤ) ^ 2 ∣
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) * ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ) ^ 2 :=
    dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hQi 2) _
  rw [focusedFermatDefect_eq hfocus]
  constructor
  · intro hd
    have hh := dvd_add hd hterm
    simpa only [sub_add_cancel] using hh
  · intro hp
    exact dvd_sub hp hterm

/-- The same square-product equivalence is transported to natural divisibility. -/
theorem defect_square_iff_product_nat {q a b c g : ℕ}
    (hfocus : a + b = c + g) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q : ℤ) ^ 2 ∣ focusedFermatDefect a b c ↔ q ^ 2 ∣ g * GTail 7 1 g c := by
  rw [defect_square_iff_product_int hfocus hQ]
  exact_mod_cast (Iff.rfl : q ^ 2 ∣ g * GTail 7 1 g c ↔ q ^ 2 ∣ g * GTail 7 1 g c)

/-- A first defect congruence excludes the endpoint without focus or a Fermat equation. -/
theorem endpoint_unit_of_defect {q a b c : ℕ} (hq : Nat.Prime q)
    (hcop : Nat.Coprime a b) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hD : (q : ℤ) ∣ focusedFermatDefect a b c) : ¬ q ∣ c := by
  have hprodunit : ¬ q ∣ a * b * (a + b) := by
    intro hd
    have hh := Nat.dvd_gcd hd hQ
    exact hq.not_dvd_one (by simpa [(coprime_product_seven_quadratic hcop).gcd_eq_one] using hh)
  have hsumunit : ¬ q ∣ a + b := fun hd => hprodunit (dvd_mul_of_dvd_right hd _)
  intro hc
  have hci : (q : ℤ) ∣ (c : ℤ) := by exact_mod_cast hc
  have hc7 : (q : ℤ) ∣ (c : ℤ) ^ 7 := hci.trans (dvd_pow_self _ (by decide : 7 ≠ 0))
  have hsi : (q : ℤ) ∣ (a : ℤ) ^ 7 + (b : ℤ) ^ 7 := by
    simpa only [focusedFermatDefect, sub_add_cancel] using dvd_add hD hc7
  have hsn : q ∣ a ^ 7 + b ^ 7 := by exact_mod_cast hsi
  have hi : q ∣ 7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
    dvd_mul_of_dvd_right (hQ.trans (dvd_pow_self _ (by decide : 2 ≠ 0))) _
  have hp : q ∣ (a + b) ^ 7 := by
    rw [add_pow_seven_eq_gap_add_interior]
    exact dvd_add (by simpa only [add_comm] using hsn) hi
  exact hsumunit (hq.dvd_of_dvd_pow hp)

/-- Square defect support routes a primitive focused input without an equation premise. -/
theorem defect_square_prime_route {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (hq7 : q ≠ 7) (hcop : Nat.Coprime a b) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hfocus : a + b = c + g) (hD2 : (q : ℤ) ^ 2 ∣ focusedFermatDefect a b c) :
    (q ^ 2 ∣ g ∧ ¬ q ∣ GTail 7 1 g c ∧ gtailSevenTailRatio q c g = 1) ∨
      (q ^ 2 ∣ GTail 7 1 g c ∧ ¬ q ∣ g) := by
  have hq : Nat.Prime q := Fact.out
  have hp := (defect_square_iff_product_nat hfocus hQ).mp hD2
  have hc := endpoint_unit_of_defect hq hcop hQ
    ((dvd_pow_self (q : ℤ) (by decide : 2 ≠ 0)).trans hD2)
  by_cases hg : q ∣ g
  · have ht := not_prime_dvd_gtail_seven_of_gap hq hq7 hg hc
    have hcopT : Nat.Coprime (q ^ 2) (GTail 7 1 g c) :=
      (hq.coprime_iff_not_dvd.mpr ht).pow_left 2
    have hg2 : q ^ 2 ∣ g := hcopT.dvd_of_dvd_mul_left (by simpa only [mul_comm] using hp)
    exact Or.inl ⟨hg2, ht, gap_ratio_eq_one hc hg⟩
  · have hcopG : Nat.Coprime (q ^ 2) g := (hq.coprime_iff_not_dvd.mpr hg).pow_left 2
    exact Or.inr ⟨hcopG.dvd_of_dvd_mul_left hp, hg⟩

/-- Exact zero defect is the original equation; finite congruence support is weaker. -/
theorem focusedFermatDefect_zero_iff {a b c : ℕ} :
    focusedFermatDefect a b c = 0 ↔ Fermat7Equation a b c := by
  unfold focusedFermatDefect Fermat7Equation
  rw [sub_eq_zero]
  norm_cast

end DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall
