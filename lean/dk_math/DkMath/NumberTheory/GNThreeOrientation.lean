/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GNThreeQuadratic

#print "file: DkMath.NumberTheory.GNThreeOrientation"

/-!
# Cubic orientation arithmetic

The common divisor of the two primitive cubic orientations divides 14.
This excludes common prime squares, while allowing common ordinary support.
-/

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom

/-- Integer Bezout-type identity for the two natural cubic GN orientations. -/
theorem GN_three_orientation_bezout (a b : ℕ) :
    (3*(b:ℤ)-9*a)*((GN 3 a b : ℕ) : ℤ) +
      (3*(a:ℤ)+5*b)*((GN 3 b a : ℕ) : ℤ) = 14*(b:ℤ)^3 := by
  simp only [GN_three_dual_explicit]
  push_cast
  ring

/-- The second identity follows by exchanging the natural coordinates. -/
theorem GN_three_orientation_bezout_swap (a b : ℕ) :
    (3*(a:ℤ)-9*b)*((GN 3 b a : ℕ) : ℤ) +
      (3*(b:ℤ)+5*a)*((GN 3 a b : ℕ) : ℤ) = 14*(a:ℤ)^3 :=
  GN_three_orientation_bezout b a

/-- Coprime coordinates bound the common GN divisor by the squarefree integer 14. -/
theorem gcd_GN_three_swap_dvd_fourteen (a b : ℕ) (hc : Nat.Coprime a b) :
    Nat.gcd (GN 3 a b) (GN 3 b a) ∣ 14 := by
  let d := Nat.gcd (GN 3 a b) (GN 3 b a)
  have hf : (d:ℤ) ∣ ((GN 3 a b : ℕ) : ℤ) := by exact_mod_cast Nat.gcd_dvd_left (GN 3 a b) (GN 3 b a)
  have hg : (d:ℤ) ∣ ((GN 3 b a : ℕ) : ℤ) := by exact_mod_cast Nat.gcd_dvd_right (GN 3 a b) (GN 3 b a)
  have hb : d ∣ 14*b^3 := by
    have h := dvd_add (dvd_mul_of_dvd_right hf (3*(b:ℤ)-9*a))
      (dvd_mul_of_dvd_right hg (3*(a:ℤ)+5*b))
    rw [GN_three_orientation_bezout] at h
    exact_mod_cast h
  have ha : d ∣ 14*a^3 := by
    have h := dvd_add (dvd_mul_of_dvd_right hg (3*(a:ℤ)-9*b))
      (dvd_mul_of_dvd_right hf (3*(b:ℤ)+5*a))
    rw [GN_three_orientation_bezout_swap] at h
    exact_mod_cast h
  have h := Nat.dvd_gcd ha hb
  rw [Nat.gcd_mul_left, (hc.pow 3 3).gcd_eq_one, mul_one] at h
  exact h

/-- No prime can occur to depth at least two in both orientations. -/
theorem not_prime_sq_dvd_both_GN_three {a b q : ℕ} (hc : Nat.Coprime a b)
    (hq : Nat.Prime q) : ¬ (q^2 ∣ GN 3 a b ∧ q^2 ∣ GN 3 b a) := by
  rintro ⟨hf,hg⟩
  have h := (Nat.dvd_gcd hf hg).trans (gcd_GN_three_swap_dvd_fourteen a b hc)
  have hle := Nat.le_of_dvd (by norm_num : 0 < 14) h
  have hqle : q ≤ 3 := by nlinarith
  interval_cases q <;> norm_num at *

/-- The two orientations can share the ordinary prime 7. -/
example : Nat.gcd (GN 3 (1 : ℕ) 1) (GN 3 (1 : ℕ) 1) = 7 := by
  simp only [GN_three_dual_explicit]
  norm_num

end DkMath.NumberTheory
