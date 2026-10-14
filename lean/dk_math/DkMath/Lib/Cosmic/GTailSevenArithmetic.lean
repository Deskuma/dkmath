/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailCongruence
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

#print "file: DkMath.Lib.Cosmic.GTailSevenArithmetic"

/-!
# Neutral arithmetic for the degree-seven factors

These natural-number statements require no Fermat equation. The residual
seven-layer result assumes its endpoint is a unit modulo seven explicitly;
no coprimality of a focused gap is inferred.
-/

namespace DkMath.CosmicFormula

/-- The first coordinate is coprime to the quadratic at a primitive pair. -/
theorem coprime_left_seven_quadratic {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime a (a ^ 2 + a * b + b ^ 2) := by
  have hform : a ^ 2 + a * b + b ^ 2 = b ^ 2 + a * (a + b) := by ring
  rw [hform]
  exact (Nat.coprime_add_mul_left_right a (b ^ 2) (a + b)).mpr (hcop.pow_right 2)

/-- The symmetric coordinate is coprime to the same quadratic. -/
theorem coprime_right_seven_quadratic {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime b (a ^ 2 + a * b + b ^ 2) := by
  have hswap : b ^ 2 + b * a + a ^ 2 = a ^ 2 + a * b + b ^ 2 := by ring
  rw [← hswap]
  exact coprime_left_seven_quadratic hcop.symm

/-- The coordinate sum is coprime to the quadratic at a primitive pair. -/
theorem coprime_sum_seven_quadratic {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime (a + b) (a ^ 2 + a * b + b ^ 2) := by
  have hsumprod : Nat.Coprime (a + b) (a * b) :=
    (Nat.coprime_self_add_left.mpr hcop.symm).mul_right
      (Nat.coprime_add_self_left.mpr hcop)
  apply Nat.coprime_of_dvd'
  intro q _hq hqsum hqQ
  have hidentity : (a ^ 2 + a * b + b ^ 2) + a * b = (a + b) ^ 2 := by ring
  have hqtotal : q ∣ (a ^ 2 + a * b + b ^ 2) + a * b := by
    rw [hidentity]
    exact hqsum.trans (dvd_pow_self (a + b) (by decide : 2 ≠ 0))
  have hqab : q ∣ a * b := (Nat.dvd_add_right hqQ).mp hqtotal
  have hgcd := Nat.dvd_gcd hqsum hqab
  simpa [hsumprod.gcd_eq_one] using hgcd

/-- All three ordinary coordinate factors are coprime to the quadratic. -/
theorem coprime_product_seven_quadratic {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime (a * b * (a + b)) (a ^ 2 + a * b + b ^ 2) :=
  ((coprime_left_seven_quadratic hcop).mul_left
    (coprime_right_seven_quadratic hcop)).mul_left
      (coprime_sum_seven_quadratic hcop)

/-- Exactly one divisibility layer at seven, with an explicit endpoint-unit premise. -/
theorem gtail_seven_exact_seven_layer {g c : ℕ} (hgap : 7 ∣ g) (hend : ¬ 7 ∣ c) :
    7 ∣ GTail 7 1 g c ∧ ¬ 7 ^ 2 ∣ GTail 7 1 g c := by
  have hp : Nat.Prime 7 := by decide
  refine ⟨(prime_dvd_GN_iff_dvd_gap hp).mpr hgap, ?_⟩
  intro hsq
  have hmod := GN_modEq_head_mod_sq_of_odd_prime_dvd_x g c hp (by norm_num) hgap
  have hhead : 7 ^ 2 ∣ 7 * c ^ (7 - 1) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hsq))
  have hpow : 7 ∣ c ^ (7 - 1) :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7)
      (by simpa only [pow_two] using hhead)
  exact hend (hp.dvd_of_dvd_pow hpow)

end DkMath.CosmicFormula
