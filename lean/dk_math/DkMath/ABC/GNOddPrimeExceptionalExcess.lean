/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNValuationExcess

#print "file: DkMath.ABC.GNOddPrimeExceptionalExcess"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# The exceptional GN valuation at exponent five

This module proves the local arithmetic kernel for the prime dividing the
exponent when that exponent is five.  For coprime boundary coordinates, a
factor of five in `GN 5 a b` occurs with valuation exactly one.

The finite exceptional-support sum and the general odd-prime case are outside
the scope of this module.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- The canonical general `GN` polynomial specialized to exponent five. -/
theorem GN_five_eq_explicit (a b : ℕ) :
    GN 5 a b =
      a ^ 4 + 5 * a ^ 3 * b + 10 * a ^ 2 * b ^ 2 +
        10 * a * b ^ 3 + 5 * b ^ 4 := by
  rw [GN_eq_sum]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- At exponent five, every non-boundary term has a visible factor of five. -/
theorem GN_five_eq_boundary_add_five_mul (a b : ℕ) :
    GN 5 a b =
      a ^ 4 +
        5 * (a ^ 3 * b + 2 * a ^ 2 * b ^ 2 + 2 * a * b ^ 3 + b ^ 4) := by
  rw [GN_five_eq_explicit]
  ring

/--
If the exponent-five GN kernel is divisible by five, then its boundary
coordinate is divisible by five.
-/
theorem five_dvd_boundary_of_dvd_GN_five
    {a b : ℕ} (h5GN : 5 ∣ GN 5 a b) :
    5 ∣ a := by
  have hGNmod : GN 5 a b % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd h5GN
  have haPowMod : a ^ 4 % 5 = 0 := by
    rw [GN_five_eq_boundary_add_five_mul] at hGNmod
    simpa [Nat.add_mod] using hGNmod
  have haPow : 5 ∣ a ^ 4 :=
    Nat.dvd_iff_mod_eq_zero.mpr haPowMod
  exact Nat.prime_five.dvd_of_dvd_pow haPow

/--
After substituting a factor of five in the boundary coordinate, all terms
except `5 * b^4` have a visible factor of twenty-five.
-/
theorem GN_five_five_mul_eq_twentyFive_mul_add (k b : ℕ) :
    GN 5 (5 * k) b =
      25 * (25 * k ^ 4 + 25 * k ^ 3 * b + 10 * k ^ 2 * b ^ 2 +
        2 * k * b ^ 3) + 5 * b ^ 4 := by
  rw [GN_five_eq_explicit]
  ring

/--
For coprime boundary coordinates, divisibility by five cannot lift to
divisibility by twenty-five.
-/
theorem not_twentyFive_dvd_GN_five_of_coprime
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    ¬ 25 ∣ GN 5 a b := by
  intro h25GN
  obtain ⟨k, rfl⟩ := five_dvd_boundary_of_dvd_GN_five h5GN
  let K :=
    25 * k ^ 4 + 25 * k ^ 3 * b + 10 * k ^ 2 * b ^ 2 +
      2 * k * b ^ 3
  have hdecomp : GN 5 (5 * k) b = 25 * K + 5 * b ^ 4 := by
    simpa [K] using GN_five_five_mul_eq_twentyFive_mul_add k b
  obtain ⟨t, ht⟩ := h25GN
  have hbPow : 5 ∣ b ^ 4 := by
    refine ⟨t - K, ?_⟩
    omega
  have h5b : 5 ∣ b :=
    Nat.prime_five.dvd_of_dvd_pow hbPow
  have h5copb : Nat.Coprime 5 b :=
    hcop.coprime_dvd_left (by exact dvd_mul_right 5 k)
  exact (Nat.prime_five.coprime_iff_not_dvd.mp h5copb) h5b

/--
For coprime boundary coordinates, a factor of five in the exponent-five GN
kernel has exact p-adic valuation one.
-/
theorem padicValNat_five_GN_five_eq_one_of_dvd
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    padicValNat 5 (GN 5 a b) = 1 := by
  have hNoSquare :=
    not_twentyFive_dvd_GN_five_of_coprime hcop h5GN
  have hGN0 : GN 5 a b ≠ 0 := by
    intro hzero
    apply hNoSquare
    rw [hzero]
    exact dvd_zero 25
  have hOneLe : 1 ≤ padicValNat 5 (GN 5 a b) :=
    padicValNat_one_le_of_prime_dvd Nat.prime_five hGN0 h5GN
  have hLtTwo : padicValNat 5 (GN 5 a b) < 2 := by
    by_contra hNot
    have hTwoLe : 2 ≤ padicValNat 5 (GN 5 a b) :=
      Nat.le_of_not_gt hNot
    apply hNoSquare
    have hPowDvd :=
      (padicValNat_le_iff_dvd Nat.prime_five hGN0 2).mp hTwoLe
    norm_num at hPowDvd ⊢
    exact hPowDvd
  omega

/-- Factorization form of the exact exponent-five exceptional valuation. -/
theorem factorization_five_GN_five_eq_one_of_dvd
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    (GN 5 a b).factorization 5 = 1 := by
  rw [Nat.factorization_def (GN 5 a b) Nat.prime_five]
  exact padicValNat_five_GN_five_eq_one_of_dvd hcop h5GN

end DkMath.ABC
