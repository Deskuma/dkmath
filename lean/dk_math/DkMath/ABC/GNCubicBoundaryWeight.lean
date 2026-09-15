/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessLargeBoundaryPacket

#print "file: DkMath.ABC.GNCubicBoundaryWeight"

/-!
# Cubic target boundary weight

At t = 3/8 the actual canonical target weight is bounded by the same power
of its repeated modulus. This is not a bound for the large-profile sum.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory

/-- A prime congruent to one modulo three is at least seven. -/
theorem seven_le_prime_of_mod_three_eq_one {q : ℕ} (hq : Nat.Prime q) (hm : q % 3 = 1) : 7 ≤ q := by
  by_contra h
  have : q ≤ 6 := by omega
  interval_cases q <;> norm_num at *

/-- The actual canonical target weight at t = 3/8 costs at most repeatedPart^(3/8). -/
theorem GNExcess_cubic_target_boundaryWeight_le_repeatedPart_three_eighths {a b X : ℕ}
    (ha : 0 < a) (hb : 0 < b) (haX : a ∈ Finset.Icc 0 X)
    (hc : Nat.Coprime a b) :
    (GNExcessRootAddressCharge (GNNonExceptionalIntervalPrimeFamily 3 b X) 3
      (GNExcessDepthProfileAt (GNNonExceptionalIntervalPrimeFamily 3 b X) 3 b a) : ℝ) *
      Real.exp ((3/8:ℝ) * GNExcessActiveProfileMass
        (GNNonExceptionalIntervalPrimeFamily 3 b X)
        (GNExcessDepthProfileAt (GNNonExceptionalIntervalPrimeFamily 3 b X) 3 b a)) ≤
      (GNNonExceptionalRepeatedPart 3 a b : ℝ) ^ (3/8:ℝ) := by
  classical
  let N := GNNonExceptionalPart 3 a b
  let S := N.factorization.support.filter (fun q => 2 ≤ N.factorization q)
  let A := piSqRad N
  let C := sqTail N
  let R := GNExcessRootAddressCharge (GNNonExceptionalIntervalPrimeFamily 3 b X) 3
    (GNExcessDepthProfileAt (GNNonExceptionalIntervalPrimeFamily 3 b X) 3 b a)
  have hR : R = 2 ^ S.card := by
    dsimp [R, GNExcessRootAddressCharge]
    rw [GNExcessActivePrimeSet_target_eq_repeatedSupport Nat.prime_three haX hc]
  have hApr : A = ∏ q ∈ S, q := rfl
  have hq7 : ∀ q ∈ S, 7 ≤ q := by
    intro q hq
    have hqS : q ∈ GNNonExceptionalSupport 3 a b := by
      rw [← GNNonExceptionalPart_factorization_support]
      exact (Finset.mem_filter.mp hq).1
    have hprime := (mem_support_factorization_iff.mp (Finset.mem_filter.mp hqS).1).2.1
    exact seven_le_prime_of_mod_three_eq_one hprime
      ((Triple.mk a b (a+b) rfl hc).mod_eq_one_of_mem_GNNonExceptionalSupport Nat.prime_three ha hqS)
  have hpow : R ^ 8 ≤ A ^ 3 := by
    rw [hR, hApr, ← Finset.prod_pow]
    calc
      (2 ^ S.card) ^ 8 = ∏ q ∈ S, (256:ℕ) := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      _ ≤ ∏ q ∈ S, q ^ 3 := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro q hq
        have h := hq7 q hq
        exact (by norm_num : 256 ≤ 7^3).trans (Nat.pow_le_pow_left h 3)
  have hRp : 0 < (R:ℝ) := by rw [hR]; positivity
  have hAp : 0 < (A:ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (piSqRad_ge_one N))
  have hCp : 0 < (C:ℝ) := by
    apply Nat.cast_pos.mpr
    apply Nat.pos_of_ne_zero
    intro h
    have he := nat_eq_sqTail_mul_rad N (Nat.ne_of_gt (GNNonExceptionalPart_pos 3 a b))
    change C = 0 at h
    change N = C * rad N at he
    rw [h, zero_mul] at he
    exact (Nat.ne_of_gt (GNNonExceptionalPart_pos 3 a b)) he
  have hlog : 8 * Real.log (R:ℝ) ≤ 3 * Real.log (A:ℝ) := by
    have h := Real.log_le_log (pow_pos hRp 8) (show (R:ℝ)^8 ≤ (A:ℝ)^3 by exact_mod_cast hpow)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hrep : (GNNonExceptionalRepeatedPart 3 a b : ℝ) = (A:ℝ)*(C:ℝ) := by
    exact_mod_cast GNNonExceptionalRepeatedPart_eq_piSqRad_mul_sqTail 3 a b
  rw [GNExcessActiveProfileMass_target_eq_log_sqTail Nat.prime_three hb haX hc]
  change (R:ℝ) * Real.exp ((3/8:ℝ) * Real.log (C:ℝ)) ≤ _
  rw [hrep, Real.rpow_def_of_pos (mul_pos hAp hCp), Real.log_mul hAp.ne' hCp.ne']
  rw [← Real.exp_log hRp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end DkMath.ABC
