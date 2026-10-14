/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage
import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve
import DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion"

namespace DkMath.FLT.Seven

/-- Primitivity forces prime-power ownership to one side; size excludes ownership by r. -/
theorem eligible_primitive_divisor_two_thirteen_pow (n : ℕ) {r : ℕ}
    (hmem : r ∈ (2 * 13 ^ n).divisors)
    (hcop : Nat.Coprime r ((2 * 13 ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < 2 * 13 ^ n) : r = 1 ∨ r = 2 := by
  have hr := Nat.pos_of_mem_divisors hmem
  have hdiv := Nat.dvd_of_mem_divisors hmem
  have hprod : r * ((2 * 13 ^ n) / r) = 2 * 13 ^ n := Nat.mul_div_cancel' hdiv
  have hp : Nat.Prime 13 := by decide
  by_cases h13 : 13 ∣ r
  · let t := (2 * 13 ^ n) / r
    have ht13 : ¬ 13 ∣ t := hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left h13)
    have htdiv : t ∣ 2 * 13 ^ n := ⟨r, by simpa only [Nat.mul_comm] using hprod.symm⟩
    have ht2 : t ∣ 2 :=
      ((hp.coprime_iff_not_dvd.mpr ht13).symm.pow_right n).dvd_mul_right.mp htdiv
    have ht : t ≤ 2 := Nat.le_of_dvd (by decide) ht2
    have hM : 2 * 13 ^ n ≤ 2 * r := by
      rw [← hprod]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left r ht
    have hpow : r ≤ r ^ 7 := by
      exact Nat.le_self_pow (by decide : 7 ≠ 0) r
    norm_num at hsize
    omega
  · have hc : Nat.Coprime r (13 ^ n) :=
      (hp.coprime_iff_not_dvd.mpr h13).symm.pow_right n
    have hr2 : r ∣ 2 := hc.dvd_mul_right.mp hdiv
    exact (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hr2

/-- An unbounded prime-power family is excluded without a global size cutoff. -/
theorem sixthPowerSieved_thirteen_power_family_excluded (k : ℕ) :
    ¬ SixthPowerSievedNestedCondition (2 * 13 ^ (6 + 4 * k)) := by
  let n := 6 + 4 * k
  have h42 : Nat.ModEq 42 (13 ^ n) 1 := by
    have h := (show Nat.ModEq 42 (13 ^ 2) 1 by decide).pow (3 + 2 * k)
    simpa only [← pow_mul, one_pow, show 2 * (3 + 2*k) = n by dsimp [n]; omega] using h
  have h5 : Nat.ModEq 5 (13 ^ n) 4 := by
    have h := (show Nat.ModEq 5 (13 ^ 6) 4 by decide).mul
      ((show Nat.ModEq 5 (13 ^ 4) 1 by decide).pow k)
    simpa only [one_pow, mul_one, ← pow_mul, ← pow_add] using h
  rintro ⟨r, hmem, hcop, hsize, _, _, hbranch⟩
  have hexact : NestedGNAllocationCondition (2 * 13 ^ n) r ∨
      NestedRHSAllocationCondition (2 * 13 ^ n) r :=
    hbranch.elim (fun h => .inl h.2) (fun h => .inr h.2.2)
  rcases eligible_primitive_divisor_two_thirteen_pow n hmem hcop hsize with hr | hr
  · subst r
    have hbad : ¬ Nat.ModEq 42 ((2 * 13 ^ n) / 1) 1 := by
      intro h
      rw [Nat.div_one] at h
      have hc := (h42.mul_left 2).symm.trans h
      norm_num [Nat.ModEq] at hc
    exact nestedAllocation_excluded_of_mod_fortyTwo (Nat.dvd_of_mem_divisors hmem) hbad hexact
  · subst r
    apply nestedAllocation_excluded_of_mod_five_square (by decide) _ hexact
    simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), show (2 : ℕ)^2 = 4 by decide] using h5

end DkMath.FLT.Seven
