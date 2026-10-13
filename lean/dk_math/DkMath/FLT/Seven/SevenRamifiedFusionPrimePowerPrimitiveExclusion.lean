/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage
import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve
import DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionPrimePowerPrimitiveExclusion"

namespace DkMath.FLT.Seven

/-- Primitivity forces prime-power ownership to one side; size excludes ownership by r. -/
theorem eligible_primitive_divisor_two_prime_pow {p n r : ℕ} (hp : Nat.Prime p)
    (hmem : r ∈ (2 * p ^ n).divisors)
    (hcop : Nat.Coprime r ((2 * p ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < 2 * p ^ n) : r = 1 ∨ r = 2 := by
  have hr := Nat.pos_of_mem_divisors hmem
  have hdiv := Nat.dvd_of_mem_divisors hmem
  have hprod : r * ((2 * p ^ n) / r) = 2 * p ^ n := Nat.mul_div_cancel' hdiv
  by_cases hpdiv : p ∣ r
  · let t := (2 * p ^ n) / r
    have htp : ¬ p ∣ t := hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hpdiv)
    have htdiv : t ∣ 2 * p ^ n := ⟨r, hprod.symm.trans (Nat.mul_comm r t)⟩
    have ht2 : t ∣ 2 :=
      ((hp.coprime_iff_not_dvd.mpr htp).symm.pow_right n).dvd_mul_right.mp htdiv
    have ht : t ≤ 2 := Nat.le_of_dvd (by decide) ht2
    have hM : 2 * p ^ n ≤ 2 * r := by
      calc
        2 * p ^ n = r * t := hprod.symm
        _ ≤ r * 2 := Nat.mul_le_mul_left r ht
        _ = 2 * r := Nat.mul_comm _ _
    have hpow : r ≤ r ^ 7 := by
      exact Nat.le_self_pow (by decide : 7 ≠ 0) r
    norm_num at hsize
    omega
  · have hc : Nat.Coprime r (p ^ n) :=
      (hp.coprime_iff_not_dvd.mpr hpdiv).symm.pow_right n
    have hr2 : r ∣ 2 := hc.dvd_mul_right.mp hdiv
    exact (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hr2

/-- Prime-power structural ownership and explicit residues exclude the exact sieve. -/
theorem sixthPowerSieved_two_prime_pow_excluded {p n : ℕ} (hp : Nat.Prime p)
    (h42 : Nat.ModEq 42 (p ^ n) 1) (h5 : Nat.ModEq 5 (p ^ n) 4) :
    ¬ SixthPowerSievedNestedCondition (2 * p ^ n) := by
  rintro ⟨r, hmem, hcop, hsize, _, _, hbranch⟩
  have hexact : NestedGNAllocationCondition (2 * p ^ n) r ∨
      NestedRHSAllocationCondition (2 * p ^ n) r :=
    hbranch.elim (fun h => .inl h.2) (fun h => .inr h.2.2)
  rcases eligible_primitive_divisor_two_prime_pow hp hmem hcop hsize with hr | hr
  · subst r
    have hbad : ¬ Nat.ModEq 42 ((2 * p ^ n) / 1) 1 := by
      intro h
      rw [Nat.div_one] at h
      have hc := (h42.mul_left 2).symm.trans h
      norm_num [Nat.ModEq] at hc
    exact nestedAllocation_excluded_of_mod_fortyTwo (Nat.dvd_of_mem_divisors hmem) hbad hexact
  · subst r
    apply nestedAllocation_excluded_of_mod_five_square (by decide) _ hexact
    simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), show (2 : ℕ)^2 = 4 by decide] using h5

end DkMath.FLT.Seven
