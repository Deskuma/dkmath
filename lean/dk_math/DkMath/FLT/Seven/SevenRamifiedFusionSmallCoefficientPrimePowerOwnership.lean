/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve
import DkMath.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimePowerOwnership"

namespace DkMath.FLT.Seven

/-- A primitive eligible divisor owns only factors of the small coefficient.
The coefficient bound and strict coarse size rule exclude ownership of p by r. -/
theorem eligible_primitive_divisor_smallCoefficient_prime_pow
    {c p n r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3)
    (hmem : r ∈ (c * p ^ n).divisors)
    (hcop : Nat.Coprime r ((c * p ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < c * p ^ n) : r ∣ c := by
  have hdiv := Nat.dvd_of_mem_divisors hmem
  have hprod : r * ((c * p ^ n) / r) = c * p ^ n := Nat.mul_div_cancel' hdiv
  have hcpos : 0 < c := by
    by_contra h
    have hz : c = 0 := by omega
    simp [hz] at hsize
  by_cases hpdiv : p ∣ r
  · let t := (c * p ^ n) / r
    have htp : ¬ p ∣ t := hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hpdiv)
    have htdiv : t ∣ c * p ^ n := ⟨r, hprod.symm.trans (Nat.mul_comm r t)⟩
    have htc : t ∣ c :=
      ((hp.coprime_iff_not_dvd.mpr htp).symm.pow_right n).dvd_mul_right.mp htdiv
    have ht : t ≤ 7 ^ 3 := (Nat.le_of_dvd hcpos htc).trans hc
    have hM : c * p ^ n ≤ 7 ^ 3 * r ^ 7 := by
      calc
        c * p ^ n = r * t := hprod.symm
        _ ≤ r * 7 ^ 3 := Nat.mul_le_mul_left r ht
        _ = 7 ^ 3 * r := Nat.mul_comm _ _
        _ ≤ 7 ^ 3 * r ^ 7 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) r)
    omega
  · exact ((hp.coprime_iff_not_dvd.mpr hpdiv).symm.pow_right n).dvd_mul_right.mp hdiv

/-- Every exact eligible allocation of this core is excluded for positive exponents. -/
theorem sixthPowerSieved_three_thirteen_pow_excluded {n : ℕ} (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (3 * 13 ^ n) := by
  rintro ⟨r, hmem, hcop, hsize, _, _, hbranch⟩
  have hexact : NestedGNAllocationCondition (3 * 13 ^ n) r ∨
      NestedRHSAllocationCondition (3 * 13 ^ n) r :=
    hbranch.elim (fun h => .inl h.2) (fun h => .inr h.2.2)
  have hr3 := eligible_primitive_divisor_smallCoefficient_prime_pow
    (by decide : Nat.Prime 13) (by decide : 3 ≤ 7 ^ 3) hmem hcop hsize
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hr3 with hr | hr
  · subst r
    have hbad : ¬ Nat.ModEq 42 ((3 * 13 ^ n) / 1) 1 := by
      intro h
      have h3 := h.of_dvd (by decide : 3 ∣ 42)
      simp [Nat.ModEq] at h3
    exact nestedAllocation_excluded_of_mod_fortyTwo
      (Nat.dvd_of_mem_divisors hmem) hbad hexact
  · subst r
    apply nestedAllocation_excluded_of_thirteen_support (by decide) _ hexact
    rw [Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
    exact dvd_pow (dvd_refl 13) (by omega : n ≠ 0)

/-- The positive-exponent family consists of distinct abstract core values. -/
theorem threeThirteenPowerCore_injective :
    Function.Injective (fun k : ℕ => 3 * 13 ^ (k + 1)) := by
  intro a b h
  have he := Nat.pow_right_injective (by decide : 2 ≤ 13)
    (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) h)
  omega
/-- Every index in the distinct positive-exponent family fails the full sieve. -/
theorem sixthPowerSieved_three_thirteen_power_family_excluded (k : ℕ) :
    ¬ SixthPowerSievedNestedCondition (3 * 13 ^ (k + 1)) :=
  sixthPowerSieved_three_thirteen_pow_excluded (Nat.succ_pos k)

end DkMath.FLT.Seven
