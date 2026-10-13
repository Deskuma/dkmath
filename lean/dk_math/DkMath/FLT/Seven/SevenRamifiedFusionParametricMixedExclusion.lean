/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage
import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve
import DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionParametricMixedExclusion"

namespace DkMath.FLT.Seven

/-- Pure residue and size hypotheses suffice for mixed all-divisor exclusion. -/
theorem sixthPowerSieved_two_times_complement_excluded {s : ℕ}
    (hs42 : Nat.ModEq 42 s 1) (hs5 : Nat.ModEq 5 s 4)
    (hbound : 2 * s < 7 ^ 3 * 5 ^ 7) :
    ¬ SixthPowerSievedNestedCondition (2 * s) := by
  rintro ⟨r, hmem, _, hsize, _, _, hbranch⟩
  have hr := Nat.pos_of_mem_divisors hmem
  have hdiv := Nat.dvd_of_mem_divisors hmem
  have hs2 := hs42.of_dvd (by decide : 2 ∣ 42)
  have hs3 := hs42.of_dvd (by decide : 3 ∣ 42)
  have hn3 : ¬ 3 ∣ 2 * s := by
    intro h
    have hz := Nat.modEq_zero_iff_dvd.mpr h
    unfold Nat.ModEq at hs3 hz
    omega
  have hn4 : ¬ 4 ∣ 2 * s := by
    intro h
    rcases h with ⟨k, hk⟩
    have he : s = 2 * k := by omega
    unfold Nat.ModEq at hs2
    omega
  have hlt : r < 5 := by
    by_contra h
    have hp := Nat.pow_le_pow_left (by omega : 5 ≤ r) 7
    norm_num at hp hsize hbound
    omega
  have h12 : r = 1 ∨ r = 2 := by
    interval_cases r
    · simp
    · simp
    · exact False.elim (hn3 hdiv)
    · exact False.elim (hn4 hdiv)
  have hexact : NestedGNAllocationCondition (2 * s) r ∨
      NestedRHSAllocationCondition (2 * s) r :=
    hbranch.elim (fun h => .inl h.2) (fun h => .inr h.2.2)
  rcases h12 with h | h
  · subst r
    have hbad : ¬ Nat.ModEq 42 ((2 * s) / 1) 1 := by
      have ht := hs42.mul_left 2
      intro h
      rw [Nat.div_one] at h
      have hc := ht.symm.trans h
      norm_num [Nat.ModEq] at hc
    exact nestedAllocation_excluded_of_mod_fortyTwo (Nat.dvd_of_mem_divisors hmem) hbad hexact
  · subst r
    apply nestedAllocation_excluded_of_mod_five_square (by decide) _ hexact
    simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), show (2 : ℕ)^2 = 4 by decide] using hs5

/-- The mixed arithmetic obstruction covers every index in this finite window. -/
theorem sixthPowerSieved_bounded_mixed_family_excluded {k : ℕ} (hk : k ≤ 63799) :
    ¬ SixthPowerSievedNestedCondition (2 * (589 + 210 * k)) := by
  apply sixthPowerSieved_two_times_complement_excluded
  · unfold Nat.ModEq
    omega
  · unfold Nat.ModEq
    omega
  · norm_num
    omega

end DkMath.FLT.Seven
