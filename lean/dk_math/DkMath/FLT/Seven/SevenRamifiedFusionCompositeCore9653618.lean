/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage
import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve
import DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCompositeCore9653618"

namespace DkMath.FLT.Seven

/-- Membership and the coarse bound exhaust the eligible divisors at this core. -/
theorem eligible_divisor_9653618_eq_one_or_two {r : ℕ}
    (hmem : r ∈ (9653618 : ℕ).divisors) (hsize : 7 ^ 3 * r ^ 7 < 9653618) :
    r = 1 ∨ r = 2 := by
  have hr := Nat.pos_of_mem_divisors hmem
  have hdiv := Nat.dvd_of_mem_divisors hmem
  have hlt : r < 5 := by
    by_contra h
    have hp := Nat.pow_le_pow_left (by omega : 5 ≤ r) 7
    norm_num at hp hsize
    omega
  interval_cases r <;> norm_num at hdiv <;> simp

/-- The same selected divisor is excluded by mod42 at one or mod5 at two. -/
theorem sixthPowerSievedNestedCondition_9653618_excluded :
    ¬ SixthPowerSievedNestedCondition 9653618 := by
  rintro ⟨r, hmem, _, hsize, _, _, hbranch⟩
  have hexact : NestedGNAllocationCondition 9653618 r ∨
      NestedRHSAllocationCondition 9653618 r :=
    hbranch.elim (fun h => .inl h.2) (fun h => .inr h.2.2)
  rcases eligible_divisor_9653618_eq_one_or_two hmem hsize with hr | hr
  · subst r
    exact nestedAllocation_excluded_of_mod_fortyTwo
      (Nat.dvd_of_mem_divisors hmem) (by decide) hexact
  · subst r
    exact nestedAllocation_excluded_of_mod_five_square (by decide) (by decide) hexact

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- Conditional reconstruction exclusion at the specified source core. -/
theorem no_reconstruction_of_core_eq_9653618 (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 9653618) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p := by
  intro h
  apply sixthPowerSievedNestedCondition_9653618_excluded
  simpa only [hcore] using (internalDepthFourReconstruction_iff_sixth_power_sieved p).mp h

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
