/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredGnomonGap

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCenteredImage589"

/-! An exact adjacent-value certificate for core 589. No literal sixth-power
assumption or identification with source-root coordinates is used. -/

namespace DkMath.FLT.Seven

/-- Both strict integer comparisons are proved by kernel reduction. -/
theorem centeredSevenSextic_589_bracket :
    centeredSevenSextic (7 ^ 27) 52382010648825907313680 < 448 * 589 ^ 49 ∧
    448 * 589 ^ 49 < centeredSevenSextic (7 ^ 27) (52382010648825907313680 + 1) := by
  decide

/-- No natural center realizes the target strictly between adjacent image values. -/
theorem centeredSevenSextic_589_no_image :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27) q = 448 * 589 ^ 49 :=
  centeredSevenSextic_no_image_of_adjacent_bracket
    centeredSevenSextic_589_bracket.1 centeredSevenSextic_589_bracket.2

/-- The existing exact receiver equivalence transports the no-image certificate. -/
theorem nestedAllocation_589_one_excluded :
    ¬ (NestedGNAllocationCondition 589 1 ∨ NestedRHSAllocationCondition 589 1) := by
  intro h
  rcases (nestedAllocation_iff_centered 589 1).mp h with ⟨q, hq⟩
  apply centeredSevenSextic_589_no_image
  refine ⟨q, ?_⟩
  simpa only [one_pow, mul_one, Nat.div_one, ← mul_assoc, show (64 : ℕ) * 7 = 448 by decide] using hq.2.1

/-- Every eligible divisor is one, where the exact receiver is excluded. -/
theorem sixthPowerSievedNestedCondition_589_excluded : ¬ SixthPowerSievedNestedCondition 589 := by
  rintro ⟨r, hmem, _, hsize, _, _, hbranch⟩
  have hpos := Nat.pos_of_mem_divisors hmem
  have hlt : r < 2 := by
    by_contra h
    have hp := Nat.pow_le_pow_left (by omega : 2 ≤ r) 7
    norm_num at hp hsize
    omega
  have hr : r = 1 := by omega
  subst r
  apply nestedAllocation_589_one_excluded
  exact hbranch.elim (fun h => .inl h.2) (fun h => .inr h.2.2)

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- A supplied source with core 589 cannot satisfy the reconstruction obligation. -/
theorem no_reconstruction_of_core_eq_589 (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 589) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p := by
  intro h
  apply sixthPowerSievedNestedCondition_589_excluded
  simpa only [hcore] using (internalDepthFourReconstruction_iff_sixth_power_sieved p).mp h

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
