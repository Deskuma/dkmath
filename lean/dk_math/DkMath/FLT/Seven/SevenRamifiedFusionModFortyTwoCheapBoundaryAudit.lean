/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit"

/-! A globally rejected arithmetic core and an unbounded family of surviving
cheap candidates. Neither construction asserts an exact endpoint witness. -/

namespace DkMath.FLT.Seven

/-- Every divisor fails the arithmetic filter at the concrete core 554. -/
theorem no_mod42Cheap_at_554 : ¬ HasModFortyTwoCheapAllocation 554 := by
  rintro ⟨r, hr, _, hsize, hres, _⟩
  have hpos : 0 < r := Nat.pos_of_mem_divisors hr
  have hlt : r < 2 := by
    by_contra h
    have hp := Nat.pow_le_pow_left (by omega : 2 ≤ r) 7
    norm_num at hp hsize
    omega
  have hr1 : r = 1 := by omega
  subst r
  exact (by decide : ¬ Nat.ModEq 42 (554 / 1) 1) hres

/-- An arithmetic progression passes the GN-side cheap threshold for every index. -/
theorem mod42Cheap_family (k : ℕ) : ModFortyTwoCheapAllocation (631 + 42 * k) 1 := by
  refine ⟨Nat.one_mem_divisors.mpr (by omega), by simp, ?_, ?_, .inl ?_⟩
  · simp only [one_pow, mul_one]
    omega
  · rw [Nat.div_one]
    unfold Nat.ModEq
    omega
  · simp only [one_pow, mul_one]
    exact lt_of_lt_of_le (by decide : 7 ^ 161 < 631 ^ 49)
      (Nat.pow_le_pow_left (by omega : 631 ≤ 631 + 42 * k) 49)

/-- Each family member has a cheap divisor candidate, without an endpoint witness. -/
theorem mod42Cheap_family_has (k : ℕ) :
    HasModFortyTwoCheapAllocation (631 + 42 * k) := ⟨1, mod42Cheap_family k⟩

/-- The separate sixth-power condition is vacuous at the family's divisor one. -/
theorem mod42Cheap_family_sixthPower (k : ℕ) :
    SixthPowerAllocationSieve 1 ((631 + 42 * k) / 1) :=
  sixthPowerAllocationSieve_mod_one _

/-- Surviving cheap candidates with the separate sixth-power sieve exceed every bound. -/
theorem mod42Cheap_survivors_unbounded (B : ℕ) :
    ∃ k : ℕ, B < 631 + 42 * k ∧
      ModFortyTwoCheapAllocation (631 + 42 * k) 1 ∧
      SixthPowerAllocationSieve 1 ((631 + 42 * k) / 1) :=
  ⟨B, by omega, mod42Cheap_family B, mod42Cheap_family_sixthPower B⟩

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- Conditional source consumer: core 554 cannot support the reconstruction obligation. -/
theorem no_reconstruction_of_core_eq_554 (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 554) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p := by
  intro h
  apply no_mod42Cheap_at_554
  simpa only [hcore] using internalDepthFourReconstruction_implies_mod42Cheap p h

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
