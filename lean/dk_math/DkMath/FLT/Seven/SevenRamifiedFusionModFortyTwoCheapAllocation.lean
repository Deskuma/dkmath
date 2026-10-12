/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve
import DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation"

/-! Arithmetic allocation candidates before choosing endpoints. The definitions
contain neither exact receiver predicates nor residual equalities. -/

namespace DkMath.FLT.Seven

/-- An endpoint-free necessary filter on a fixed allocation divisor.
The sixth-power existence sieve is deliberately a separate condition. -/
def ModFortyTwoCheapAllocation (M r : ℕ) : Prop :=
  r ∈ M.divisors ∧ Nat.Coprime r (M / r) ∧ 7 ^ 3 * r ^ 7 < M ∧
    Nat.ModEq 42 (M / r) 1 ∧
    (7 ^ 161 * r ^ 343 < M ^ 49 ∨
      (M ^ 49 < 7 ^ 161 * r ^ 343 ∧ 7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49))

/-- Some divisor passes the arithmetic filter; no endpoint witness is asserted. -/
def HasModFortyTwoCheapAllocation (M : ℕ) : Prop :=
  ∃ r : ℕ, ModFortyTwoCheapAllocation M r

/-- Forget exact receiver data after transporting its necessary modulo-42 residue. -/
theorem sixthPowerSieved_implies_mod42Cheap (M : ℕ)
    (h : SixthPowerSievedNestedCondition M) : HasModFortyTwoCheapAllocation M := by
  rcases h with ⟨r, hmem, hcop, hsize, _, _, hbranch⟩
  have hexact : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r :=
    hbranch.elim (fun h => .inl h.2) (fun h => .inr h.2.2)
  refine ⟨r, hmem, hcop, hsize,
    nestedAllocation_mod_fortyTwo (Nat.dvd_of_mem_divisors hmem) hexact, ?_⟩
  exact hbranch.elim (fun h => .inl h.1) (fun h => .inr ⟨h.1, h.2.1⟩)

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- An actual reconstruction must pass the independent arithmetic prefilter. -/
theorem internalDepthFourReconstruction_implies_mod42Cheap
    (p : RamifiedSignedRootRoutingPacket)
    (h : InternalDepthFourCounterexampleReconstructionObligation p) :
    HasModFortyTwoCheapAllocation (internalDepthFourSeventhCore p) :=
  sixthPowerSieved_implies_mod42Cheap _
    ((internalDepthFourReconstruction_iff_sixth_power_sieved p).mp h)

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
