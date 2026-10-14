/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneReconstructionKernel
import DkMath.FLT.Seven.SevenRamifiedFusionStrictDescentFailureBoundary

#print "file: DkMath.FLT.Seven.PrimeTraceOneReconstructionKernelU16"

namespace DkMath.FLT.Seven

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem internalDepthFourReconstruction_iff_awayCarrierReconstruction
    (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      AwayCarrierReconstruction (internalDepthFourCarrier p) := by
  constructor
  · rintro ⟨x, y, z, route, hcarrier⟩
    exact ⟨x, y, z, route, hcarrier⟩
  · rintro ⟨x, y, z, route, hcarrier⟩
    exact ⟨x, y, z, route, hcarrier⟩

theorem internalDepthFourCarrier_admissible
    (p : RamifiedSignedRootRoutingPacket) :
    0 < internalDepthFourCarrier p ∧
      1 ≤ padicValNat 7 (internalDepthFourCarrier p) ∧
      7 ∣ internalDepthFourCarrier p := by
  have hdepth := padicValNat_internalDepthFourCarrier p
  have hpos : 0 < internalDepthFourCarrier p := by
    by_contra hzero
    have hz : internalDepthFourCarrier p = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hz, padicValNat_zero_right] at hdepth
    omega
  have hone : 1 ≤ padicValNat 7 (internalDepthFourCarrier p) := by
    rw [hdepth]
    norm_num
  have hdvd : 7 ∣ internalDepthFourCarrier p := by
    exact (@padicValNat_dvd_iff_le 7 inferInstance
      (internalDepthFourCarrier p) 1 hpos.ne').mpr hone
  exact ⟨hpos, hone, hdvd⟩

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
