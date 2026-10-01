/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedResolution
import DkMath.FLT.Seven.PrimeTraceOneReconstructionRamifiedResolutionU16

#print "file: DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedResolutionU16"

namespace DkMath.FLT.Seven

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- Under the existing U1.6 reconstruction obligation, the recovered ramified
summit has the forced depth profile.  This is a conditional consequence, not
an inconsistency of arbitrary summit data. -/
theorem internalDepthFourPrescribedCarrierRamifiedSummit_depths
    (p : RamifiedSignedRootRoutingPacket)
    (h : InternalDepthFourCounterexampleReconstructionObligation p) :
    ∃ q : PrescribedCarrierRamifiedSummit (internalDepthFourCarrier p),
      padicValNat 7 q.summit.gapRoot = 3 ∧
        padicValNat 7 (Int.natAbs q.summit.root.snd) = 26 ∧
        7 ∣ q.summit.gapRoot := by
  rcases internalDepthFourPrescribedCarrierRamifiedSummit p h with ⟨q⟩
  refine ⟨q, ?_, ?_, ?_⟩
  · have hcarrier :
        padicValNat 7 (internalDepthFourCarrier p) = 4 :=
      padicValNat_internalDepthFourCarrier p
    have hdist :
        padicValNat 7 (Int.natAbs q.summit.distinguished) = 4 := by
      rw [q.distinguished_eq]
      simpa using hcarrier
    have hgap := q.summit.distinguished_padicValNat
    rw [hdist] at hgap
    omega
  · have hcarrier :
        padicValNat 7 (internalDepthFourCarrier p) = 4 :=
      padicValNat_internalDepthFourCarrier p
    have hdist :
        padicValNat 7 (Int.natAbs q.summit.distinguished) = 4 := by
      rw [q.distinguished_eq]
      simpa using hcarrier
    have hgap : padicValNat 7 q.summit.gapRoot = 3 := by
      have hgap' := q.summit.distinguished_padicValNat
      rw [hdist] at hgap'
      omega
    have hroot := q.summit.rootSnd_padicValNat
    rw [hgap] at hroot
    norm_num at hroot ⊢
    exact hroot
  · have hcarrier :
        padicValNat 7 (internalDepthFourCarrier p) = 4 :=
      padicValNat_internalDepthFourCarrier p
    have hdist :
        padicValNat 7 (Int.natAbs q.summit.distinguished) = 4 := by
      rw [q.distinguished_eq]
      simpa using hcarrier
    have hgap : padicValNat 7 q.summit.gapRoot = 3 := by
      have hgap' := q.summit.distinguished_padicValNat
      rw [hdist] at hgap'
      omega
    exact (@padicValNat_dvd_iff_le 7 inferInstance q.summit.gapRoot 1
      q.summit.gapRoot_pos.ne').mpr (by rw [hgap]; norm_num)

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
