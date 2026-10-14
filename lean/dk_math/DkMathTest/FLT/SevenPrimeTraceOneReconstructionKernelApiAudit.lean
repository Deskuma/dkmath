import DkMath.FLT.Seven.PrimeTraceOneReconstructionKernelU16
import DkMath.FLT.Seven.SevenBaseTerminalDescentSeedExclusion

open DkMath.FLT.Seven

#check AwayCarrierReconstruction
#check awayCarrierReconstruction_iff_nonempty_descentClosureProvider
#check AwayCarrierReconstruction.carrier_pos
#check AwayCarrierReconstruction.one_le_carrier_depth
#check AwayCarrierReconstruction.seven_dvd_carrier
#check AwayValuationTransferPacket.root_snd_depth_eq_carrier_depth_sub_one
#check AwayValuationTransferPacket.no_reconstruction_at_depth_one
#check AwayValuationTransferPacket.no_descentClosureProvider_at_depth_one
#check AwayValuationTransferPacket.seven_dvd_root_snd_of_two_le_carrier_depth
#check RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstruction_iff_awayCarrierReconstruction
#check RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier_admissible
#check AwayDescentReconstructionSeed.two_le_pivotExponent
#check AwayDescentClosureProvider.two_le_pivotExponent

example {carrier : ℕ} (h : AwayCarrierReconstruction carrier) :
    0 < carrier ∧
      1 ≤ padicValNat 7 carrier ∧
      7 ∣ carrier := by
  exact ⟨h.carrier_pos, h.one_le_carrier_depth, h.seven_dvd_carrier⟩

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    AwayCarrierReconstruction (Int.natAbs p.normal.root.snd) ↔
      Nonempty (AwayDescentClosureProvider x y z p) :=
  awayCarrierReconstruction_iff_nonempty_descentClosureProvider p

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z)
    (hdepth : padicValNat 7 p.carrier = 1) :
    ¬ AwayCarrierReconstruction (Int.natAbs p.normal.root.snd) :=
  p.no_reconstruction_at_depth_one hdepth

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z)
    (hdepth : 2 ≤ padicValNat 7 p.carrier) :
    7 ∣ Int.natAbs p.normal.root.snd :=
  p.seven_dvd_root_snd_of_two_le_carrier_depth hdepth

example (p : RamifiedSignedRootRoutingPacket) :
    0 < RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier p ∧
      1 ≤ padicValNat 7
        (RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier p) ∧
      7 ∣ RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier p :=
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier_admissible p
