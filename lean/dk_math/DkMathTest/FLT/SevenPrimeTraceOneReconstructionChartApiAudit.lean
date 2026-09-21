import DkMath.FLT.Seven.PrimeTraceOneReconstructionChartU16

open DkMath.FLT.Seven

#check AwayCarrierFermatChart
#check awayCarrierReconstruction_to_fermatChart
#check fermatChart_to_awayCarrierReconstruction
#check awayCarrierReconstruction_iff_fermatChart
#check awayCarrierReconstruction_additive_decomposition
#check AwayCarrierFermatChart.left_bounds
#check AwayCarrierFermatChart.sum_bounds
#check AwayCarrierFermatChart.right_bounds
#check AwayValuationTransferPacket.no_fermatChart_at_depth_one
#check RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstruction_iff_fermatChart

example {carrier : ℕ} :
    AwayCarrierReconstruction carrier ↔ AwayCarrierFermatChart carrier :=
  awayCarrierReconstruction_iff_fermatChart

example {carrier : ℕ} (h : AwayCarrierReconstruction carrier) :
    (∃ x z, CounterexamplePack x carrier z) ∨
      (∃ x y, CounterexamplePack x y carrier) ∨
      (∃ x y z, CounterexamplePack x y z ∧ y + z = carrier) :=
  awayCarrierReconstruction_additive_decomposition h

example {x y carrier : ℕ} (pack : CounterexamplePack x y carrier) :
    x < carrier ∧ y < carrier :=
  AwayCarrierFermatChart.left_bounds pack

example {x y z carrier : ℕ} (pack : CounterexamplePack x y z)
    (hcarrier : y + z = carrier) :
    x < carrier ∧ y < carrier ∧ z < carrier :=
  AwayCarrierFermatChart.sum_bounds pack hcarrier

example {x carrier z : ℕ} (pack : CounterexamplePack x carrier z) :
    carrier < z ∧ x < z :=
  AwayCarrierFermatChart.right_bounds pack

example {x y z : ℕ} (p : AwayValuationTransferPacket x y z)
    (hdepth : padicValNat 7 p.carrier = 1) :
    ¬ AwayCarrierFermatChart (Int.natAbs p.normal.root.snd) :=
  p.no_fermatChart_at_depth_one hdepth

example (p : RamifiedSignedRootRoutingPacket) :
    RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.InternalDepthFourCounterexampleReconstructionObligation p ↔
      AwayCarrierFermatChart
        (RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier p) :=
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstruction_iff_fermatChart p
