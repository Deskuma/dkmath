import DkMath.FLT.Seven.PrimeTraceOneReconstructionRamifiedResolutionU16

open DkMath.FLT.Seven

#check no_counterexample_of_seven_dvd_y_add_z
#check AwayCarrierFermatChart.sum_impossible
#check nonempty_ramified_of_seven_dvd_second
#check PrescribedCarrierAlternatingPowerSplit
#check nonempty_prescribedCarrierAlternatingPowerSplit
#check PrescribedCarrierSignedResidualCore
#check nonempty_prescribedCarrierSignedResidualCore
#check PrescribedCarrierSignedResidualCore.exists_residualCore_eq_seventh_power
#check PrescribedCarrierRamifiedSummit
#check nonempty_prescribedCarrierRamifiedSummit_of_right_chart
#check nonempty_prescribedCarrierRamifiedSummit_of_left_chart
#check nonempty_prescribedCarrierRamifiedSummit_of_fermatChart
#check nonempty_prescribedCarrierRamifiedSummit_of_awayCarrierReconstruction
#check RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourPrescribedCarrierRamifiedSummit

example {x y z : ℕ} (source : CounterexamplePack x y z)
    (hsum : 7 ∣ y + z) : False :=
  no_counterexample_of_seven_dvd_y_add_z source hsum

example {carrier : ℕ} (h : AwayCarrierFermatChart carrier) :
    Nonempty (PrescribedCarrierRamifiedSummit carrier) :=
  nonempty_prescribedCarrierRamifiedSummit_of_fermatChart h

example {carrier : ℕ} (h : AwayCarrierReconstruction carrier) :
    Nonempty (PrescribedCarrierRamifiedSummit carrier) :=
  nonempty_prescribedCarrierRamifiedSummit_of_awayCarrierReconstruction h
