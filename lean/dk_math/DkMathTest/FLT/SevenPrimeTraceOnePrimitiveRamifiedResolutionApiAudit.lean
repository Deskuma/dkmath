import DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedResolutionU16

open DkMath.FLT.Seven

#check PrimitiveSevenDivisibleEndpoint
#check primitiveSevenDivisibleEndpoint_of_counterexample
#check seven_dvd_some_endpoint_of_counterexample
#check seven_dvd_gap_of_seven_dvd_first
#check PrimitiveCounterexampleRamifiedResolution
#check PrimitiveCounterexampleRamifiedResolution.summit
#check PrimitiveCounterexampleRamifiedResolution.distinguishedEndpoint
#check PrimitiveCounterexampleRamifiedResolution.rootSnd_padicValNat_add_two_eq_seven_mul_endpoint_depth
#check nonempty_primitiveCounterexampleRamifiedResolution
#check nonempty_primitiveCounterexampleRamifiedSummit
#check PrimitiveRamifiedSummitPacket.distinguished_padicValNat
#check PrimitiveRamifiedSummitPacket.rootSnd_padicValNat_add_two_eq
#check RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourPrescribedCarrierRamifiedSummit_depths

example {x y z : ℕ} (source : CounterexamplePack x y z) :
    7 ∣ x ∨ 7 ∣ y ∨ 7 ∣ z :=
  seven_dvd_some_endpoint_of_counterexample source

example {x y z : ℕ} (source : CounterexamplePack x y z) :
    Nonempty (PrimitiveCounterexampleRamifiedResolution source) :=
  nonempty_primitiveCounterexampleRamifiedResolution source

example {x y z : ℕ} (source : CounterexamplePack x y z) :
    Nonempty PrimitiveRamifiedSummitPacket :=
  nonempty_primitiveCounterexampleRamifiedSummit source
