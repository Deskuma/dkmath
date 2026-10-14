import DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedProvenance

open DkMath.FLT.Seven

#check PrimitiveCounterexampleRamifiedProvenance
#check nonempty_primitiveCounterexampleRamifiedProvenance
#check PrimitiveCounterexampleRamifiedProvenance.summit
#check PrimitiveCounterexampleRamifiedProvenance.distinguishedEndpoint
#check PrimitiveCounterexampleRamifiedProvenance.gap_residual_coprime
#check PrimitiveCounterexampleRamifiedProvenance.toResolution
#check PrimitiveCounterexampleRamifiedProvenance.toResolution_summit
#check PrimitiveCounterexampleRamifiedProvenance.endpointLeft_not_seven_dvd
#check PrimitiveCounterexampleRamifiedProvenance.endpointRight_not_seven_dvd
#check PrimitiveCounterexampleRamifiedProvenance.endpointSum_not_seven_dvd
#check PrimitiveCounterexampleRamifiedProvenance.CounterexampleOriginTerminalizable
#check PrimitiveCounterexampleRamifiedProvenance.terminalizable_iff_gapRoot_not_seven_dvd
#check PrimitiveCounterexampleRamifiedProvenance.terminalizable_iff_endpoint_depth_eq_one
#check PrimitiveCounterexampleRamifiedProvenance.endpoint_depth_eq_one_or_two_le
#check PrimitiveCounterexampleRamifiedProvenance.seven_dvd_gapRoot_of_two_le_endpoint_depth
#check PrimitiveCounterexampleRamifiedProvenance.not_terminalizable_of_two_le_endpoint_depth
#check PrimitiveCounterexampleRamifiedProvenance.nonempty_secondCoordinateRouting_of_endpoint_depth_eq_one

example {x y z : ℕ} (source : CounterexamplePack x y z) :
    Nonempty (PrimitiveCounterexampleRamifiedProvenance source) :=
  nonempty_primitiveCounterexampleRamifiedProvenance source

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    PrimitiveCounterexampleRamifiedResolution source :=
  r.toResolution

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    r.CounterexampleOriginTerminalizable ↔
      padicValNat 7 r.distinguishedEndpoint = 1 :=
  r.terminalizable_iff_endpoint_depth_eq_one
