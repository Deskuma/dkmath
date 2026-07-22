import DkMath.FLT.Seven
import DkMathTest.FLT.SevenSpecializedPrimeAddress

open DkMath.FLT.Seven

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    Nonempty (AwayNonSevenPrimePowerOrbitSource p p.column) :=
  primePowerOrbitSource_of_depthPacket p

example {x y z : ℕ} (h : CounterexamplePack x y z) :
    Nonempty (PrimePowerOrbitAuditResult x y z) :=
  primePowerOrbitAuditResult_of_pack h

/-- The permanent FLT7-015 generic diagonal counterexample remains available. -/
example : 2 ∣ routingCell genericAddressCounterexample .y .sevenV := by
  norm_num [routingCell, genericAddressCounterexample]

example : 2 ∣ routingCell genericAddressCounterexample .z .leftCubic := by
  norm_num [routingCell, genericAddressCounterexample]

#print axioms primePowerOrbitSource_of_depthPacket
#print axioms primePowerOrbitAuditResult_of_pack
