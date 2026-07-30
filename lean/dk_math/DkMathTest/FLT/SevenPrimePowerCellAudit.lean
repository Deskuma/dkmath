import DkMath.FLT.Seven

open DkMath.FLT.Seven

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    Nonempty (AwayNonSevenPrimePowerSolubilitySource p p.column) :=
  primePowerSolubilitySource_of_depthPacket p

example {x y z : ℕ} (h : CounterexamplePack x y z) :
    Nonempty (PrimePowerCellAuditResult x y z) :=
  primePowerCellAuditResult_of_pack h

#print axioms primePowerSolubilitySource_of_depthPacket
#print axioms primePowerCellAuditResult_of_pack
