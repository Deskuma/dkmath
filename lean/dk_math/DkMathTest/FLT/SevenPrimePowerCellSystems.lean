import DkMath.FLT.Seven

open DkMath.FLT.Seven

example {q e a : ℕ} (hq : Nat.Prime q) (he : 0 < e) (ha : ¬ q ∣ a) :
    IsUnit (a : ZMod (q ^ e)) :=
  isUnit_zmod_primePower_of_not_dvd hq he ha

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    p.modulus ∣ routingCell r.routing p.row p.column := p.modulus_dvd_cell

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    AwayRoutingPrimePowerSolution p.modulus p.row p.column :=
  p.toPrimePowerSolution

#print axioms isUnit_zmod_primePower_of_not_dvd
#print axioms AwayNonSevenPrimeDepthPacket.modulus_dvd_cell
#print axioms AwayNonSevenPrimeDepthPacket.toPrimePowerSolution
