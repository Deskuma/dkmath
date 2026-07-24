/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimeAddress

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRootLoadAddress"

namespace DkMath.FLT.Seven

/-- The complete cubic root load on the right side of the fixed terminal routing
board. -/
def awaySevenBaseTerminalCubicRootLoad
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) : ℕ :=
  r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
    r.cubic.rootTriple.rightPart

/-- Every prime dividing the terminal cubic root load is non-seven and has one
globally unique endpoint row, routing cell, and cubic column address on the fixed
terminal board. -/
theorem AwaySevenBaseTerminalRoutingPacket.prime_dvd_cubicRootLoad_unique_global_address
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqLoad : q ∣ awaySevenBaseTerminalCubicRootLoad r) :
    q ≠ 7 ∧ AwaySevenBaseTerminalGlobalPrimeAddress packet q := by
  apply packet.prime_dvd_factorProduct_unique_global_address hq
  change q ∣ packet.core.carrier.carrierUnit *
    awaySevenBaseTerminalUnselectedEndpointNat p.row y z *
    awaySevenBaseTerminalCompanionEndpointNat p.row y z
  rw [packet.core.endpoint_carrier_root_load_normal_form.1]
  simpa [awaySevenBaseTerminalCubicRootLoad] using hqLoad

end DkMath.FLT.Seven
