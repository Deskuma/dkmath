/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPacket

#print "file: DkMath.FLT.Seven.SevenBaseTerminalWeightedBridge"

namespace DkMath.FLT.Seven

/-- In the positive unit sector, the `Y` endpoint quotient and cubic load
collapse to a single weighted terminal identity. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.positive_sector_endpoint_load_bridge
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (hpos : packet.unitSector.rootLinearUnit *
      (packet.unitSector.endpointUnit ^ 3)⁻¹ = 1) :
    (z : ℤ) * (cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3) =
      7 * ((z : ℤ) - (y : ℤ)) *
        ((r.cubic.rootTriple.vPart : ℤ) *
          (r.cubic.rootTriple.leftPart : ℤ) *
          (r.cubic.rootTriple.rightPart : ℤ)) := by
  have hrow :=
    packet.unitSector.normalized_rootLinearUnit_eq_one_iff_row_y.mp hpos
  have hend := packet.core.endpoint_quotient_eq
  have hloadNat := packet.core.load_quotient_eq
  simp only [AwaySevenBaseEndpointQuotientEquation, hrow] at hend
  simp only [awaySevenBaseLoadQuotientValue, hrow] at hloadNat
  have hload := congrArg (fun n : ℕ => (n : ℤ)) hloadNat
  push_cast at hload
  rw [hend, ← hload]
  ring

end DkMath.FLT.Seven
