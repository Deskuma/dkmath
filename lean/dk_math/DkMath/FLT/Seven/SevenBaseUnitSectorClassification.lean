/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseFirstOrderLinearization

#print "file: DkMath.FLT.Seven.SevenBaseUnitSectorClassification"

namespace DkMath.FLT.Seven

/-- The positive row sign occurs exactly in the `Y` sector. -/
theorem awaySevenBaseRowSignUnit_eq_one_iff (row : EndpointRoutingRow) :
    awaySevenBaseRowSignUnit row = 1 ↔ row = .y := by
  have hneg : (-1 : (ZMod 7)ˣ) ≠ 1 := by
    intro h
    have hval : (-1 : ZMod 7) = 1 :=
      congrArg (fun u : (ZMod 7)ˣ => (u : ZMod 7)) h
    norm_num at hval
  cases row <;> simp [awaySevenBaseRowSignUnit, hneg]

/-- The normalized terminal unit equals one exactly in the `Y` row. -/
theorem AwaySevenBaseUnitEquationPacket.normalized_rootLinearUnit_eq_one_iff_row_y
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    {p : AwaySevenPivotDepthPacket r} (packet : AwaySevenBaseUnitEquationPacket p) :
    packet.rootLinearUnit * (packet.endpointUnit ^ 3)⁻¹ = 1 ↔ p.row = .y := by
  rw [packet.normalized_rootLinearUnit_eq_rowSign]
  exact awaySevenBaseRowSignUnit_eq_one_iff p.row

end DkMath.FLT.Seven
