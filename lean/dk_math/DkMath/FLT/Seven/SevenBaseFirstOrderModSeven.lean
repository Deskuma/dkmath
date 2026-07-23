/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseLayerQuotient

#print "file: DkMath.FLT.Seven.SevenBaseFirstOrderModSeven"

namespace DkMath.FLT.Seven

/-- The row-sensitive first-order terminal equation after exact integer
extraction of the single visible factor seven and reduction modulo seven. -/
def AwaySevenBaseFirstOrderEquationModSeven
    (row : EndpointRoutingRow) (u v : ℤ) (y z : ℕ) : Prop :=
  (awaySevenBaseFirstOrderCore row u v y z : ZMod 7) = 0

/-- Every exact terminal carrier quotient satisfies the corresponding
first-order equation modulo seven.  The row remains part of the proposition,
so the `Y`, `Z`, and `Sum` sectors are not merged. -/
theorem AwaySevenBaseCarrierQuotient.first_order_eq_mod_seven {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (q : AwaySevenBaseCarrierQuotient p) :
    AwaySevenBaseFirstOrderEquationModSeven p.row
      r.cubic.rootTriple.normal.root.fst
      r.cubic.rootTriple.normal.root.snd y z := by
  unfold AwaySevenBaseFirstOrderEquationModSeven
  rw [q.first_order_core_eq]
  apply intCast_zero_of_dvd
  exact ⟨_, rfl⟩

end DkMath.FLT.Seven
