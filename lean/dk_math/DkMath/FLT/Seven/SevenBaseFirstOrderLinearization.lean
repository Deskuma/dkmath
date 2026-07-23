/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseFirstOrderModSeven

#print "file: DkMath.FLT.Seven.SevenBaseFirstOrderLinearization"

namespace DkMath.FLT.Seven

/-- The Frobenius-linearized form of the terminal first-order equation over
`ZMod 7`.  The selected endpoint row remains explicit. -/
def AwaySevenBaseLinearEquationModSeven
    (row : EndpointRoutingRow) (u v : ℤ) (y z : ℕ) : Prop :=
  match row with
  | .y =>
      (u : ZMod 7) + 4 * (v : ZMod 7) = (z : ZMod 7) ^ 3
  | .z | .sum =>
      (u : ZMod 7) + 4 * (v : ZMod 7) = -((y : ZMod 7) ^ 3)

/-- Over the prime field with seven elements, the seventh powers in the exact
first-order quotient system collapse to first powers. -/
theorem AwaySevenBaseCarrierQuotient.linearized_first_order_eq_mod_seven
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    {p : AwaySevenPivotDepthPacket r} (q : AwaySevenBaseCarrierQuotient p) :
    AwaySevenBaseLinearEquationModSeven p.row
      r.cubic.rootTriple.normal.root.fst
      r.cubic.rootTriple.normal.root.snd y z := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := q.first_order_eq_mod_seven
  cases hrow : p.row <;>
    simp only [AwaySevenBaseFirstOrderEquationModSeven,
      awaySevenBaseFirstOrderCore, hrow,
      AwaySevenBaseLinearEquationModSeven] at h ⊢ <;>
    push_cast at h <;>
    simp [ZMod.pow_card] at h <;>
    linear_combination h

end DkMath.FLT.Seven
