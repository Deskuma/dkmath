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

/-- The row-selected endpoint cube appearing in the linearized base equation is
nonzero modulo seven.  This is the direct transport of the already proved
root-linear nonvanishing through the exact first-order linearization. -/
def AwaySevenBaseEndpointCubeNonzeroModSeven
    (row : EndpointRoutingRow) (y z : ℕ) : Prop :=
  match row with
  | .y => (z : ZMod 7) ^ 3 ≠ 0
  | .z | .sum => -((y : ZMod 7) ^ 3) ≠ 0

/-- The linearized first-order identity identifies the nonzero root-linear core
with the row-selected endpoint cube. -/
theorem AwaySevenBaseCarrierQuotient.endpoint_cube_ne_zero_mod_seven
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    {p : AwaySevenPivotDepthPacket r} (q : AwaySevenBaseCarrierQuotient p) :
    AwaySevenBaseEndpointCubeNonzeroModSeven p.row y z := by
  have hlinear := q.linearized_first_order_eq_mod_seven
  have hroot :
      ((r.cubic.rootTriple.normal.root.fst +
        4 * r.cubic.rootTriple.normal.root.snd : ℤ) : ZMod 7) ≠ 0 := by
    simpa [awayRootLinearModSeven] using
      r.cubic.rootTriple.normal.rootLinear_ne_zero
  push_cast at hroot
  cases hrow : p.row <;>
    simp only [AwaySevenBaseLinearEquationModSeven,
      AwaySevenBaseEndpointCubeNonzeroModSeven, hrow] at hlinear ⊢ <;>
    rw [← hlinear] <;>
    exact hroot

/-- The endpoint selected by the terminal row is itself nonzero modulo seven. -/
def AwaySevenBaseEndpointNonzeroModSeven
    (row : EndpointRoutingRow) (y z : ℕ) : Prop :=
  match row with
  | .y => (z : ZMod 7) ≠ 0
  | .z | .sum => (y : ZMod 7) ≠ 0

/-- Nonvanishing of the selected endpoint cube descends to nonvanishing of the
selected endpoint itself. -/
theorem AwaySevenBaseCarrierQuotient.endpoint_ne_zero_mod_seven
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    {p : AwaySevenPivotDepthPacket r} (q : AwaySevenBaseCarrierQuotient p) :
    AwaySevenBaseEndpointNonzeroModSeven p.row y z := by
  have hcube := q.endpoint_cube_ne_zero_mod_seven
  cases hrow : p.row <;>
    simp only [AwaySevenBaseEndpointCubeNonzeroModSeven,
      AwaySevenBaseEndpointNonzeroModSeven, hrow] at hcube ⊢ <;>
    intro hzero <;>
    apply hcube <;>
    simp [hzero]

/-- The endpoint selected by the terminal row is a unit modulo seven. -/
def AwaySevenBaseEndpointIsUnitModSeven
    (row : EndpointRoutingRow) (y z : ℕ) : Prop :=
  match row with
  | .y => IsUnit (z : ZMod 7)
  | .z | .sum => IsUnit (y : ZMod 7)

/-- Over the prime field `ZMod 7`, the selected endpoint nonvanishing is
exactly the corresponding unit statement. -/
theorem AwaySevenBaseCarrierQuotient.endpoint_isUnit_mod_seven
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    {p : AwaySevenPivotDepthPacket r} (q : AwaySevenBaseCarrierQuotient p) :
    AwaySevenBaseEndpointIsUnitModSeven p.row y z := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hne := q.endpoint_ne_zero_mod_seven
  cases hrow : p.row <;>
    simp only [AwaySevenBaseEndpointNonzeroModSeven,
      AwaySevenBaseEndpointIsUnitModSeven, hrow] at hne ⊢ <;>
    exact isUnit_iff_ne_zero.mpr hne

end DkMath.FLT.Seven
