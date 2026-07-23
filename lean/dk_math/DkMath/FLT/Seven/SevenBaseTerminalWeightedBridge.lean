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

/-- Every terminal packet satisfies exactly one of the positive and negative
weighted endpoint/load identities selected by its normalized unit sign. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.endpoint_load_bridge_dichotomy
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    (packet.unitSector.rootLinearUnit *
        (packet.unitSector.endpointUnit ^ 3)⁻¹ = 1 ∧
      (z : ℤ) * (cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3) =
        7 * ((z : ℤ) - (y : ℤ)) *
          ((r.cubic.rootTriple.vPart : ℤ) *
            (r.cubic.rootTriple.leftPart : ℤ) *
            (r.cubic.rootTriple.rightPart : ℤ))) ∨
    (packet.unitSector.rootLinearUnit *
        (packet.unitSector.endpointUnit ^ 3)⁻¹ = -1 ∧
      (y : ℤ) * (cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3) =
        7 * (z : ℤ) *
          ((r.cubic.rootTriple.vPart : ℤ) *
            (r.cubic.rootTriple.leftPart : ℤ) *
            (r.cubic.rootTriple.rightPart : ℤ))) := by
  rcases packet.unitSector.normalized_rootLinearUnit_eq_one_or_eq_neg_one with
    hpos | hneg
  · exact Or.inl ⟨hpos, packet.positive_sector_endpoint_load_bridge hpos⟩
  · exact Or.inr ⟨hneg, packet.negative_sector_endpoint_load_bridge hneg⟩

/-- After reduction modulo seven, the selected endpoint unit cancels from the
weighted bridge, leaving the bare cyclotomic residual equal to zero. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.residual_mod_seven_dichotomy
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    (packet.unitSector.rootLinearUnit *
        (packet.unitSector.endpointUnit ^ 3)⁻¹ = 1 ∧
      ((cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3 : ℤ) : ZMod 7) = 0) ∨
    (packet.unitSector.rootLinearUnit *
        (packet.unitSector.endpointUnit ^ 3)⁻¹ = -1 ∧
      ((cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 : ℤ) : ZMod 7) = 0) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rcases packet.endpoint_load_bridge_dichotomy with hpos | hneg
  · left
    refine ⟨hpos.1, ?_⟩
    have hrow :=
      packet.unitSector.normalized_rootLinearUnit_eq_one_iff_row_y.mp hpos.1
    have hz : (z : ZMod 7) ≠ 0 := by
      have hne := packet.core.carrier.endpoint_ne_zero_mod_seven
      simpa [AwaySevenBaseEndpointNonzeroModSeven, hrow] using hne
    have hcast := congrArg (fun n : ℤ => (n : ZMod 7)) hpos.2
    push_cast at hcast
    rw [show (7 : ZMod 7) = 0 by decide] at hcast
    simp only [zero_mul] at hcast
    have hzero := (mul_eq_zero.mp hcast).resolve_left hz
    simpa using hzero
  · right
    refine ⟨hneg.1, ?_⟩
    have hrows :=
      packet.unitSector.normalized_rootLinearUnit_eq_neg_one_iff_row_z_or_sum.mp hneg.1
    have hy : (y : ZMod 7) ≠ 0 := by
      have hne := packet.core.carrier.endpoint_ne_zero_mod_seven
      rcases hrows with hrow | hrow
      · simpa [AwaySevenBaseEndpointNonzeroModSeven, hrow] using hne
      · simpa [AwaySevenBaseEndpointNonzeroModSeven, hrow] using hne
    have hcast := congrArg (fun n : ℤ => (n : ZMod 7)) hneg.2
    push_cast at hcast
    rw [show (7 : ZMod 7) = 0 by decide] at hcast
    simp only [zero_mul] at hcast
    have hzero := (mul_eq_zero.mp hcast).resolve_left hy
    simpa using hzero

/-- The unit-sector proof is eliminated from the public arithmetic surface:
each terminal row directly carries its corresponding bare residual equation
modulo seven. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.row_resolved_residual_mod_seven_normal_form
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    (p.row = .y ∧
      ((cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3 : ℤ) : ZMod 7) = 0) ∨
    (p.row = .z ∧
      ((cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 : ℤ) : ZMod 7) = 0) ∨
    (p.row = .sum ∧
      ((cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 : ℤ) : ZMod 7) = 0) := by
  rcases packet.residual_mod_seven_dichotomy with hpos | hneg
  · left
    exact ⟨
      packet.unitSector.normalized_rootLinearUnit_eq_one_iff_row_y.mp hpos.1,
      hpos.2⟩
  · have hrows :=
      packet.unitSector.normalized_rootLinearUnit_eq_neg_one_iff_row_z_or_sum.mp hneg.1
    rcases hrows with hrow | hrow
    · exact Or.inr (Or.inl ⟨hrow, hneg.2⟩)
    · exact Or.inr (Or.inr ⟨hrow, hneg.2⟩)

/-- The row-sensitive bare cyclotomic residual at the terminal seven-primary
layer.  The `Z` and `Sum` rows share the same negative-sector residual. -/
def awaySevenBaseTerminalResidualModSeven
    (row : EndpointRoutingRow) (y z : ℕ) : ZMod 7 :=
  match row with
  | .y =>
      ((cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3 : ℤ) : ZMod 7)
  | .z | .sum =>
      ((cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 : ℤ) : ZMod 7)

/-- Every terminal packet annihilates its row-selected bare residual modulo
seven. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.terminal_residual_eq_zero_mod_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    awaySevenBaseTerminalResidualModSeven p.row y z = 0 := by
  rcases packet.row_resolved_residual_mod_seven_normal_form with hy | hz | hs
  · simpa [awaySevenBaseTerminalResidualModSeven, hy.1] using hy.2
  · simpa [awaySevenBaseTerminalResidualModSeven, hz.1] using hz.2
  · simpa [awaySevenBaseTerminalResidualModSeven, hs.1] using hs.2

end DkMath.FLT.Seven