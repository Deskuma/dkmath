/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalFixedRouting

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimeAddress"

namespace DkMath.FLT.Seven

/-- The three endpoint-side factor rows of the fixed terminal routing board. -/
inductive AwaySevenBaseTerminalFactorRow : Type
  | carrier
  | unselected
  | companion
  deriving DecidableEq, Repr

/-- The endpoint-side factor represented by a fixed terminal routing row. -/
def awaySevenBaseTerminalFactorRowValue
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow) : ℕ :=
  match row with
  | .carrier => packet.core.carrier.carrierUnit
  | .unselected => awaySevenBaseTerminalUnselectedEndpointNat p.row y z
  | .companion => awaySevenBaseTerminalCompanionEndpointNat p.row y z

/-- A prime address on one fixed terminal routing board.  The source factor row
is explicit, while the disjunction records its unique cell inside that row and
the corresponding cubic root-load column. -/
def AwaySevenBaseTerminalFixedPrimeAddress
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow) (q : ℕ) : Prop :=
  match row with
  | .carrier =>
      (q ∣ packet.routing.c11 ∧ ¬ q ∣ packet.routing.c12 ∧
          ¬ q ∣ packet.routing.c13 ∧ q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ packet.routing.c12 ∧ ¬ q ∣ packet.routing.c11 ∧
          ¬ q ∣ packet.routing.c13 ∧ q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ packet.routing.c13 ∧ ¬ q ∣ packet.routing.c11 ∧
          ¬ q ∣ packet.routing.c12 ∧ q ∣ r.cubic.rootTriple.rightPart)
  | .unselected =>
      (q ∣ packet.routing.c21 ∧ ¬ q ∣ packet.routing.c22 ∧
          ¬ q ∣ packet.routing.c23 ∧ q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ packet.routing.c22 ∧ ¬ q ∣ packet.routing.c21 ∧
          ¬ q ∣ packet.routing.c23 ∧ q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ packet.routing.c23 ∧ ¬ q ∣ packet.routing.c21 ∧
          ¬ q ∣ packet.routing.c22 ∧ q ∣ r.cubic.rootTriple.rightPart)
  | .companion =>
      (q ∣ packet.routing.c31 ∧ ¬ q ∣ packet.routing.c32 ∧
          ¬ q ∣ packet.routing.c33 ∧ q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ packet.routing.c32 ∧ ¬ q ∣ packet.routing.c31 ∧
          ¬ q ∣ packet.routing.c33 ∧ q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ packet.routing.c33 ∧ ¬ q ∣ packet.routing.c31 ∧
          ¬ q ∣ packet.routing.c32 ∧ q ∣ r.cubic.rootTriple.rightPart)

/-- Every prime carried by an explicitly selected endpoint-side factor row is
non-seven and has a unique cell address on the same fixed terminal board. -/
theorem AwaySevenBaseTerminalRoutingPacket.prime_dvd_factor_row_unique_address
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow)
    {q : ℕ} (hq : Nat.Prime q)
    (hqRow : q ∣ awaySevenBaseTerminalFactorRowValue packet row) :
    q ≠ 7 ∧ AwaySevenBaseTerminalFixedPrimeAddress packet row q := by
  cases row with
  | carrier =>
      simpa [awaySevenBaseTerminalFactorRowValue,
        AwaySevenBaseTerminalFixedPrimeAddress] using
        packet.prime_dvd_carrierUnit_unique_cell hq hqRow
  | unselected =>
      simpa [awaySevenBaseTerminalFactorRowValue,
        AwaySevenBaseTerminalFixedPrimeAddress] using
        packet.prime_dvd_unselected_endpoint_unique_cell hq hqRow
  | companion =>
      simpa [awaySevenBaseTerminalFactorRowValue,
        AwaySevenBaseTerminalFixedPrimeAddress] using
        packet.prime_dvd_companion_endpoint_unique_cell hq hqRow

end DkMath.FLT.Seven
