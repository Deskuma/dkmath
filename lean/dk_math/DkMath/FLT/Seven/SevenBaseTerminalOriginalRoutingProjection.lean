/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimeCellCoordinate
import DkMath.FLT.Seven.SpecializedPrimeAddress

#print "file: DkMath.FLT.Seven.SevenBaseTerminalOriginalRoutingProjection"

set_option linter.style.longLine false

namespace DkMath.FLT.Seven

/-- The original endpoint row represented by one terminal factor row.  The
terminal rows are a pivot-sensitive permutation of `y`, `z`, and `y + z`. -/
def awaySevenBaseTerminalOriginalEndpointRow
    (pivot : EndpointRoutingRow)
    (row : AwaySevenBaseTerminalFactorRow) : EndpointRoutingRow :=
  match pivot with
  | .y =>
      match row with
      | .carrier => .y
      | .unselected => .z
      | .companion => .sum
  | .z =>
      match row with
      | .carrier => .z
      | .unselected => .y
      | .companion => .sum
  | .sum =>
      match row with
      | .carrier => .sum
      | .unselected => .y
      | .companion => .z

/-- The original cubic routing column represented by one terminal root-load
column.  The terminal `vPart` column sits inside the original `7 * vPart`
column. -/
def awaySevenBaseTerminalOriginalRootColumn :
    AwaySevenBaseTerminalRootColumn → RootRoutingColumn
  | .vPart => .sevenV
  | .leftPart => .leftCubic
  | .rightPart => .rightCubic

/-- A terminal prime-cell coordinate projects to divisibility of its original
endpoint routing factor.  In the carrier row this uses the exact identity
`selected endpoint = 7 * carrierUnit`; the other two rows are unchanged endpoint
factors. -/
theorem AwaySevenBaseTerminalRoutingPacket.primeCellCoordinate_dvd_originalEndpointFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) {q : ℕ}
    (hcoordinate : AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q) :
    q ∣ endpointRoutingFactorNat y z
      (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row) := by
  rcases coordinate with ⟨row, column⟩
  change q ∣ awaySevenBaseTerminalFactorRowValue packet row ∧
    AwaySevenBaseTerminalFixedPrimeCoordinate packet row column q at hcoordinate
  cases row with
  | carrier =>
      have hqEndpoint : q ∣ endpointRoutingFactorNat y z p.row := by
        rw [packet.core.carrier.carrier_eq]
        exact dvd_mul_of_dvd_right hcoordinate.1 7
      cases hrow : p.row <;>
        simpa [awaySevenBaseTerminalOriginalEndpointRow, hrow] using hqEndpoint
  | unselected =>
      cases hrow : p.row <;>
        simpa [awaySevenBaseTerminalOriginalEndpointRow,
          awaySevenBaseTerminalFactorRowValue,
          awaySevenBaseTerminalUnselectedEndpointNat,
          endpointRoutingFactorNat, hrow] using hcoordinate.1
  | companion =>
      cases hrow : p.row <;>
        simpa [awaySevenBaseTerminalOriginalEndpointRow,
          awaySevenBaseTerminalFactorRowValue,
          awaySevenBaseTerminalCompanionEndpointNat,
          endpointRoutingFactorNat, hrow] using hcoordinate.1

/-- A terminal prime-cell coordinate projects to divisibility of its original
root routing factor.  For the `vPart` column the prime divides `7 * vPart`; the
left and right cubic columns are unchanged. -/
theorem AwaySevenBaseTerminalRoutingPacket.primeCellCoordinate_dvd_originalRootFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) {q : ℕ}
    (hcoordinate : AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q) :
    q ∣ rootRoutingFactorNat r
      (awaySevenBaseTerminalOriginalRootColumn coordinate.column) := by
  rcases coordinate with ⟨row, column⟩
  change q ∣ awaySevenBaseTerminalFactorRowValue packet row ∧
    AwaySevenBaseTerminalFixedPrimeCoordinate packet row column q at hcoordinate
  cases row <;> cases column <;>
    simp only [AwaySevenBaseTerminalFixedPrimeCoordinate] at hcoordinate <;>
    simp only [awaySevenBaseTerminalOriginalRootColumn, rootRoutingFactorNat]
  · exact dvd_mul_of_dvd_right hcoordinate.2.2.2.2 7
  · exact hcoordinate.2.2.2.2
  · exact hcoordinate.2.2.2.2
  · exact dvd_mul_of_dvd_right hcoordinate.2.2.2.2 7
  · exact hcoordinate.2.2.2.2
  · exact hcoordinate.2.2.2.2
  · exact dvd_mul_of_dvd_right hcoordinate.2.2.2.2 7
  · exact hcoordinate.2.2.2.2
  · exact hcoordinate.2.2.2.2

/-- The minimal projection packet needed to re-enter the original specialized
prime-address layer.  It records the terminal coordinate together with the
corresponding original endpoint and root factor divisibilities. -/
structure AwaySevenBaseTerminalOriginalRoutingPrimeProjection
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) : Type where
  q : ℕ
  q_prime : Nat.Prime q
  q_ne_seven : q ≠ 7
  coordinate : AwaySevenBaseTerminalCellCoordinate
  prime_cell : AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q
  q_dvd_original_endpoint : q ∣ endpointRoutingFactorNat y z
    (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
  q_dvd_original_root : q ∣ rootRoutingFactorNat r
    (awaySevenBaseTerminalOriginalRootColumn coordinate.column)

/-- Every prime dividing the terminal cubic root load produces a projection into
one original endpoint row and one original cubic routing column. -/
theorem AwaySevenBaseTerminalRoutingPacket.nonempty_originalRoutingPrimeProjection_of_dvd_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqLoad : q ∣ awaySevenBaseTerminalCubicRootLoad r) :
    Nonempty (AwaySevenBaseTerminalOriginalRoutingPrimeProjection packet) := by
  have hglobal :=
    packet.prime_dvd_cubicRootLoad_unique_global_cellCoordinate hq hqLoad
  rcases hglobal.2 with ⟨coordinate, hcoordinate, _⟩
  exact ⟨{
    q := q
    q_prime := hq
    q_ne_seven := hglobal.1
    coordinate := coordinate
    prime_cell := hcoordinate
    q_dvd_original_endpoint :=
      packet.primeCellCoordinate_dvd_originalEndpointFactor coordinate hcoordinate
    q_dvd_original_root :=
      packet.primeCellCoordinate_dvd_originalRootFactor coordinate hcoordinate }⟩

end DkMath.FLT.Seven
