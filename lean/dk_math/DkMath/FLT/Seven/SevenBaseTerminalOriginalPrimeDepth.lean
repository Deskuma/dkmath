/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalOriginalPrimeAddress
import DkMath.FLT.Seven.PrimePowerCellSystems

#print "file: DkMath.FLT.Seven.SevenBaseTerminalOriginalPrimeDepth"

namespace DkMath.FLT.Seven

/-- A terminal prime coordinate lifted to the complete non-seven prime depth of
its corresponding cell in the original routing grid. -/
structure AwaySevenBaseTerminalOriginalPrimeDepthPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (q : ℕ) : Type where
  coordinate : AwaySevenBaseTerminalCellCoordinate
  prime_cell : AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q
  depth : AwayNonSevenPrimeDepthPacket r
  depth_q_eq : depth.q = q
  depth_row_eq : depth.row =
    awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row
  depth_column_eq : depth.column =
    awaySevenBaseTerminalOriginalRootColumn coordinate.column

/-- Lift one terminal prime coordinate to the exact prime-adic depth of the
corresponding original routing cell. -/
def AwaySevenBaseTerminalRoutingPacket.originalNonSevenPrimeDepthOfCoordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) {q : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7)
    (hcoordinate : AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q) :
    AwayNonSevenPrimeDepthPacket r where
  depth := (packet.originalPrimeAddressOfCoordinate coordinate hq hcoordinate).toDepthPacket
  q_ne_seven := by
    change q ≠ 7
    exact hq7

/-- Package the terminal coordinate together with its exact original routing
prime depth and the defining row/column projection equalities. -/
def AwaySevenBaseTerminalRoutingPacket.originalPrimeDepthPacketOfCoordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) {q : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7)
    (hcoordinate : AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q) :
    AwaySevenBaseTerminalOriginalPrimeDepthPacket packet q where
  coordinate := coordinate
  prime_cell := hcoordinate
  depth := packet.originalNonSevenPrimeDepthOfCoordinate coordinate hq hq7 hcoordinate
  depth_q_eq := rfl
  depth_row_eq := rfl
  depth_column_eq := rfl

/-- Every prime dividing the terminal cubic root load enters the existing
non-seven prime-power depth layer at the corresponding original routing cell. -/
theorem AwaySevenBaseTerminalRoutingPacket
    .nonempty_originalPrimeDepthPacket_of_dvd_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqLoad : q ∣ awaySevenBaseTerminalCubicRootLoad r) :
    Nonempty (AwaySevenBaseTerminalOriginalPrimeDepthPacket packet q) := by
  have hglobal :=
    packet.prime_dvd_cubicRootLoad_unique_global_cellCoordinate hq hqLoad
  rcases hglobal.2 with ⟨coordinate, hcoordinate, _⟩
  exact ⟨packet.originalPrimeDepthPacketOfCoordinate coordinate hq hglobal.1 hcoordinate⟩

/-- The exact prime power attached to a lifted terminal prime divides its
original routing cell. -/
theorem AwaySevenBaseTerminalOriginalPrimeDepthPacket.modulus_dvd_originalRoutingCell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalOriginalPrimeDepthPacket packet q) :
    a.depth.modulus ∣ routingCell r.routing a.depth.row a.depth.column :=
  a.depth.modulus_dvd_cell

/-- The next prime power does not divide the original routing cell, so the
lifted exponent is its complete prime-adic depth. -/
theorem AwaySevenBaseTerminalOriginalPrimeDepthPacket.nextPower_not_dvd_originalRoutingCell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalOriginalPrimeDepthPacket packet q) :
    ¬ a.depth.q ^ (a.depth.exponent + 1) ∣
      routingCell r.routing a.depth.row a.depth.column :=
  a.depth.next_power_not_dvd_cell

end DkMath.FLT.Seven
