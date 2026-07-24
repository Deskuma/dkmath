/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerClassification
import DkMath.FLT.Seven.PrimePowerOrbitAudit

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimePowerOrbit"

namespace DkMath.FLT.Seven

/-- A terminal cubic-root prime together with its complete original routing
prime depth and its weight-(3,7) unit-orbit classification. -/
structure AwaySevenBaseTerminalPrimePowerOrbitPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (q : ℕ) : Type where
  depthPacket : AwaySevenBaseTerminalOriginalPrimeDepthPacket packet q
  orbit : AwayNonSevenPrimePowerOrbitSource
    depthPacket.depth depthPacket.depth.column

/-- Every lifted terminal prime depth belongs to one of the three complete
weight-(3,7) unit-orbit families on its original routing cell. -/
theorem AwaySevenBaseTerminalOriginalPrimeDepthPacket.nonempty_primePowerOrbitPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalOriginalPrimeDepthPacket packet q) :
    Nonempty (AwaySevenBaseTerminalPrimePowerOrbitPacket packet q) := by
  rcases primePowerOrbitSource_of_depthPacket a.depth with ⟨orbit⟩
  exact ⟨{
    depthPacket := a
    orbit := orbit }⟩

/-- Every prime dividing the terminal cubic root load reaches the existing
complete-depth weight-(3,7) unit-orbit classification of its unique original
routing cell. -/
theorem AwaySevenBaseTerminalRoutingPacket
    .nonempty_primePowerOrbitPacket_of_dvd_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqLoad : q ∣ awaySevenBaseTerminalCubicRootLoad r) :
    Nonempty (AwaySevenBaseTerminalPrimePowerOrbitPacket packet q) := by
  rcases packet.nonempty_originalPrimeDepthPacket_of_dvd_cubicRootLoad hq hqLoad with
    ⟨depthPacket⟩
  exact depthPacket.nonempty_primePowerOrbitPacket

/-- The actual integral coordinates reduced modulo the complete prime power
attached to an orbit-classified terminal prime. -/
def AwaySevenBaseTerminalPrimePowerOrbitPacket.actualSolution
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerOrbitPacket packet q) :
    AwayRoutingPrimePowerSolution a.depthPacket.depth.modulus
      a.depthPacket.depth.row a.depthPacket.depth.column :=
  a.depthPacket.depth.toPrimePowerSolution

/-- The orbit modulus is the exact prime power carried by the unique original
routing cell associated with the terminal prime. -/
theorem AwaySevenBaseTerminalPrimePowerOrbitPacket.modulus_dvd_originalRoutingCell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerOrbitPacket packet q) :
    a.depthPacket.depth.modulus ∣ routingCell r.routing
      a.depthPacket.depth.row a.depthPacket.depth.column :=
  a.depthPacket.depth.modulus_dvd_cell

/-- The lifted exponent is complete: the next power of the addressed prime does
not divide the original routing cell. -/
theorem AwaySevenBaseTerminalPrimePowerOrbitPacket.nextPower_not_dvd_originalRoutingCell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerOrbitPacket packet q) :
    ¬ a.depthPacket.depth.q ^ (a.depthPacket.depth.exponent + 1) ∣
      routingCell r.routing a.depthPacket.depth.row a.depthPacket.depth.column :=
  a.depthPacket.depth.next_power_not_dvd_cell

end DkMath.FLT.Seven
