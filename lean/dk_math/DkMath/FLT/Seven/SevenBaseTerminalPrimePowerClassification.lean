/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalOriginalPrimeDepth
import DkMath.FLT.Seven.PrimePowerCellAudit

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimePowerClassification"

set_option linter.style.longLine false

namespace DkMath.FLT.Seven

/-- A terminal cubic-root prime together with its complete original routing
prime depth and the corresponding explicit prime-power solubility family. -/
structure AwaySevenBaseTerminalPrimePowerClassificationPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (q : ℕ) : Type where
  depthPacket : AwaySevenBaseTerminalOriginalPrimeDepthPacket packet q
  classification : AwayNonSevenPrimePowerSolubilitySource
    depthPacket.depth depthPacket.depth.column

/-- Every lifted terminal prime depth belongs to one of the three explicit
prime-power column families, with its endpoint row selecting one of the nine
routing cells. -/
theorem AwaySevenBaseTerminalOriginalPrimeDepthPacket.nonempty_primePowerClassificationPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalOriginalPrimeDepthPacket packet q) :
    Nonempty (AwaySevenBaseTerminalPrimePowerClassificationPacket packet q) := by
  rcases primePowerSolubilitySource_of_depthPacket a.depth with ⟨classification⟩
  exact ⟨{
    depthPacket := a
    classification := classification }⟩

/-- Every prime dividing the terminal cubic root load reaches the existing
complete-depth `ZMod (q^e)` classification of its unique original routing cell. -/
theorem AwaySevenBaseTerminalRoutingPacket.nonempty_primePowerClassificationPacket_of_dvd_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqLoad : q ∣ awaySevenBaseTerminalCubicRootLoad r) :
    Nonempty (AwaySevenBaseTerminalPrimePowerClassificationPacket packet q) := by
  rcases packet.nonempty_originalPrimeDepthPacket_of_dvd_cubicRootLoad hq hqLoad with
    ⟨depthPacket⟩
  exact depthPacket.nonempty_primePowerClassificationPacket

/-- The actual integral coordinates, reduced modulo the complete prime power
attached to a classified terminal prime. -/
def AwaySevenBaseTerminalPrimePowerClassificationPacket.actualSolution
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerClassificationPacket packet q) :
    AwayRoutingPrimePowerSolution a.depthPacket.depth.modulus
      a.depthPacket.depth.row a.depthPacket.depth.column :=
  a.depthPacket.depth.toPrimePowerSolution

/-- The classification modulus is the exact prime power carried by the unique
original routing cell associated with the terminal prime. -/
theorem AwaySevenBaseTerminalPrimePowerClassificationPacket.modulus_dvd_originalRoutingCell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerClassificationPacket packet q) :
    a.depthPacket.depth.modulus ∣ routingCell r.routing
      a.depthPacket.depth.row a.depthPacket.depth.column :=
  a.depthPacket.depth.modulus_dvd_cell

end DkMath.FLT.Seven
