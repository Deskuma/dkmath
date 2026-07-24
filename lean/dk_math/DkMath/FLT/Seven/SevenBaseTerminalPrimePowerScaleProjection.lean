/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerOrbit

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimePowerScaleProjection"

namespace DkMath.FLT.Seven

/-- The column-independent core of a complete prime-power unit-orbit witness. -/
structure AwayNonSevenPrimePowerOrbitProjection
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) (column : RootRoutingColumn) : Type where
  actual : AwayRoutingPrimePowerSolution p.modulus p.row column
  model : AwayRoutingPrimePowerSolution p.modulus p.row column
  scale : ZMod p.modulus
  scale_isUnit : IsUnit scale
  actual_eq : actual = scalePrimePowerSolution model scale scale_isUnit

/-- Forget the column-specific root and correction data while retaining the
actual/model pair and its common weight-(3,7) unit scale. -/
def AwayNonSevenPrimePowerOrbitSource.toProjection
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    {p : AwayNonSevenPrimeDepthPacket r} {column : RootRoutingColumn}
    (source : AwayNonSevenPrimePowerOrbitSource p column) :
    AwayNonSevenPrimePowerOrbitProjection p column := by
  cases source with
  | sevenV actual model scale scale_isUnit actual_eq =>
      exact {
        actual := actual
        model := model
        scale := scale
        scale_isUnit := scale_isUnit
        actual_eq := actual_eq }
  | leftCubic t root correction_unit actual model scale scale_isUnit actual_eq =>
      exact {
        actual := actual
        model := model
        scale := scale
        scale_isUnit := scale_isUnit
        actual_eq := actual_eq }
  | rightCubic t root correction_unit actual model scale scale_isUnit actual_eq =>
      exact {
        actual := actual
        model := model
        scale := scale
        scale_isUnit := scale_isUnit
        actual_eq := actual_eq }

/-- A terminal prime orbit together with its column-independent local scale
projection. -/
structure AwaySevenBaseTerminalPrimePowerScaleProjectionPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (q : ℕ) : Type where
  orbitPacket : AwaySevenBaseTerminalPrimePowerOrbitPacket packet q
  projection : AwayNonSevenPrimePowerOrbitProjection
    orbitPacket.depthPacket.depth orbitPacket.depthPacket.depth.column

/-- Normalize one terminal orbit packet to its common actual/model/scale core. -/
def AwaySevenBaseTerminalPrimePowerOrbitPacket.toScaleProjectionPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerOrbitPacket packet q) :
    AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q where
  orbitPacket := a
  projection := a.orbit.toProjection

/-- Every terminal cubic-root prime has a complete local unit scale projection
at its exact original routing-cell modulus. -/
theorem AwaySevenBaseTerminalRoutingPacket.nonempty_primePowerScaleProjectionPacket_of_dvd_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqLoad : q ∣ awaySevenBaseTerminalCubicRootLoad r) :
    Nonempty (AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q) := by
  rcases packet.nonempty_primePowerOrbitPacket_of_dvd_cubicRootLoad hq hqLoad with ⟨orbitPacket⟩
  exact ⟨orbitPacket.toScaleProjectionPacket⟩

/-- The local scale attached to the terminal prime. -/
def AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.localScale
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q) :
    ZMod a.orbitPacket.depthPacket.depth.modulus :=
  a.projection.scale

/-- The projected local scale is invertible modulo the complete prime power. -/
theorem AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.localScale_isUnit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q) :
    IsUnit a.localScale :=
  a.projection.scale_isUnit

/-- The projected actual solution is exactly the weight-(3,7) scaling of its
projected canonical model by the local unit scale. -/
theorem AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.actual_eq_weightedScale
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q) :
    a.projection.actual = scalePrimePowerSolution a.projection.model
      a.localScale a.localScale_isUnit := by
  exact a.projection.actual_eq

end DkMath.FLT.Seven
