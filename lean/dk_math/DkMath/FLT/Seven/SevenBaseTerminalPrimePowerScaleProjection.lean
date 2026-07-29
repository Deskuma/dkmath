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
  actual_original_u : actual.u = p.toPrimePowerSolution.u
  actual_original_v : actual.v = p.toPrimePowerSolution.v
  actual_original_y : actual.y = p.toPrimePowerSolution.y
  actual_original_z : actual.z = p.toPrimePowerSolution.z

/-- Forget the column-specific root and correction data while retaining the
actual/model pair and its common weight-(3,7) unit scale. -/
def AwayNonSevenPrimePowerOrbitSource.toProjection
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    {p : AwayNonSevenPrimeDepthPacket r} {column : RootRoutingColumn}
    (source : AwayNonSevenPrimePowerOrbitSource p column) :
    AwayNonSevenPrimePowerOrbitProjection p column := by
  cases source with
  | sevenV actual model scale scale_isUnit actual_eq hu hv hy hz =>
      exact {
        actual := actual
        model := model
        scale := scale
        scale_isUnit := scale_isUnit
        actual_eq := actual_eq
        actual_original_u := hu
        actual_original_v := hv
        actual_original_y := hy
        actual_original_z := hz }
  | leftCubic t root correction_unit actual model scale scale_isUnit actual_eq
      hu hv hy hz =>
      exact {
        actual := actual
        model := model
        scale := scale
        scale_isUnit := scale_isUnit
        actual_eq := actual_eq
        actual_original_u := hu
        actual_original_v := hv
        actual_original_y := hy
        actual_original_z := hz }
  | rightCubic t root correction_unit actual model scale scale_isUnit actual_eq
      hu hv hy hz =>
      exact {
        actual := actual
        model := model
        scale := scale
        scale_isUnit := scale_isUnit
        actual_eq := actual_eq
        actual_original_u := hu
        actual_original_v := hv
        actual_original_y := hy
        actual_original_z := hz }

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

/-- The projected actual solution is the original integral routing solution
reduced modulo the complete local prime power. -/
theorem AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.actual_eq_original
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (a : AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q) :
    a.projection.actual =
      a.orbitPacket.depthPacket.depth.toPrimePowerSolution :=
  AwayRoutingPrimePowerSolution.ext
    a.projection.actual_original_u
    a.projection.actual_original_v
    a.projection.actual_original_y
    a.projection.actual_original_z

end DkMath.FLT.Seven
