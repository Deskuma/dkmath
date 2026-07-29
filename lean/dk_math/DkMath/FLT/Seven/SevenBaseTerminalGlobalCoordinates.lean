/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalCubicRootLoadModulus

#print "file: DkMath.FLT.Seven.SevenBaseTerminalGlobalCoordinates"

namespace DkMath.FLT.Seven

/-- A column-independent carrier for the four coordinates of an away routing
model. It deliberately contains no local equation certificate. -/
structure AwayRoutingCoordinates (R : Type*) where
  u : R
  v : R
  y : R
  z : R

@[ext] theorem AwayRoutingCoordinates.ext {R : Type*}
    {a b : AwayRoutingCoordinates R}
    (hu : a.u = b.u) (hv : a.v = b.v)
    (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a
  cases b
  simp_all

/-- Apply one function to every entry of a column-independent coordinate
tuple. -/
def AwayRoutingCoordinates.map {R S : Type*} (f : R → S)
    (a : AwayRoutingCoordinates R) : AwayRoutingCoordinates S where
  u := f a.u
  v := f a.v
  y := f a.y
  z := f a.z

@[simp] theorem AwayRoutingCoordinates.map_u {R S : Type*} (f : R → S)
    (a : AwayRoutingCoordinates R) : (a.map f).u = f a.u := rfl

@[simp] theorem AwayRoutingCoordinates.map_v {R S : Type*} (f : R → S)
    (a : AwayRoutingCoordinates R) : (a.map f).v = f a.v := rfl

@[simp] theorem AwayRoutingCoordinates.map_y {R S : Type*} (f : R → S)
    (a : AwayRoutingCoordinates R) : (a.map f).y = f a.y := rfl

@[simp] theorem AwayRoutingCoordinates.map_z {R S : Type*} (f : R → S)
    (a : AwayRoutingCoordinates R) : (a.map f).z = f a.z := rfl

/-- Forget the row- and column-specific equation certificates of a local
prime-power solution, retaining exactly its four residue coordinates. -/
def AwayRoutingPrimePowerSolution.toCoordinates
    {M : ℕ} {row : EndpointRoutingRow} {column : RootRoutingColumn}
    (a : AwayRoutingPrimePowerSolution M row column) :
    AwayRoutingCoordinates (ZMod M) where
  u := a.u
  v := a.v
  y := a.y
  z := a.z

/-- Coordinates of the chosen actual solution in one projected local orbit. -/
def AwayNonSevenPrimePowerOrbitProjection.actualCoordinates
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    {p : AwayNonSevenPrimeDepthPacket r} {column : RootRoutingColumn}
    (projection : AwayNonSevenPrimePowerOrbitProjection p column) :
    AwayRoutingCoordinates (ZMod p.modulus) :=
  projection.actual.toCoordinates

/-- Coordinates of the chosen model in one projected local orbit. -/
def AwayNonSevenPrimePowerOrbitProjection.modelCoordinates
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    {p : AwayNonSevenPrimeDepthPacket r} {column : RootRoutingColumn}
    (projection : AwayNonSevenPrimePowerOrbitProjection p column) :
    AwayRoutingCoordinates (ZMod p.modulus) :=
  projection.model.toCoordinates

/-- Exact local coherence condition omitted from the current
`AwaySevenBaseTerminalPrimePowerScaleProjectionPacket` fields. -/
def AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.IsOrbitCoherent
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ}
    (localPacket :
      AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q) :
    Prop :=
  localPacket.projection = localPacket.orbitPacket.orbit.toProjection

/-- A projection packet produced directly from an orbit packet is locally
coherent. -/
theorem AwaySevenBaseTerminalPrimePowerOrbitPacket.toScaleProjectionPacket_isOrbitCoherent
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (orbit : AwaySevenBaseTerminalPrimePowerOrbitPacket packet q) :
    orbit.toScaleProjectionPacket.IsOrbitCoherent :=
  rfl

/-- The exact family-level local coherence obligation exposed by MODEL-001.
It is not a global CRT compatibility assertion. -/
def AwaySevenBaseTerminalPrimeScaleFamily.IsLocallyOrbitCoherent
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) : Prop :=
  ∀ q, (family.localPacket q).IsOrbitCoherent

/-- MODEL-001 audit packet for one complete local model.

The projected coordinate tuple is column-independent, while `orbitSource`
retains the exact column-indexed orbit constructor, including a cubic-root
parameter and its correction-unit certificate in the left and right sectors.
The current scale-projection packet does not contain an equality identifying
its separately stored projection with `orbitSource.toProjection`, so this audit
does not invent such an equality or any global compatibility assertion. -/
structure AwayNonSevenPrimePowerLocalModelCompatibilityAudit
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : Type where
  projectedModelCoordinates : AwayRoutingCoordinates (ZMod p.modulus)
  orbitSource : AwayNonSevenPrimePowerOrbitSource p p.column

/-- Audit the model selected by one member of the terminal prime-scale family
without erasing its constructor-specific source data. -/
def AwaySevenBaseTerminalPrimeScaleFamily.localModelCompatibilityAudit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    AwayNonSevenPrimePowerLocalModelCompatibilityAudit
      (family.localDepth q) where
  projectedModelCoordinates := (family.localModel q).toCoordinates
  orbitSource := (family.localPacket q).orbitPacket.orbit

/-- The coordinate view exposed by the local compatibility audit is exactly
the coordinate view of the family model. -/
theorem AwaySevenBaseTerminalPrimeScaleFamily.localModelCompatibilityAudit_coordinates
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    (family.localModelCompatibilityAudit q).projectedModelCoordinates =
      (family.localModel q).toCoordinates := by
  rfl

end DkMath.FLT.Seven
