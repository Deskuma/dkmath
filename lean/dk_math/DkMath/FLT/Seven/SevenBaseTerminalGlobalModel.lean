/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalGlobalCoordinates

#print "file: DkMath.FLT.Seven.SevenBaseTerminalGlobalModel"

namespace DkMath.FLT.Seven

/-- The column-independent coordinates of the projected model selected at one
terminal prime. -/
def AwaySevenBaseTerminalPrimeScaleFamily.localModelCoordinates
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    AwayRoutingCoordinates (ZMod (family.localModulus q)) :=
  (family.localModel q).toCoordinates

/-- A product-modulus residue model whose four coordinates reduce exactly to
the four coordinates of every projected local model.

This packet is coordinate compatibility only. It does not equip the combined
coordinates with one column-independent polynomial-system certificate. -/
structure AwaySevenBaseTerminalGlobalModelCoordinatesPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) : Type where
  globalModel : AwayRoutingCoordinates (ZMod family.combinedModulus)
  local_model_reduction :
    ∀ q, globalModel.map (family.reductionHom q) =
      family.localModelCoordinates q

/-- Glue all four projected local-model coordinates independently through the
finite Chinese-remainder equivalence. -/
noncomputable def AwaySevenBaseTerminalPrimeScaleFamily.globalModelCoordinatesPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) :
    AwaySevenBaseTerminalGlobalModelCoordinatesPacket family := by
  let crt :=
    ZMod.prodEquivPi family.localModulus family.localModuli_pairwise_coprime
  let localU :
      (q : AwaySevenBaseTerminalPrimeIndex r) →
        ZMod (family.localModulus q) :=
    fun q => (family.localModelCoordinates q).u
  let localV :
      (q : AwaySevenBaseTerminalPrimeIndex r) →
        ZMod (family.localModulus q) :=
    fun q => (family.localModelCoordinates q).v
  let localY :
      (q : AwaySevenBaseTerminalPrimeIndex r) →
        ZMod (family.localModulus q) :=
    fun q => (family.localModelCoordinates q).y
  let localZ :
      (q : AwaySevenBaseTerminalPrimeIndex r) →
        ZMod (family.localModulus q) :=
    fun q => (family.localModelCoordinates q).z
  let globalModel : AwayRoutingCoordinates (ZMod family.combinedModulus) := {
    u := crt.symm localU
    v := crt.symm localV
    y := crt.symm localY
    z := crt.symm localZ }
  refine {
    globalModel := globalModel
    local_model_reduction := ?_ }
  intro q
  apply AwayRoutingCoordinates.ext
  · exact congrFun (crt.apply_symm_apply localU) q
  · exact congrFun (crt.apply_symm_apply localV) q
  · exact congrFun (crt.apply_symm_apply localY) q
  · exact congrFun (crt.apply_symm_apply localZ) q

/-- Every terminal prime-scale family has a coordinate-compatible global
product-modulus model. -/
theorem nonempty_awaySevenBaseTerminalGlobalModelCoordinatesPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) :
    Nonempty (AwaySevenBaseTerminalGlobalModelCoordinatesPacket family) :=
  ⟨family.globalModelCoordinatesPacket⟩

/-- Strengthened MODEL-002 packet retaining the separately audited equality
between every chosen scale projection and its orbit source. -/
structure AwaySevenBaseTerminalOrbitCoherentGlobalModelPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) : Type where
  coordinates : AwaySevenBaseTerminalGlobalModelCoordinatesPacket family
  local_orbit_coherence : family.IsLocallyOrbitCoherent

/-- A locally orbit-coherent family admits the strengthened global coordinate
packet without weakening or erasing the coherence proof. -/
noncomputable def
    AwaySevenBaseTerminalPrimeScaleFamily.orbitCoherentGlobalModelPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (hcoherent : family.IsLocallyOrbitCoherent) :
    AwaySevenBaseTerminalOrbitCoherentGlobalModelPacket family where
  coordinates := family.globalModelCoordinatesPacket
  local_orbit_coherence := hcoherent

/-- A MODEL-002 global compatibility packet chosen directly from the terminal
orbit sources. The family is locally orbit-coherent and its projected model
coordinates are simultaneously reconstructed modulo the product modulus. -/
structure AwaySevenBaseTerminalGlobalModelCompatibilityPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) :
    Type where
  family : AwaySevenBaseTerminalPrimeScaleFamily packet
  local_orbit_coherence : family.IsLocallyOrbitCoherent
  coordinates : AwaySevenBaseTerminalGlobalModelCoordinatesPacket family

/-- Choose each local projection directly from its orbit source, preserving
local source/projection coherence, and then glue all projected model
coordinates by finite CRT. -/
noncomputable def
    AwaySevenBaseTerminalRoutingPacket.globalModelCompatibilityPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) :
    AwaySevenBaseTerminalGlobalModelCompatibilityPacket packet := by
  let family : AwaySevenBaseTerminalPrimeScaleFamily packet := {
    localPacket := fun q =>
      (Classical.choice
        (packet.nonempty_primePowerOrbitPacket_of_dvd_cubicRootLoad
          q.prime q.dvd_cubicRootLoad)).toScaleProjectionPacket }
  have hcoherent : family.IsLocallyOrbitCoherent := by
    intro q
    exact
      AwaySevenBaseTerminalPrimePowerOrbitPacket.toScaleProjectionPacket_isOrbitCoherent
        _
  exact {
    family := family
    local_orbit_coherence := hcoherent
    coordinates := family.globalModelCoordinatesPacket }

/-- The terminal routing packet therefore admits a coherent global
product-modulus coordinate model. -/
theorem nonempty_awaySevenBaseTerminalGlobalModelCompatibilityPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) :
    Nonempty (AwaySevenBaseTerminalGlobalModelCompatibilityPacket packet) :=
  ⟨packet.globalModelCompatibilityPacket⟩

end DkMath.FLT.Seven
