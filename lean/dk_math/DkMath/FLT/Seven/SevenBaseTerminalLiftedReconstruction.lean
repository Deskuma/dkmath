/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalGlobalModel

#print "file: DkMath.FLT.Seven.SevenBaseTerminalLiftedReconstruction"

namespace DkMath.FLT.Seven

/-- Apply the FLT7 weight-three root scaling and weight-seven endpoint scaling
to a column-independent coordinate tuple. -/
def AwayRoutingCoordinates.weightedScale {R : Type*} [Monoid R]
    (model : AwayRoutingCoordinates R) (scale : R) :
    AwayRoutingCoordinates R where
  u := model.u * scale ^ 3
  v := model.v * scale ^ 3
  y := model.y * scale ^ 7
  z := model.z * scale ^ 7

/-- Ring homomorphisms commute with the weight-(3,7) coordinate scaling. -/
theorem AwayRoutingCoordinates.map_weightedScale
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (model : AwayRoutingCoordinates R) (scale : R) :
    (model.weightedScale scale).map f =
      (model.map f).weightedScale (f scale) := by
  ext <;> simp [AwayRoutingCoordinates.weightedScale]

/-- Forgetting the local equation certificates commutes with the existing
prime-power solution scaling operation. -/
theorem scalePrimePowerSolution_toCoordinates
    {M : ℕ} {row : EndpointRoutingRow} {column : RootRoutingColumn}
    (model : AwayRoutingPrimePowerSolution M row column)
    (scale : ZMod M) (scale_isUnit : IsUnit scale) :
    (scalePrimePowerSolution model scale scale_isUnit).toCoordinates =
      model.toCoordinates.weightedScale scale :=
  rfl

/-- LIFT-001 product-modulus weighted coordinate candidate.

It combines one CRT-compatible global model tuple with one simultaneous unit
scale. Its reduction theorem recovers the actual local coordinates at every
terminal prime. No integer representative or signed equality is asserted. -/
structure AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) : Type where
  model : AwaySevenBaseTerminalGlobalModelCoordinatesPacket family
  scale : AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family
  weighted :
    AwayRoutingCoordinates (ZMod family.combinedModulus)
  weighted_eq :
    weighted = model.globalModel.weightedScale scale.combinedScale
  local_actual_reduction :
    ∀ q, weighted.map (family.reductionHom q) =
      (family.localActual q).toCoordinates

/-- Form the modular weighted candidate from independently proved global-model
and global-scale CRT packets over the same local family. -/
noncomputable def
    AwaySevenBaseTerminalGlobalModelCoordinatesPacket.weightedCoordinatesPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (model : AwaySevenBaseTerminalGlobalModelCoordinatesPacket family)
    (scale : AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family) :
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family := by
  let weighted :=
    model.globalModel.weightedScale scale.combinedScale
  refine {
    model := model
    scale := scale
    weighted := weighted
    weighted_eq := rfl
    local_actual_reduction := ?_ }
  intro q
  calc
    weighted.map (family.reductionHom q) =
        (model.globalModel.map (family.reductionHom q)).weightedScale
          (family.reductionHom q scale.combinedScale) :=
      AwayRoutingCoordinates.map_weightedScale
        (family.reductionHom q) model.globalModel scale.combinedScale
    _ = (family.localModelCoordinates q).weightedScale
          (family.localScale q) := by
      rw [model.local_model_reduction q, scale.reduces_to_localScale q]
    _ = (family.localActual q).toCoordinates := by
      simp only [AwaySevenBaseTerminalPrimeScaleFamily.localModelCoordinates]
      rw [family.localActual_eq_weightedScale q,
        scalePrimePowerSolution_toCoordinates]

/-- The coherent MODEL-002 compatibility packet canonically supplies the
LIFT-001 weighted coordinate candidate. -/
noncomputable def
    AwaySevenBaseTerminalGlobalModelCompatibilityPacket.weightedCoordinatesPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (compatibility :
      AwaySevenBaseTerminalGlobalModelCompatibilityPacket packet) :
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket
      compatibility.family :=
  compatibility.coordinates.weightedCoordinatesPacket
    compatibility.family.finiteScaleGluingPacket

/-- Every terminal routing packet admits a product-modulus weighted coordinate
candidate with exact local reductions. -/
theorem nonempty_awaySevenBaseTerminalProductModulusWeightedCoordinatesPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) :
    Nonempty
      (AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket
        packet.globalModelCompatibilityPacket.family) :=
  ⟨packet.globalModelCompatibilityPacket.weightedCoordinatesPacket⟩

end DkMath.FLT.Seven
