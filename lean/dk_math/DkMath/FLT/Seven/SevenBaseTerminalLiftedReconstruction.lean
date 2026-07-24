/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalGlobalModel
import Mathlib.Data.ZMod.ValMinAbs

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

/-- The centered signed integer representative of every entry of a residue
coordinate tuple. -/
def AwayRoutingCoordinates.signedRepresentative {M : ℕ}
    (coordinates : AwayRoutingCoordinates (ZMod M)) :
    AwayRoutingCoordinates ℤ :=
  coordinates.map ZMod.valMinAbs

/-- Casting centered signed representatives back to `ZMod M` recovers the
original coordinate tuple exactly. -/
@[simp] theorem AwayRoutingCoordinates.cast_signedRepresentative
    {M : ℕ} (coordinates : AwayRoutingCoordinates (ZMod M)) :
    coordinates.signedRepresentative.map (fun a : ℤ => (a : ZMod M)) =
      coordinates := by
  ext <;> exact ZMod.coe_valMinAbs _

/-- Every entry of an integer coordinate tuple lies in the centered
representative interval for `ZMod M`. -/
def AwayRoutingCoordinates.IsCentered (M : ℕ)
    (coordinates : AwayRoutingCoordinates ℤ) : Prop :=
  coordinates.u * 2 ∈ Set.Ioc (-(M : ℤ)) M ∧
  coordinates.v * 2 ∈ Set.Ioc (-(M : ℤ)) M ∧
  coordinates.y * 2 ∈ Set.Ioc (-(M : ℤ)) M ∧
  coordinates.z * 2 ∈ Set.Ioc (-(M : ℤ)) M

/-- Centered representatives satisfy the common half-open interval
normalization coordinatewise. -/
theorem AwayRoutingCoordinates.signedRepresentative_isCentered
    {M : ℕ} [NeZero M]
    (coordinates : AwayRoutingCoordinates (ZMod M)) :
    (coordinates.signedRepresentative).IsCentered M := by
  exact ⟨ZMod.valMinAbs_mem_Ioc _, ZMod.valMinAbs_mem_Ioc _,
    ZMod.valMinAbs_mem_Ioc _, ZMod.valMinAbs_mem_Ioc _⟩

/-- LIFT-002 signed representative and congruence packet.

The three integer objects are independently chosen centered representatives
of the modular scale, model, and weighted candidate. In particular, this
packet does not claim the integer equality
`weighted = model.weightedScale scale`. -/
structure AwaySevenBaseTerminalSignedRepresentativePacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family) :
    Type where
  scale : ℤ
  model : AwayRoutingCoordinates ℤ
  weighted : AwayRoutingCoordinates ℤ
  scale_cast :
    (scale : ZMod family.combinedModulus) =
      candidate.scale.combinedScale
  model_cast :
    model.map (fun a : ℤ => (a : ZMod family.combinedModulus)) =
      candidate.model.globalModel
  weighted_cast :
    weighted.map (fun a : ℤ => (a : ZMod family.combinedModulus)) =
      candidate.weighted
  scale_centered :
    scale * 2 ∈ Set.Ioc
      (-(family.combinedModulus : ℤ)) family.combinedModulus
  model_centered :
    model.IsCentered family.combinedModulus
  weighted_centered :
    weighted.IsCentered family.combinedModulus

namespace AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket

/-- Choose the canonical centered representatives supplied by
`ZMod.valMinAbs`. -/
noncomputable def signedRepresentativePacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family) :
    AwaySevenBaseTerminalSignedRepresentativePacket candidate := by
  have hMpos : 0 < family.combinedModulus := by
    rw [family.combinedModulus_eq_cubicRootLoad]
    exact awaySevenBaseTerminalCubicRootLoad_pos r
  letI : NeZero family.combinedModulus := ⟨hMpos.ne'⟩
  exact {
    scale := candidate.scale.combinedScale.valMinAbs
    model := candidate.model.globalModel.signedRepresentative
    weighted := candidate.weighted.signedRepresentative
    scale_cast := ZMod.coe_valMinAbs _
    model_cast :=
      AwayRoutingCoordinates.cast_signedRepresentative
        candidate.model.globalModel
    weighted_cast :=
      AwayRoutingCoordinates.cast_signedRepresentative candidate.weighted
    scale_centered := ZMod.valMinAbs_mem_Ioc _
    model_centered :=
      candidate.model.globalModel.signedRepresentative_isCentered
    weighted_centered :=
      candidate.weighted.signedRepresentative_isCentered }

end AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket

/-- Reducing the signed weighted representative at any terminal prime
recovers the actual local coordinate tuple. -/
theorem AwaySevenBaseTerminalSignedRepresentativePacket.local_weighted_congruence
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    signed.weighted.map
        (fun a : ℤ =>
          family.reductionHom q
            (a : ZMod family.combinedModulus)) =
      (family.localActual q).toCoordinates := by
  rw [← candidate.local_actual_reduction q]
  have h := congrArg
    (fun coordinates =>
      coordinates.map (family.reductionHom q))
    signed.weighted_cast
  simpa [AwayRoutingCoordinates.map] using h

end DkMath.FLT.Seven
