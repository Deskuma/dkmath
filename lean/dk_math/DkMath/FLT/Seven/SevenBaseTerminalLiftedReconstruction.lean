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

/-- The integer defect between the independently centered weighted tuple and
the integer weighted scaling of the centered model. -/
def AwaySevenBaseTerminalSignedRepresentativePacket.integerWeightedDefect
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwayRoutingCoordinates ℤ where
  u := signed.weighted.u - signed.model.u * signed.scale ^ 3
  v := signed.weighted.v - signed.model.v * signed.scale ^ 3
  y := signed.weighted.y - signed.model.y * signed.scale ^ 7
  z := signed.weighted.z - signed.model.z * signed.scale ^ 7

/-- LIFT-003 exact defect packet. Every coordinate defect is a multiple of the
complete combined modulus; vanishing is deliberately not asserted. -/
structure AwaySevenBaseTerminalIntegerWeightedDefectPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type where
  defect : AwayRoutingCoordinates ℤ
  defect_eq : defect = signed.integerWeightedDefect
  modulus_dvd_u : (family.combinedModulus : ℤ) ∣ defect.u
  modulus_dvd_v : (family.combinedModulus : ℤ) ∣ defect.v
  modulus_dvd_y : (family.combinedModulus : ℤ) ∣ defect.y
  modulus_dvd_z : (family.combinedModulus : ℤ) ∣ defect.z

/-- Construct the exact divisibility certificate for the integer weighted
defect from the modular weighted identity. -/
def AwaySevenBaseTerminalSignedRepresentativePacket.integerWeightedDefectPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwaySevenBaseTerminalIntegerWeightedDefectPacket signed := by
  let castCoordinates :=
    fun coordinates : AwayRoutingCoordinates ℤ =>
      coordinates.map
        (fun a : ℤ => (a : ZMod family.combinedModulus))
  have hscaled :
      castCoordinates
          (signed.model.weightedScale signed.scale) =
        candidate.weighted := by
    calc
      castCoordinates
          (signed.model.weightedScale signed.scale) =
          (castCoordinates signed.model).weightedScale
            (signed.scale : ZMod family.combinedModulus) :=
        AwayRoutingCoordinates.map_weightedScale
          (Int.castRingHom (ZMod family.combinedModulus))
          signed.model signed.scale
      _ = candidate.model.globalModel.weightedScale
            candidate.scale.combinedScale := by
        dsimp [castCoordinates]
        rw [signed.model_cast, signed.scale_cast]
      _ = candidate.weighted := candidate.weighted_eq.symm
  have hcast :
      castCoordinates signed.weighted =
        castCoordinates
          (signed.model.weightedScale signed.scale) :=
    signed.weighted_cast.trans hscaled.symm
  let defect := signed.integerWeightedDefect
  refine {
    defect := defect
    defect_eq := rfl
    modulus_dvd_u := ?_
    modulus_dvd_v := ?_
    modulus_dvd_y := ?_
    modulus_dvd_z := ?_ }
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h := congrArg (fun a => a.u) hcast
    simpa [castCoordinates, defect, integerWeightedDefect,
      AwayRoutingCoordinates.weightedScale,
      AwayRoutingCoordinates.map] using sub_eq_zero.mpr h
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h := congrArg (fun a => a.v) hcast
    simpa [castCoordinates, defect, integerWeightedDefect,
      AwayRoutingCoordinates.weightedScale,
      AwayRoutingCoordinates.map] using sub_eq_zero.mpr h
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h := congrArg (fun a => a.y) hcast
    simpa [castCoordinates, defect, integerWeightedDefect,
      AwayRoutingCoordinates.weightedScale,
      AwayRoutingCoordinates.map] using sub_eq_zero.mpr h
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h := congrArg (fun a => a.z) hcast
    simpa [castCoordinates, defect, integerWeightedDefect,
      AwayRoutingCoordinates.weightedScale,
      AwayRoutingCoordinates.map] using sub_eq_zero.mpr h

/-- The exact scalar criterion upgrading a modular defect to an integer
equality. The strict absolute-value bound is an explicit input. -/
theorem integerWeightedDefect_eq_zero_of_abs_lt
    {M : ℕ} {defect : ℤ}
    (hdiv : (M : ℤ) ∣ defect) (hsmall : |defect| < M) :
    defect = 0 :=
  Int.eq_zero_of_abs_lt_dvd hdiv hsmall

/-- The zero coordinate tuple used to state exact reconstruction outcomes. -/
def AwayRoutingCoordinates.zero (R : Type*) [Zero R] :
    AwayRoutingCoordinates R where
  u := 0
  v := 0
  y := 0
  z := 0

/-- Vanishing of the exact defect is equivalent to the desired integer
weight-(3,7) reconstruction equality. -/
theorem AwaySevenBaseTerminalSignedRepresentativePacket.integerWeightedDefect_eq_zero_iff
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    signed.integerWeightedDefect = AwayRoutingCoordinates.zero ℤ ↔
      signed.weighted = signed.model.weightedScale signed.scale := by
  constructor
  · intro h
    apply AwayRoutingCoordinates.ext
    · have hc := congrArg (fun a => a.u) h
      change signed.weighted.u -
        signed.model.u * signed.scale ^ 3 = 0 at hc
      exact sub_eq_zero.mp hc
    · have hc := congrArg (fun a => a.v) h
      change signed.weighted.v -
        signed.model.v * signed.scale ^ 3 = 0 at hc
      exact sub_eq_zero.mp hc
    · have hc := congrArg (fun a => a.y) h
      change signed.weighted.y -
        signed.model.y * signed.scale ^ 7 = 0 at hc
      exact sub_eq_zero.mp hc
    · have hc := congrArg (fun a => a.z) h
      change signed.weighted.z -
        signed.model.z * signed.scale ^ 7 = 0 at hc
      exact sub_eq_zero.mp hc
  · intro h
    ext <;>
      simp [integerWeightedDefect, AwayRoutingCoordinates.zero,
        AwayRoutingCoordinates.weightedScale, h]

/-- An exact signed reconstruction obstruction is a certified nonzero defect,
all of whose entries remain multiples of the combined modulus. -/
structure AwaySevenBaseTerminalSignedReconstructionObstruction
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type where
  defectPacket : AwaySevenBaseTerminalIntegerWeightedDefectPacket signed
  defect_ne_zero :
    defectPacket.defect ≠ AwayRoutingCoordinates.zero ℤ

/-- Exact LIFT-003 outcome: either signed integer reconstruction holds, or a
nonzero combined-modulus defect is retained as an explicit obstruction. -/
inductive AwaySevenBaseTerminalSignedReconstructionOutcome
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type
  | reconstructed
      (weighted_eq :
        signed.weighted = signed.model.weightedScale signed.scale)
  | obstructed
      (obstruction :
        AwaySevenBaseTerminalSignedReconstructionObstruction signed)

/-- Classify the signed lift by its exact integer defect, without assuming a
size bound that would force the defect to vanish. -/
noncomputable def AwaySevenBaseTerminalSignedRepresentativePacket.signedReconstructionOutcome
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwaySevenBaseTerminalSignedReconstructionOutcome signed := by
  let defectPacket := signed.integerWeightedDefectPacket
  by_cases hzero :
      defectPacket.defect = AwayRoutingCoordinates.zero ℤ
  · apply AwaySevenBaseTerminalSignedReconstructionOutcome.reconstructed
    apply signed.integerWeightedDefect_eq_zero_iff.mp
    exact defectPacket.defect_eq.symm.trans hzero
  · exact AwaySevenBaseTerminalSignedReconstructionOutcome.obstructed
      ⟨defectPacket, hzero⟩

end DkMath.FLT.Seven
