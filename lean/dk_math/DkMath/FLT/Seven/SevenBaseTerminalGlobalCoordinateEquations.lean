/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalLiftedReconstruction

#print "file: DkMath.FLT.Seven.SevenBaseTerminalGlobalCoordinateEquations"

namespace DkMath.FLT.Seven

/-- First seventh-power coordinate over an arbitrary commutative ring. -/
def seventhPowerFstR {R : Type*} [CommRing R] (u v : R) : R :=
  u ^ 7 - 42 * u ^ 5 * v ^ 2 - 70 * u ^ 4 * v ^ 3
    + 70 * u ^ 3 * v ^ 4 + 126 * u ^ 2 * v ^ 5
    + 14 * u * v ^ 6 - 10 * v ^ 7

/-- Second seventh-power coordinate over an arbitrary commutative ring. -/
def seventhPowerSndR {R : Type*} [CommRing R] (u v : R) : R :=
  7 * u ^ 6 * v + 21 * u ^ 5 * v ^ 2 - 35 * u ^ 4 * v ^ 3
    - 105 * u ^ 3 * v ^ 4 - 21 * u ^ 2 * v ^ 5
    + 35 * u * v ^ 6 + 7 * v ^ 7

/-- First cubic cyclotomic coordinate over an arbitrary commutative ring. -/
def cyclotomicSevenFstR {R : Type*} [CommRing R] (z y : R) : R :=
  z ^ 3 + z ^ 2 * y - y ^ 3

/-- Second cubic cyclotomic coordinate over an arbitrary commutative ring. -/
def cyclotomicSevenSndR {R : Type*} [CommRing R] (z y : R) : R :=
  -z ^ 2 * y - z * y ^ 2

@[simp] theorem seventhPowerFstR_int (u v : ℤ) :
    seventhPowerFstR u v = seventhPowerFst u v := rfl

@[simp] theorem seventhPowerSndR_int (u v : ℤ) :
    seventhPowerSndR u v = seventhPowerSnd u v := rfl

@[simp] theorem cyclotomicSevenFstR_int (z y : ℤ) :
    cyclotomicSevenFstR z y = cyclotomicSevenFst z y := rfl

@[simp] theorem cyclotomicSevenSndR_int (z y : ℤ) :
    cyclotomicSevenSndR z y = cyclotomicSevenSnd z y := rfl

theorem seventhPowerFstR_weighted {R : Type*} [CommRing R]
    (u v scale : R) :
    seventhPowerFstR (u * scale ^ 3) (v * scale ^ 3) =
      scale ^ 21 * seventhPowerFstR u v := by
  simp [seventhPowerFstR]
  ring

theorem seventhPowerSndR_weighted {R : Type*} [CommRing R]
    (u v scale : R) :
    seventhPowerSndR (u * scale ^ 3) (v * scale ^ 3) =
      scale ^ 21 * seventhPowerSndR u v := by
  simp [seventhPowerSndR]
  ring

theorem cyclotomicSevenFstR_weighted {R : Type*} [CommRing R]
    (z y scale : R) :
    cyclotomicSevenFstR (z * scale ^ 7) (y * scale ^ 7) =
      scale ^ 21 * cyclotomicSevenFstR z y := by
  simp [cyclotomicSevenFstR]
  ring

theorem cyclotomicSevenSndR_weighted {R : Type*} [CommRing R]
    (z y scale : R) :
    cyclotomicSevenSndR (z * scale ^ 7) (y * scale ^ 7) =
      scale ^ 21 * cyclotomicSevenSndR z y := by
  simp [cyclotomicSevenSndR]
  ring

/-- The two universal coordinate equations satisfied by the global CRT model.
This is independent of the row- and column-specific local cell systems. -/
structure AwaySevenBaseTerminalGlobalCoordinateEquationPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family) :
    Prop where
  fstEquation :
    seventhPowerFstR candidate.model.globalModel.u
        candidate.model.globalModel.v =
      cyclotomicSevenFstR candidate.model.globalModel.z
        candidate.model.globalModel.y
  sndEquation :
    seventhPowerSndR candidate.model.globalModel.u
        candidate.model.globalModel.v =
      cyclotomicSevenSndR candidate.model.globalModel.z
        candidate.model.globalModel.y

theorem
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket.weighted_fstEquation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family) :
    seventhPowerFstR candidate.weighted.u candidate.weighted.v =
      cyclotomicSevenFstR candidate.weighted.z candidate.weighted.y := by
  rw [candidate.weighted_eq_original]
  have h := congrArg
    (fun a : ℤ => (a : ZMod family.combinedModulus))
    r.cubic.rootTriple.normal.fst_eq
  simpa [awaySevenBaseTerminalOriginalCoordinates, seventhPowerFstR,
    cyclotomicSevenFstR, seventhPowerFst, cyclotomicSevenFst] using h.symm

theorem
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket.weighted_sndEquation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family) :
    seventhPowerSndR candidate.weighted.u candidate.weighted.v =
      cyclotomicSevenSndR candidate.weighted.z candidate.weighted.y := by
  rw [candidate.weighted_eq_original]
  have h := congrArg
    (fun a : ℤ => (a : ZMod family.combinedModulus))
    r.cubic.rootTriple.normal.snd_eq
  simpa [awaySevenBaseTerminalOriginalCoordinates, seventhPowerSndR,
    cyclotomicSevenSndR, seventhPowerSnd, cyclotomicSevenSnd] using h.symm

/-- Cancel the common unit scale of total weight 21 and recover the universal
equations for the unscaled global model. -/
theorem
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket.globalCoordinateEquations
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family) :
    AwaySevenBaseTerminalGlobalCoordinateEquationPacket candidate := by
  have hfst := candidate.weighted_fstEquation
  have hsnd := candidate.weighted_sndEquation
  rw [candidate.weighted_eq] at hfst hsnd
  refine ⟨?_, ?_⟩
  · apply (candidate.scale.combinedScale_isUnit.pow 21).mul_left_cancel
    simpa [AwayRoutingCoordinates.weightedScale,
      seventhPowerFstR_weighted, cyclotomicSevenFstR_weighted] using hfst
  · apply (candidate.scale.combinedScale_isUnit.pow 21).mul_left_cancel
    simpa [AwayRoutingCoordinates.weightedScale,
      seventhPowerSndR_weighted, cyclotomicSevenSndR_weighted] using hsnd

/-- Exact integer carries for the two universal equations of centered model
representatives.  No bound or vanishing claim is included. -/
structure AwaySevenBaseTerminalIntegerEquationCarryPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type where
  fstCarry : ℤ
  sndCarry : ℤ
  fstCarry_eq :
    seventhPowerFst signed.model.u signed.model.v -
        cyclotomicSevenFst signed.model.z signed.model.y =
      family.combinedModulus * fstCarry
  sndCarry_eq :
    seventhPowerSnd signed.model.u signed.model.v -
        cyclotomicSevenSnd signed.model.z signed.model.y =
      family.combinedModulus * sndCarry

/-- Extract the two integer equation carries from the global modular
coordinate equations. -/
noncomputable def
    AwaySevenBaseTerminalSignedRepresentativePacket.integerEquationCarryPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwaySevenBaseTerminalIntegerEquationCarryPacket signed := by
  let fstDefect :=
    seventhPowerFst signed.model.u signed.model.v -
      cyclotomicSevenFst signed.model.z signed.model.y
  let sndDefect :=
    seventhPowerSnd signed.model.u signed.model.v -
      cyclotomicSevenSnd signed.model.z signed.model.y
  have hequations := candidate.globalCoordinateEquations
  have hfstZero :
      (fstDefect : ZMod family.combinedModulus) = 0 := by
    have h := hequations.fstEquation
    rw [← signed.model_cast] at h
    simpa [fstDefect, AwayRoutingCoordinates.map, seventhPowerFstR,
      cyclotomicSevenFstR, seventhPowerFst, cyclotomicSevenFst,
      sub_eq_zero] using h
  have hsndZero :
      (sndDefect : ZMod family.combinedModulus) = 0 := by
    have h := hequations.sndEquation
    rw [← signed.model_cast] at h
    simpa [sndDefect, AwayRoutingCoordinates.map, seventhPowerSndR,
      cyclotomicSevenSndR, seventhPowerSnd, cyclotomicSevenSnd,
      sub_eq_zero] using h
  have hfstDvd : (family.combinedModulus : ℤ) ∣ fstDefect := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsndDvd : (family.combinedModulus : ℤ) ∣ sndDefect := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  let fstCarry := Classical.choose hfstDvd
  let sndCarry := Classical.choose hsndDvd
  exact {
    fstCarry := fstCarry
    sndCarry := sndCarry
    fstCarry_eq := Classical.choose_spec hfstDvd
    sndCarry_eq := Classical.choose_spec hsndDvd }

end DkMath.FLT.Seven
