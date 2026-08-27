/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalCellPrimePartition
import DkMath.FLT.Seven.SevenBaseTerminalExclusion

#print "file: DkMath.FLT.Seven.SevenBaseTerminalCellwiseCRTDecision"

namespace DkMath.FLT.Seven

/-- Reduction from the full CRT modulus to one exact terminal-cell modulus. -/
noncomputable def awaySevenBaseTerminalCellReductionHom
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    ZMod family.combinedModulus →+*
      ZMod (awaySevenBaseTerminalRoutingCell packet coordinate) :=
  ZMod.castHom
    (by
      rw [family.combinedModulus_eq_cubicRootLoad]
      exact packet.routingCell_dvd_cubicRootLoad coordinate)
    (ZMod (awaySevenBaseTerminalRoutingCell packet coordinate))

/-- TERM-006 cellwise CRT projection. The modulus is the exact prime-power
product of one fixed cell, and all global model, scale, and weighted data are
reduced to that quotient. Universal coordinate equations remain valid there. -/
structure AwaySevenBaseTerminalCellwiseCRTUniversalSolutionPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) : Type where
  cellModulus : ℕ
  cellModulus_eq :
    cellModulus = awaySevenBaseTerminalRoutingCell packet coordinate
  model : AwayRoutingCoordinates (ZMod cellModulus)
  scale : ZMod cellModulus
  scale_isUnit : IsUnit scale
  weighted : AwayRoutingCoordinates (ZMod cellModulus)
  weighted_eq : weighted = model.weightedScale scale
  weighted_eq_original :
    weighted =
      awaySevenBaseTerminalOriginalCoordinates r cellModulus
  fstEquation :
    seventhPowerFstR model.u model.v =
      cyclotomicSevenFstR model.z model.y
  sndEquation :
    seventhPowerSndR model.u model.v =
      cyclotomicSevenSndR model.z model.y
  primeSupport_fixed :
    ∀ q, q ∈ awaySevenBaseTerminalCellPrimeSupport packet coordinate →
      AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q

/-- Reduce the already reconstructed full CRT solution to one fixed cell. -/
noncomputable def
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket.cellwiseCRTUniversalSolution
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    AwaySevenBaseTerminalCellwiseCRTUniversalSolutionPacket
      candidate coordinate := by
  let reduction :=
    awaySevenBaseTerminalCellReductionHom family coordinate
  let model := candidate.model.globalModel.map reduction
  let scale := reduction candidate.scale.combinedScale
  let weighted := candidate.weighted.map reduction
  have hmodelEquations := candidate.globalCoordinateEquations
  refine {
    cellModulus := awaySevenBaseTerminalRoutingCell packet coordinate
    cellModulus_eq := rfl
    model := model
    scale := scale
    scale_isUnit := candidate.scale.combinedScale_isUnit.map reduction
    weighted := weighted
    weighted_eq := ?_
    weighted_eq_original := ?_
    fstEquation := ?_
    sndEquation := ?_
    primeSupport_fixed := ?_ }
  · dsimp [weighted, model, scale]
    rw [candidate.weighted_eq,
      AwayRoutingCoordinates.map_weightedScale]
  · dsimp [weighted]
    have h := congrArg
      (fun coordinates => coordinates.map reduction)
      candidate.weighted_eq_original
    simpa [reduction, awaySevenBaseTerminalCellReductionHom,
      AwayRoutingCoordinates.map,
      awaySevenBaseTerminalOriginalCoordinates, ZMod.castHom_apply] using h
  · have h := congrArg reduction hmodelEquations.fstEquation
    simp only [seventhPowerFstR, cyclotomicSevenFstR, map_sub,
      map_add, map_mul, map_pow, map_ofNat] at h
    simpa [model, AwayRoutingCoordinates.map, seventhPowerFstR,
      cyclotomicSevenFstR] using h
  · have h := congrArg reduction hmodelEquations.sndEquation
    simp only [seventhPowerSndR, cyclotomicSevenSndR, map_sub,
      map_add, map_mul, map_pow, map_neg, map_ofNat] at h
    simpa [model, AwayRoutingCoordinates.map, seventhPowerSndR,
      cyclotomicSevenSndR] using h
  · intro q hq
    exact (mem_awaySevenBaseTerminalCellPrimeSupport_iff.mp hq).2

/-- The still-missing strengthening from universal cell equations to the
row/column-specific prime-power system. This proposition is recorded rather
than assumed. -/
def AwaySevenBaseTerminalCellwiseFixedSystemObligation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family) :
    Prop :=
  ∀ coordinate : AwaySevenBaseTerminalCellCoordinate,
    ∃ solution :
        AwayRoutingPrimePowerSolution
        (awaySevenBaseTerminalRoutingCell packet coordinate)
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
        (awaySevenBaseTerminalOriginalRootColumn coordinate.column),
      solution.toCoordinates =
        (candidate.cellwiseCRTUniversalSolution coordinate).model

/-- All concrete TERM-006 inputs available before the final arithmetic
decision: nine cellwise CRT projections, coordinate windings, equation carries,
and the row-specific factorization of the full modulus. -/
structure AwaySevenBaseTerminalRowResolvedCarryPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type where
  cells :
    ∀ coordinate,
      AwaySevenBaseTerminalCellwiseCRTUniversalSolutionPacket
        candidate coordinate
  winding :
    AwaySevenBaseTerminalOriginalReconstructionWindingPacket signed
  equationCarry :
    AwaySevenBaseTerminalIntegerEquationCarryPacket signed
  rowWinding :
    AwaySevenBaseTerminalRowResolvedWindingPacket terminal signed

noncomputable def
    AwaySevenBaseTerminalSignedRepresentativePacket.rowResolvedCarryPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwaySevenBaseTerminalRowResolvedCarryPacket terminal signed where
  cells := candidate.cellwiseCRTUniversalSolution
  winding := signed.originalReconstructionWindingPacket
  equationCarry := signed.integerEquationCarryPacket
  rowWinding := signed.rowResolvedWindingPacket terminal

/-- Honest TERM-006 decision boundary. A later arithmetic theorem may close
the terminal branch or construct the full recursive descent provider; with the
present APIs the fixed-system strengthening remains explicit and open. -/
inductive AwaySevenBaseTerminalCarryDecision
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type
  | contradiction (eliminates : False)
  | descends
      (provider : AwayDescentClosureProvider x y z r.cubic.transfer)
  | open
      (carry : AwaySevenBaseTerminalRowResolvedCarryPacket terminal signed)
      (missingObligation : Prop)
      (missing_eq :
        missingObligation =
          AwaySevenBaseTerminalCellwiseFixedSystemObligation candidate)

/-- Current construction reaches the exact row-resolved carries and records,
without inhabiting, the remaining fixed-system proposition. -/
noncomputable def
    AwaySevenBaseTerminalSignedRepresentativePacket.carryDecisionOpen
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwaySevenBaseTerminalCarryDecision terminal signed :=
  .open (signed.rowResolvedCarryPacket terminal)
    (AwaySevenBaseTerminalCellwiseFixedSystemObligation candidate) rfl

end DkMath.FLT.Seven
