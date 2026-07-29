/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalCellwiseFixedSystem

#print "file: DkMath.FLT.Seven.SevenBaseTerminalCellCarryDependency"

namespace DkMath.FLT.Seven

/-- Endpoint equation as an integer residual. -/
def AwayEndpointIntegerResidual
    (row : EndpointRoutingRow) (y z : ℤ) : ℤ :=
  match row with
  | .y => y
  | .z => z
  | .sum => y + z

/-- Root equation as an integer residual. -/
def AwayRootIntegerResidual
    (column : RootRoutingColumn) (u v : ℤ) : ℤ :=
  match column with
  | .sevenV => v
  | .leftCubic => seventhPowerSndLeftCubic u v
  | .rightCubic => seventhPowerSndRightCubic u v

/-- The nine fixed first-coordinate equations as integer residuals. -/
def AwayFirstCoordinateIntegerResidual
    (row : EndpointRoutingRow) (column : RootRoutingColumn)
    (u v y z : ℤ) : ℤ :=
  match row, column with
  | .y, .sevenV => u ^ 7 - z ^ 3
  | .z, .sevenV => u ^ 7 + y ^ 3
  | .sum, .sevenV => u ^ 7 + y ^ 3
  | .y, .leftCubic =>
      z ^ 3 + 49 * v ^ 5 * leftFstCorrection u v
  | .z, .leftCubic =>
      49 * v ^ 5 * leftFstCorrection u v - y ^ 3
  | .sum, .leftCubic =>
      49 * v ^ 5 * leftFstCorrection u v - y ^ 3
  | .y, .rightCubic =>
      z ^ 3 - 49 * v ^ 5 * rightFstCorrection u v
  | .z, .rightCubic =>
      y ^ 3 + 49 * v ^ 5 * rightFstCorrection u v
  | .sum, .rightCubic =>
      y ^ 3 + 49 * v ^ 5 * rightFstCorrection u v

/-- Universal first-coordinate equation as an integer residual. -/
def AwayUniversalFstIntegerResidual (u v y z : ℤ) : ℤ :=
  seventhPowerFst u v - cyclotomicSevenFst z y

/-- Sign with which the universal residual enters a fixed first equation. -/
def awayFixedUniversalSign
    (row : EndpointRoutingRow) (column : RootRoutingColumn) : ℤ :=
  match column with
  | .sevenV => 1
  | .leftCubic => -1
  | .rightCubic =>
      match row with
      | .y => -1
      | .z | .sum => 1

/-- Quotient in the endpoint specialization of the cyclotomic first
coordinate. -/
def awayFixedEndpointQuotient
    (row : EndpointRoutingRow) (y z : ℤ) : ℤ :=
  match row with
  | .y => (z - y) * (z + y)
  | .z => z * (z + y)
  | .sum => z ^ 2

/-- Quotient in the root specialization of the seventh-power first
coordinate. -/
def awayFixedRootQuotient
    (column : RootRoutingColumn) (u v : ℤ) : ℤ :=
  match column with
  | .sevenV => v * seventhPowerFstVResidual u v
  | .leftCubic => leftFstQuotient u v
  | .rightCubic => rightFstQuotient u v

/-- Endpoint-residual coefficient in the fixed first-residual decomposition. -/
def awayFixedEndpointCoefficient
    (row : EndpointRoutingRow) (column : RootRoutingColumn)
    (y z : ℤ) : ℤ :=
  awayFixedUniversalSign row column *
    awayFixedEndpointQuotient row y z

/-- Root-residual coefficient in the fixed first-residual decomposition. -/
def awayFixedRootCoefficient
    (row : EndpointRoutingRow) (column : RootRoutingColumn)
    (u v : ℤ) : ℤ :=
  -awayFixedUniversalSign row column *
    awayFixedRootQuotient column u v

/-- Exact dependency of every fixed first residual on the universal,
endpoint, and root residuals. -/
theorem fixedFirstResidual_decomposition
    (row : EndpointRoutingRow) (column : RootRoutingColumn)
    (u v y z : ℤ) :
    AwayFirstCoordinateIntegerResidual row column u v y z =
      awayFixedUniversalSign row column *
          AwayUniversalFstIntegerResidual u v y z +
        awayFixedEndpointCoefficient row column y z *
          AwayEndpointIntegerResidual row y z +
        awayFixedRootCoefficient row column u v *
          AwayRootIntegerResidual column u v := by
  cases row <;> cases column <;>
    simp [AwayFirstCoordinateIntegerResidual,
      AwayUniversalFstIntegerResidual, AwayEndpointIntegerResidual,
      AwayRootIntegerResidual, awayFixedUniversalSign,
      awayFixedEndpointCoefficient, awayFixedEndpointQuotient,
      awayFixedRootCoefficient, awayFixedRootQuotient,
      seventhPowerFst, cyclotomicSevenFst,
      seventhPowerFstVResidual, seventhPowerSndLeftCubic,
      seventhPowerSndRightCubic, leftFstCorrection,
      rightFstCorrection, leftFstQuotient, rightFstQuotient] <;>
    ring

/-- The common full-modulus signed model casts to the reduced model at every
whole terminal cell. -/
theorem AwaySevenBaseTerminalSignedRepresentativePacket.signedModel_cast_cell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    signed.model.map
        (fun a : ℤ =>
          (a : ZMod
            (awaySevenBaseTerminalRoutingCell packet coordinate))) =
      (candidate.cellwiseCRTUniversalSolution coordinate).model := by
  let reduction := awaySevenBaseTerminalCellReductionHom family coordinate
  change signed.model.map
      (fun a : ℤ =>
        (a : ZMod
          (awaySevenBaseTerminalRoutingCell packet coordinate))) =
    candidate.model.globalModel.map reduction
  have h := congrArg
    (fun coordinates => coordinates.map reduction) signed.model_cast
  simpa [reduction, awaySevenBaseTerminalCellReductionHom,
    AwayRoutingCoordinates.map, ZMod.castHom_apply] using h

private theorem signedModel_cell_component_equalities
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (coordinate : AwaySevenBaseTerminalCellCoordinate)
    (solution :
      AwayRoutingPrimePowerSolution
        (awaySevenBaseTerminalRoutingCell packet coordinate)
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
        (awaySevenBaseTerminalOriginalRootColumn coordinate.column))
    (hsolution :
      solution.toCoordinates =
        (candidate.cellwiseCRTUniversalSolution coordinate).model) :
    (signed.model.u :
        ZMod (awaySevenBaseTerminalRoutingCell packet coordinate)) =
        solution.u ∧
      (signed.model.v :
        ZMod (awaySevenBaseTerminalRoutingCell packet coordinate)) =
        solution.v ∧
      (signed.model.y :
        ZMod (awaySevenBaseTerminalRoutingCell packet coordinate)) =
        solution.y ∧
      (signed.model.z :
        ZMod (awaySevenBaseTerminalRoutingCell packet coordinate)) =
        solution.z := by
  have hcoordinates :=
    (signed.signedModel_cast_cell coordinate).trans hsolution.symm
  exact ⟨congrArg AwayRoutingCoordinates.u hcoordinates,
    congrArg AwayRoutingCoordinates.v hcoordinates,
    congrArg AwayRoutingCoordinates.y hcoordinates,
    congrArg AwayRoutingCoordinates.z hcoordinates⟩

private theorem endpointResidual_cast_eq_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    (AwayEndpointIntegerResidual
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
        signed.model.y signed.model.z :
      ZMod (awaySevenBaseTerminalRoutingCell packet coordinate)) = 0 := by
  rcases candidate.cellwiseFixedSystemObligation coordinate with
    ⟨solution, hsolution⟩
  rcases signedModel_cell_component_equalities
      signed coordinate solution hsolution with ⟨_, _, hy, hz⟩
  have heq := solution.endpoint_equation
  cases hrow :
      awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row
  · simpa [AwayEndpointIntegerResidual, hrow,
      AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation, hy] using heq
  · simpa [AwayEndpointIntegerResidual, hrow,
      AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation, hz] using heq
  · simpa [AwayEndpointIntegerResidual, hrow,
      AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation,
      Int.cast_add, hy, hz] using heq

private theorem rootResidual_cast_eq_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    (AwayRootIntegerResidual
        (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
        signed.model.u signed.model.v :
      ZMod (awaySevenBaseTerminalRoutingCell packet coordinate)) = 0 := by
  rcases candidate.cellwiseFixedSystemObligation coordinate with
    ⟨solution, hsolution⟩
  rcases signedModel_cell_component_equalities
      signed coordinate solution hsolution with ⟨hu, hv, _, _⟩
  have heq := solution.root_equation
  cases hcolumn :
      awaySevenBaseTerminalOriginalRootColumn coordinate.column
  · simpa [AwayRootIntegerResidual, hcolumn,
      AwayRootPrimePowerEquation, AwayRootLocalEquation, hv] using heq
  · simpa [AwayRootIntegerResidual, hcolumn,
      AwayRootPrimePowerEquation, AwayRootLocalEquation,
      leftCubicZMod, seventhPowerSndLeftCubic, hu, hv] using heq
  · simpa [AwayRootIntegerResidual, hcolumn,
      AwayRootPrimePowerEquation, AwayRootLocalEquation,
      rightCubicZMod, seventhPowerSndRightCubic, hu, hv] using heq

private theorem firstResidual_cast_eq_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    (AwayFirstCoordinateIntegerResidual
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
        (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
        signed.model.u signed.model.v signed.model.y signed.model.z :
      ZMod (awaySevenBaseTerminalRoutingCell packet coordinate)) = 0 := by
  rcases candidate.cellwiseFixedSystemObligation coordinate with
    ⟨solution, hsolution⟩
  rcases signedModel_cell_component_equalities
      signed coordinate solution hsolution with ⟨hu, hv, hy, hz⟩
  have heq := solution.first_coordinate_equation
  cases hrow :
      awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row <;>
    cases hcolumn :
      awaySevenBaseTerminalOriginalRootColumn coordinate.column <;>
    simpa [AwayFirstCoordinateIntegerResidual, hrow, hcolumn,
      AwayFirstCoordinatePrimePowerEquation,
      AwayFirstCoordinateLocalEquation, leftCorrectionZMod,
      rightCorrectionZMod, leftFstCorrection, rightFstCorrection,
      hu, hv, hy, hz] using heq

/-- Three exact integer carries for one fixed composite terminal cell, all
using the common full-modulus signed model representatives. -/
structure AwaySevenBaseTerminalCellIntegerCarryPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) : Type where
  modulus : ℕ
  modulus_eq :
    modulus = awaySevenBaseTerminalRoutingCell packet coordinate
  fullModulusQuotient : ℕ
  fullModulus_eq :
    family.combinedModulus = modulus * fullModulusQuotient
  endpointCarry : ℤ
  rootCarry : ℤ
  firstCarry : ℤ
  endpoint_eq :
    AwayEndpointIntegerResidual
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
        signed.model.y signed.model.z =
      modulus * endpointCarry
  root_eq :
    AwayRootIntegerResidual
        (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
        signed.model.u signed.model.v =
      modulus * rootCarry
  first_eq :
    AwayFirstCoordinateIntegerResidual
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
        (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
        signed.model.u signed.model.v signed.model.y signed.model.z =
      modulus * firstCarry

/-- Extract all three cell carries from the proved fixed-system solution. -/
noncomputable def
    AwaySevenBaseTerminalSignedRepresentativePacket.cellIntegerCarryPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    AwaySevenBaseTerminalCellIntegerCarryPacket signed coordinate := by
  let modulus := awaySevenBaseTerminalRoutingCell packet coordinate
  let endpointResidual :=
    AwayEndpointIntegerResidual
      (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
      signed.model.y signed.model.z
  let rootResidual :=
    AwayRootIntegerResidual
      (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
      signed.model.u signed.model.v
  let firstResidual :=
    AwayFirstCoordinateIntegerResidual
      (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
      (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
      signed.model.u signed.model.v signed.model.y signed.model.z
  have hfullDvd : modulus ∣ family.combinedModulus := by
    rw [family.combinedModulus_eq_cubicRootLoad]
    exact packet.routingCell_dvd_cubicRootLoad coordinate
  have hendpointDvd : (modulus : ℤ) ∣ endpointResidual := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact endpointResidual_cast_eq_zero signed coordinate
  have hrootDvd : (modulus : ℤ) ∣ rootResidual := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact rootResidual_cast_eq_zero signed coordinate
  have hfirstDvd : (modulus : ℤ) ∣ firstResidual := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact firstResidual_cast_eq_zero signed coordinate
  exact {
    modulus := modulus
    modulus_eq := rfl
    fullModulusQuotient := Classical.choose hfullDvd
    fullModulus_eq := Classical.choose_spec hfullDvd
    endpointCarry := Classical.choose hendpointDvd
    rootCarry := Classical.choose hrootDvd
    firstCarry := Classical.choose hfirstDvd
    endpoint_eq := Classical.choose_spec hendpointDvd
    root_eq := Classical.choose_spec hrootDvd
    first_eq := Classical.choose_spec hfirstDvd }

/-- TERM-008 dependency audit: a cell first carry is completely determined by
the global universal carry and the endpoint/root carries of that cell. -/
theorem AwaySevenBaseTerminalCellIntegerCarryPacket.firstCarry_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    {signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate}
    {coordinate : AwaySevenBaseTerminalCellCoordinate}
    (cell : AwaySevenBaseTerminalCellIntegerCarryPacket signed coordinate)
    (global : AwaySevenBaseTerminalIntegerEquationCarryPacket signed) :
    cell.firstCarry =
      awayFixedUniversalSign
          (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
          (awaySevenBaseTerminalOriginalRootColumn coordinate.column) *
        cell.fullModulusQuotient * global.fstCarry +
      awayFixedEndpointCoefficient
          (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
          (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
          signed.model.y signed.model.z * cell.endpointCarry +
      awayFixedRootCoefficient
          (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
          (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
          signed.model.u signed.model.v * cell.rootCarry := by
  have hmodulus :
      (cell.modulus : ℤ) ≠ 0 := by
    rw [cell.modulus_eq]
    exact_mod_cast packet.routingCell_ne_zero coordinate
  apply mul_left_cancel₀ hmodulus
  rw [← cell.first_eq]
  rw [fixedFirstResidual_decomposition]
  simp only [AwayUniversalFstIntegerResidual]
  rw [global.fstCarry_eq, cell.endpoint_eq, cell.root_eq]
  have hfullModulus :
      (family.combinedModulus : ℤ) =
        (cell.modulus : ℤ) * cell.fullModulusQuotient := by
    exact_mod_cast cell.fullModulus_eq
  rw [hfullModulus]
  ring

/-- All nine cell carry packets with their proved first-carry dependency. -/
structure AwaySevenBaseTerminalCellCarryDependencyAuditPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type where
  cells :
    ∀ coordinate,
      AwaySevenBaseTerminalCellIntegerCarryPacket signed coordinate
  firstCarry_dependency :
    ∀ coordinate,
      (cells coordinate).firstCarry =
        awayFixedUniversalSign
            (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
            (awaySevenBaseTerminalOriginalRootColumn coordinate.column) *
          (cells coordinate).fullModulusQuotient *
            signed.integerEquationCarryPacket.fstCarry +
        awayFixedEndpointCoefficient
            (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
            (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
            signed.model.y signed.model.z *
              (cells coordinate).endpointCarry +
        awayFixedRootCoefficient
            (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
            (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
            signed.model.u signed.model.v *
              (cells coordinate).rootCarry

/-- Assemble the TERM-008 dependency audit simultaneously over all nine
terminal cells. -/
noncomputable def
    AwaySevenBaseTerminalSignedRepresentativePacket.cellCarryDependencyAuditPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwaySevenBaseTerminalCellCarryDependencyAuditPacket signed := by
  let cells := signed.cellIntegerCarryPacket
  exact {
    cells := cells
    firstCarry_dependency := fun coordinate =>
      (cells coordinate).firstCarry_eq signed.integerEquationCarryPacket }

end DkMath.FLT.Seven
