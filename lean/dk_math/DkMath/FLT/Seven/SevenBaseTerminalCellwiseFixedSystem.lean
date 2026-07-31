/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalCellwiseCRTDecision

#print "file: DkMath.FLT.Seven.SevenBaseTerminalCellwiseFixedSystem"

namespace DkMath.FLT.Seven

private theorem intCast_zero_of_dvd' {M : ℕ} {a : ℤ}
    (h : (M : ℤ) ∣ a) : (a : ZMod M) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd a M).2 h

private theorem intCast_isUnit_of_natAbs_coprime {M : ℕ} {a : ℤ}
    (h : Nat.Coprime a.natAbs M) : IsUnit (a : ZMod M) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
  simpa using h.symm

private theorem natCast_isUnit_of_coprime {M a : ℕ}
    (h : Nat.Coprime a M) : IsUnit (a : ZMod M) := by
  rwa [ZMod.isUnit_iff_coprime]

/-- A whole terminal cell divides its corresponding original endpoint factor.
The carrier row uses `selected endpoint = 7 * carrierUnit`. -/
theorem
    AwaySevenBaseTerminalRoutingPacket.routingCell_dvd_originalEndpointFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    awaySevenBaseTerminalRoutingCell packet coordinate ∣
      endpointRoutingFactorNat y z
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row) := by
  rcases coordinate with ⟨row, column⟩
  have hfactor :
      awaySevenBaseTerminalRoutingCell packet ⟨row, column⟩ ∣
        awaySevenBaseTerminalFactorRowValue packet row := by
    cases row <;> cases column <;>
      simp only [awaySevenBaseTerminalRoutingCell,
        awaySevenBaseTerminalFactorRowValue]
    · exact packet.routing.c11_dvd_row1
    · exact packet.routing.c12_dvd_row1
    · exact packet.routing.c13_dvd_row1
    · exact packet.routing.c21_dvd_row2
    · exact packet.routing.c22_dvd_row2
    · exact packet.routing.c23_dvd_row2
    · exact packet.routing.c31_dvd_row3
    · exact packet.routing.c32_dvd_row3
    · exact packet.routing.c33_dvd_row3
  cases row with
  | carrier =>
      have hselected :
          awaySevenBaseTerminalRoutingCell packet ⟨.carrier, column⟩ ∣
            endpointRoutingFactorNat y z p.row := by
        rw [packet.core.carrier.carrier_eq]
        exact dvd_mul_of_dvd_right hfactor 7
      cases hrow : p.row <;>
        simpa [awaySevenBaseTerminalOriginalEndpointRow, hrow] using hselected
  | unselected =>
      cases hrow : p.row <;>
        simpa [awaySevenBaseTerminalOriginalEndpointRow,
          awaySevenBaseTerminalFactorRowValue,
          awaySevenBaseTerminalUnselectedEndpointNat,
          endpointRoutingFactorNat, hrow] using hfactor
  | companion =>
      cases hrow : p.row <;>
        simpa [awaySevenBaseTerminalOriginalEndpointRow,
          awaySevenBaseTerminalFactorRowValue,
          awaySevenBaseTerminalCompanionEndpointNat,
          endpointRoutingFactorNat, hrow] using hfactor

/-- A whole terminal cell divides its exact terminal root-column factor. -/
theorem AwaySevenBaseTerminalRoutingPacket.routingCell_dvd_terminalRootFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    awaySevenBaseTerminalRoutingCell packet coordinate ∣
      match coordinate.column with
      | .vPart => r.cubic.rootTriple.vPart
      | .leftPart => r.cubic.rootTriple.leftPart
      | .rightPart => r.cubic.rootTriple.rightPart := by
  rcases coordinate with ⟨row, column⟩
  cases row <;> cases column <;>
    simp only [awaySevenBaseTerminalRoutingCell]
  · exact packet.routing.c11_dvd_col1
  · exact packet.routing.c12_dvd_col2
  · exact packet.routing.c13_dvd_col3
  · exact packet.routing.c21_dvd_col1
  · exact packet.routing.c22_dvd_col2
  · exact packet.routing.c23_dvd_col3
  · exact packet.routing.c31_dvd_col1
  · exact packet.routing.c32_dvd_col2
  · exact packet.routing.c33_dvd_col3

/-- The universal first-coordinate equation decodes to every one of the nine
fixed endpoint-row/root-column equations. -/
theorem AwayFirstCoordinatePrimePowerEquation.of_universal
    {M : ℕ} (row : EndpointRoutingRow) (column : RootRoutingColumn)
    {u v y z : ZMod M}
    (hend : AwayEndpointPrimePowerEquation M row y z)
    (hroot : AwayRootPrimePowerEquation M column u v)
    (hfst : seventhPowerFstR u v = cyclotomicSevenFstR z y) :
    AwayFirstCoordinatePrimePowerEquation M row column u v y z := by
  have hleft :
      seventhPowerFstR u v =
        leftCubicZMod u v *
            (u ^ 4 + 2 * u ^ 3 * v - 37 * u ^ 2 * v ^ 2 -
              143 * u * v ^ 3 - 255 * v ^ 4) -
          49 * v ^ 5 * leftCorrectionZMod u v := by
    simp [seventhPowerFstR, leftCubicZMod, leftCorrectionZMod]
    ring
  have hright :
      seventhPowerFstR u v =
        rightCubicZMod u v *
            (u ^ 4 - 5 * u ^ 3 * v - 23 * u ^ 2 * v ^ 2 +
              74 * u * v ^ 3 - 157 * v ^ 4) +
          49 * v ^ 5 * rightCorrectionZMod u v := by
    simp [seventhPowerFstR, rightCubicZMod, rightCorrectionZMod]
    ring
  cases row <;> cases column
  all_goals
    simp only [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation,
      AwayRootPrimePowerEquation, AwayRootLocalEquation,
      AwayFirstCoordinatePrimePowerEquation,
      AwayFirstCoordinateLocalEquation] at hend hroot ⊢
  · apply sub_eq_zero.mpr
    simpa [hroot, hend, seventhPowerFstR, cyclotomicSevenFstR] using hfst
  · rw [hroot, zero_mul, zero_sub] at hleft
    simp [hend, cyclotomicSevenFstR, hleft] at hfst
    linear_combination -hfst
  · rw [hroot, zero_mul, zero_add] at hright
    simp [hend, cyclotomicSevenFstR, hright] at hfst
    linear_combination -hfst
  · simp [hroot, hend, seventhPowerFstR, cyclotomicSevenFstR] at hfst
    linear_combination hfst
  · rw [hroot, zero_mul, zero_sub] at hleft
    simp [hend, cyclotomicSevenFstR, hleft] at hfst
    linear_combination hfst
  · rw [hroot, zero_mul, zero_add] at hright
    simp [hend, cyclotomicSevenFstR, hright] at hfst
    linear_combination hfst
  · have hz : z = -y := by linear_combination hend
    simp [hroot, hz, seventhPowerFstR, cyclotomicSevenFstR] at hfst
    linear_combination hfst
  · have hz : z = -y := by linear_combination hend
    rw [hroot, zero_mul, zero_sub] at hleft
    simp [hz, cyclotomicSevenFstR, hleft] at hfst
    linear_combination -hfst
  · have hz : z = -y := by linear_combination hend
    rw [hroot, zero_mul, zero_add] at hright
    simp [hz, cyclotomicSevenFstR, hright] at hfst
    linear_combination hfst

/-- The weighted cell coordinates satisfy the universal first equation. -/
theorem
    AwaySevenBaseTerminalCellwiseCRTUniversalSolutionPacket.weighted_fstEquation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    {coordinate : AwaySevenBaseTerminalCellCoordinate}
    (cell :
      AwaySevenBaseTerminalCellwiseCRTUniversalSolutionPacket
        candidate coordinate) :
    seventhPowerFstR cell.weighted.u cell.weighted.v =
      cyclotomicSevenFstR cell.weighted.z cell.weighted.y := by
  rw [cell.weighted_eq]
  simp only [AwayRoutingCoordinates.weightedScale]
  rw [seventhPowerFstR_weighted, cyclotomicSevenFstR_weighted,
    cell.fstEquation]

/-- Original integral coordinates form a fixed-system solution modulo the
whole composite terminal-cell value. -/
noncomputable def
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket.cellwiseOriginalActualSolution
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    AwayRoutingPrimePowerSolution
      (awaySevenBaseTerminalRoutingCell packet coordinate)
      (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
      (awaySevenBaseTerminalOriginalRootColumn coordinate.column) := by
  let cell := candidate.cellwiseCRTUniversalSolution coordinate
  let M := cell.cellModulus
  have hM : M = awaySevenBaseTerminalRoutingCell packet coordinate := by
    simpa [M] using cell.cellModulus_eq
  have hendpoint :
      M ∣ endpointRoutingFactorNat y z
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row) := by
    rw [hM]
    exact packet.routingCell_dvd_originalEndpointFactor coordinate
  have hroot :
      M ∣ match coordinate.column with
        | .vPart => r.cubic.rootTriple.vPart
        | .leftPart => r.cubic.rootTriple.leftPart
        | .rightPart => r.cubic.rootTriple.rightPart := by
    rw [hM]
    exact packet.routingCell_dvd_terminalRootFactor coordinate
  have hweighted := cell.weighted_eq_original
  have hfst := cell.weighted_fstEquation
  rw [← hM]
  refine {
    u := cell.weighted.u
    v := cell.weighted.v
    y := cell.weighted.y
    z := cell.weighted.z
    endpoint_nondegenerate := ?_
    endpoint_equation := ?_
    root_nondegenerate := ?_
    root_equation := ?_
    first_coordinate_equation := ?_ }
  · rw [hweighted]
    cases hrow :
        awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row
    · exact natCast_isUnit_of_coprime
        (Nat.Coprime.of_dvd_right
          (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
          r.endpoint_y_z_coprime.symm)
    · exact natCast_isUnit_of_coprime
        (Nat.Coprime.of_dvd_right
          (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
          r.endpoint_y_z_coprime)
    · exact ⟨natCast_isUnit_of_coprime
          (Nat.Coprime.of_dvd_right
            (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
            r.endpoint_y_sum_coprime),
        natCast_isUnit_of_coprime
          (Nat.Coprime.of_dvd_right
            (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
            r.endpoint_z_sum_coprime)⟩
  · rw [hweighted]
    cases hrow :
        awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row
    · exact (ZMod.natCast_eq_zero_iff y M).2
            (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
    · exact (ZMod.natCast_eq_zero_iff z M).2
            (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
    · have hzero := (ZMod.natCast_eq_zero_iff (y + z) M).2
          (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
      simpa [M, awaySevenBaseTerminalOriginalCoordinates,
        AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation,
        Nat.cast_add] using hzero
  · rw [hweighted]
    rcases coordinate with ⟨row, column⟩
    cases column
    · apply intCast_isUnit_of_natAbs_coprime
      exact Nat.Coprime.of_dvd_right
        (by simpa [r.cubic.rootTriple.vPart_eq] using hroot)
        r.cubic.rootTriple.normal.root_coordinates_natAbs_coprime
    · apply intCast_isUnit_of_natAbs_coprime
      rw [← r.cubic.rootTriple.vPart_eq]
      exact Nat.Coprime.of_dvd_right
        (by simpa using hroot) r.cubic.rootTriple.coprime_v_left
    · apply intCast_isUnit_of_natAbs_coprime
      rw [← r.cubic.rootTriple.vPart_eq]
      exact Nat.Coprime.of_dvd_right
        (by simpa using hroot) r.cubic.rootTriple.coprime_v_right
  · rw [hweighted]
    rcases coordinate with ⟨row, column⟩
    cases column
    · apply intCast_zero_of_dvd'
      apply intCast_dvd_of_dvd_natAbs
      simpa [← r.cubic.rootTriple.vPart_eq] using hroot
    · have hi : (M : ℤ) ∣ seventhPowerSndLeftCubic
          r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd := by
        apply intCast_dvd_of_dvd_natAbs
        simpa [← r.cubic.rootTriple.leftPart_eq] using hroot
      simpa [M,
        awaySevenBaseTerminalOriginalRootColumn,
        awaySevenBaseTerminalOriginalCoordinates, AwayRootPrimePowerEquation,
        AwayRootLocalEquation,
        leftCubicZMod, seventhPowerSndLeftCubic] using
        intCast_zero_of_dvd' hi
    · have hi : (M : ℤ) ∣ seventhPowerSndRightCubic
          r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd := by
        apply intCast_dvd_of_dvd_natAbs
        simpa [← r.cubic.rootTriple.rightPart_eq] using hroot
      simpa [M,
        awaySevenBaseTerminalOriginalRootColumn,
        awaySevenBaseTerminalOriginalCoordinates, AwayRootPrimePowerEquation,
        AwayRootLocalEquation,
        rightCubicZMod, seventhPowerSndRightCubic] using
        intCast_zero_of_dvd' hi
  · exact AwayFirstCoordinatePrimePowerEquation.of_universal _ _
      (by
        rw [hweighted]
        cases hrow :
            awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row
        · exact (ZMod.natCast_eq_zero_iff y M).2
            (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
        · exact (ZMod.natCast_eq_zero_iff z M).2
            (by simpa [hrow, endpointRoutingFactorNat] using hendpoint)
        · have hzero := (ZMod.natCast_eq_zero_iff (y + z) M).2 (by
            simpa [hrow, endpointRoutingFactorNat] using hendpoint)
          simpa [M,
            awaySevenBaseTerminalOriginalCoordinates,
            AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation,
            Nat.cast_add] using hzero)
      (by
        rw [hweighted]
        rcases coordinate with ⟨row, column⟩
        cases column
        · apply intCast_zero_of_dvd'
          apply intCast_dvd_of_dvd_natAbs
          simpa [← r.cubic.rootTriple.vPart_eq] using hroot
        · have hi : (M : ℤ) ∣ seventhPowerSndLeftCubic
              r.cubic.rootTriple.normal.root.fst
              r.cubic.rootTriple.normal.root.snd := by
            apply intCast_dvd_of_dvd_natAbs
            simpa [M,
              ← r.cubic.rootTriple.leftPart_eq] using hroot
          simpa [M, awaySevenBaseTerminalOriginalRootColumn,
            awaySevenBaseTerminalOriginalCoordinates, AwayRootPrimePowerEquation,
            AwayRootLocalEquation,
            leftCubicZMod, seventhPowerSndLeftCubic] using
            intCast_zero_of_dvd' hi
        · have hi : (M : ℤ) ∣ seventhPowerSndRightCubic
              r.cubic.rootTriple.normal.root.fst
              r.cubic.rootTriple.normal.root.snd := by
            apply intCast_dvd_of_dvd_natAbs
            simpa [M,
              ← r.cubic.rootTriple.rightPart_eq] using hroot
          simpa [M, awaySevenBaseTerminalOriginalRootColumn,
            awaySevenBaseTerminalOriginalCoordinates, AwayRootPrimePowerEquation,
            AwayRootLocalEquation,
            rightCubicZMod, seventhPowerSndRightCubic] using
            intCast_zero_of_dvd' hi)
      hfst

/-- Inverse weighted action by a unit scale. -/
noncomputable def unscalePrimePowerSolution
    {M : ℕ} {row : EndpointRoutingRow} {column : RootRoutingColumn}
    (a : AwayRoutingPrimePowerSolution M row column)
    (scale : ZMod M) (scale_isUnit : IsUnit scale) :
    AwayRoutingPrimePowerSolution M row column :=
  scalePrimePowerSolution a
    (↑scale_isUnit.unit⁻¹ : ZMod M) (Units.isUnit _)

private theorem weighted_unscale_cancel {M n : ℕ}
    (a scale : ZMod M) (scale_isUnit : IsUnit scale) :
    a * scale ^ n * (↑scale_isUnit.unit⁻¹ : ZMod M) ^ n = a := by
  calc
    a * scale ^ n * (↑scale_isUnit.unit⁻¹ : ZMod M) ^ n =
        a * (scale * (↑scale_isUnit.unit⁻¹ : ZMod M)) ^ n := by ring
    _ = a := by rw [scale_isUnit.mul_val_inv]; simp

/-- Scaling by the inverse unit recovers the unweighted model coordinates. -/
theorem unscalePrimePowerSolution_toCoordinates
    {M : ℕ} {row : EndpointRoutingRow} {column : RootRoutingColumn}
    (actual : AwayRoutingPrimePowerSolution M row column)
    (model : AwayRoutingCoordinates (ZMod M))
    (scale : ZMod M) (scale_isUnit : IsUnit scale)
    (hcoordinates :
      actual.toCoordinates = model.weightedScale scale) :
    (unscalePrimePowerSolution actual scale scale_isUnit).toCoordinates =
      model := by
  apply AwayRoutingCoordinates.ext
  · have h := congrArg AwayRoutingCoordinates.u hcoordinates
    simp only [AwayRoutingCoordinates.weightedScale,
      AwayRoutingPrimePowerSolution.toCoordinates] at h ⊢
    simp only [unscalePrimePowerSolution, scalePrimePowerSolution]
    rw [h]
    exact weighted_unscale_cancel model.u scale scale_isUnit
  · have h := congrArg AwayRoutingCoordinates.v hcoordinates
    simp only [AwayRoutingCoordinates.weightedScale,
      AwayRoutingPrimePowerSolution.toCoordinates] at h ⊢
    simp only [unscalePrimePowerSolution, scalePrimePowerSolution]
    rw [h]
    exact weighted_unscale_cancel model.v scale scale_isUnit
  · have h := congrArg AwayRoutingCoordinates.y hcoordinates
    simp only [AwayRoutingCoordinates.weightedScale,
      AwayRoutingPrimePowerSolution.toCoordinates] at h ⊢
    simp only [unscalePrimePowerSolution, scalePrimePowerSolution]
    rw [h]
    exact weighted_unscale_cancel model.y scale scale_isUnit
  · have h := congrArg AwayRoutingCoordinates.z hcoordinates
    simp only [AwayRoutingCoordinates.weightedScale,
      AwayRoutingPrimePowerSolution.toCoordinates] at h ⊢
    simp only [unscalePrimePowerSolution, scalePrimePowerSolution]
    rw [h]
    exact weighted_unscale_cancel model.z scale scale_isUnit

/-- TERM-007 closes the fixed-system compatibility obligation for every cell. -/
theorem
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket.cellwiseFixedSystemObligation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family) :
    AwaySevenBaseTerminalCellwiseFixedSystemObligation candidate := by
  intro coordinate
  let cell := candidate.cellwiseCRTUniversalSolution coordinate
  let actual := candidate.cellwiseOriginalActualSolution coordinate
  let solution :=
    unscalePrimePowerSolution actual cell.scale cell.scale_isUnit
  refine ⟨solution, ?_⟩
  apply unscalePrimePowerSolution_toCoordinates
  change actual.toCoordinates = cell.model.weightedScale cell.scale
  calc
    actual.toCoordinates = cell.weighted := rfl
    _ = cell.model.weightedScale cell.scale := cell.weighted_eq

end DkMath.FLT.Seven
