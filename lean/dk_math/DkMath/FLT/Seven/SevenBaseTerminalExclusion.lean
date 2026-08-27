/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalLiftedReconstruction
import DkMath.FLT.Seven.SevenBaseTerminalLoadDivisibility

#print "file: DkMath.FLT.Seven.SevenBaseTerminalExclusion"

namespace DkMath.FLT.Seven

/-- Exact arithmetic profile of the positive terminal `Y` row. -/
def AwaySevenBaseTerminalRowYProfile
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) : Prop :=
  p.row = .y ∧
  y = 7 * terminal.core.carrier.carrierUnit ∧
  terminal.unitSector.rootLinearUnit *
      (terminal.unitSector.endpointUnit ^ 3)⁻¹ = 1 ∧
  terminal.core.carrier.carrierUnit * z * (y + z) =
    r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
      r.cubic.rootTriple.rightPart

/-- Exact arithmetic profile of the negative terminal `Z` row. -/
def AwaySevenBaseTerminalRowZProfile
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) : Prop :=
  p.row = .z ∧
  z = 7 * terminal.core.carrier.carrierUnit ∧
  terminal.unitSector.rootLinearUnit *
      (terminal.unitSector.endpointUnit ^ 3)⁻¹ = -1 ∧
  y * terminal.core.carrier.carrierUnit * (y + z) =
    r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
      r.cubic.rootTriple.rightPart

/-- Exact arithmetic profile of the negative terminal `Sum` row. -/
def AwaySevenBaseTerminalRowSumProfile
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) : Prop :=
  p.row = .sum ∧
  y + z = 7 * terminal.core.carrier.carrierUnit ∧
  terminal.unitSector.rootLinearUnit *
      (terminal.unitSector.endpointUnit ^ 3)⁻¹ = -1 ∧
  y * z * terminal.core.carrier.carrierUnit =
    r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
      r.cubic.rootTriple.rightPart

/-- The terminal arithmetic remains in exactly one of the three explicit row
profiles. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.row_profile_decision
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    AwaySevenBaseTerminalRowYProfile terminal ∨
    AwaySevenBaseTerminalRowZProfile terminal ∨
    AwaySevenBaseTerminalRowSumProfile terminal := by
  exact terminal.row_resolved_complete_normal_form

/-- TERM-001 decision packet. It keeps the exact row branch together with the
signed reconstruction-versus-defect decision; neither axis is erased. -/
structure AwaySevenBaseTerminalRowSensitiveDecisionPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {routing :
      AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily routing}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type where
  rowProfile :
    AwaySevenBaseTerminalRowYProfile terminal ∨
    AwaySevenBaseTerminalRowZProfile terminal ∨
    AwaySevenBaseTerminalRowSumProfile terminal
  endpointQuotientNormalForm :
    (p.row = .y ∧
      cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3 =
        7 * ((terminal.core.carrier.carrierUnit : ℤ) *
          ((z : ℤ) - (y : ℤ)) * ((z : ℤ) + (y : ℤ)))) ∨
    (p.row = .z ∧
      cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 =
        7 * ((terminal.core.carrier.carrierUnit : ℤ) * (z : ℤ) *
          ((z : ℤ) + (y : ℤ)))) ∨
    (p.row = .sum ∧
      cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 =
        7 * ((terminal.core.carrier.carrierUnit : ℤ) * (z : ℤ) ^ 2))
  reconstruction :
    AwaySevenBaseTerminalSignedReconstructionOutcome signed

/-- Assemble the row-sensitive terminal decision from the exact quotient
normal forms and the LIFT-003 reconstruction outcome. -/
noncomputable def AwaySevenBaseTerminalSignedRepresentativePacket.rowSensitiveTerminalDecision
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {routing :
      AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily routing}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwaySevenBaseTerminalRowSensitiveDecisionPacket terminal signed where
  rowProfile := terminal.row_profile_decision
  endpointQuotientNormalForm :=
    terminal.row_resolved_endpoint_quotient_normal_form
  reconstruction := signed.signedReconstructionOutcome

/-- TERM-003 row-resolved winding data.  It keeps the exact four winding
witnesses together with the row-specific factorization of the full CRT
modulus.  No claim that a winding vanishes, or that a row is contradictory, is
made here. -/
structure AwaySevenBaseTerminalRowResolvedWindingPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {routing :
      AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily routing}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type where
  winding : AwaySevenBaseTerminalOriginalReconstructionWindingPacket signed
  rowModulusNormalForm :
    (AwaySevenBaseTerminalRowYProfile terminal ∧
      family.combinedModulus =
        terminal.core.carrier.carrierUnit * z * (y + z)) ∨
    (AwaySevenBaseTerminalRowZProfile terminal ∧
      family.combinedModulus =
        y * terminal.core.carrier.carrierUnit * (y + z)) ∨
    (AwaySevenBaseTerminalRowSumProfile terminal ∧
      family.combinedModulus =
        y * z * terminal.core.carrier.carrierUnit)

/-- Assemble the exact winding numbers with the corresponding terminal
factorization of the full cubic-root-load modulus. -/
noncomputable def
    AwaySevenBaseTerminalSignedRepresentativePacket.rowResolvedWindingPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {routing :
      AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily routing}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwaySevenBaseTerminalRowResolvedWindingPacket terminal signed := by
  refine {
    winding := signed.originalReconstructionWindingPacket
    rowModulusNormalForm := ?_ }
  rcases terminal.row_profile_decision with hy | hz | hs
  · left
    exact ⟨hy, family.combinedModulus_eq_cubicRootLoad.trans hy.2.2.2.symm⟩
  · right
    left
    exact ⟨hz, family.combinedModulus_eq_cubicRootLoad.trans hz.2.2.2.symm⟩
  · right
    right
    exact ⟨hs, family.combinedModulus_eq_cubicRootLoad.trans hs.2.2.2.symm⟩

/-- The strict coordinate bounds which turn the modular weighted identity into
an exact integer identity.  This is the first, independently reviewable,
arithmetic obligation left by TERM-002. -/
structure AwaySevenBaseTerminalDefectStrictBounds
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {routing :
      AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily routing}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Prop where
  u_abs_lt :
    |signed.integerWeightedDefect.u| < family.combinedModulus
  v_abs_lt :
    |signed.integerWeightedDefect.v| < family.combinedModulus
  y_abs_lt :
    |signed.integerWeightedDefect.y| < family.combinedModulus
  z_abs_lt :
    |signed.integerWeightedDefect.z| < family.combinedModulus

/-- Strict bounds annihilate every coordinate of the combined-modulus defect,
and hence upgrade the CRT identity to exact integer reconstruction. -/
theorem exact_reconstruction_of_defect_strictBounds
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {routing :
      AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily routing}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (bounds : AwaySevenBaseTerminalDefectStrictBounds signed) :
    signed.weighted = signed.model.weightedScale signed.scale := by
  apply signed.integerWeightedDefect_eq_zero_iff.mp
  have defectPacket := signed.integerWeightedDefectPacket
  apply AwayRoutingCoordinates.ext
  · apply integerWeightedDefect_eq_zero_of_abs_lt
      (M := family.combinedModulus) (defect := signed.integerWeightedDefect.u)
    · simpa [defectPacket.defect_eq] using defectPacket.modulus_dvd_u
    · exact bounds.u_abs_lt
  · apply integerWeightedDefect_eq_zero_of_abs_lt
      (M := family.combinedModulus) (defect := signed.integerWeightedDefect.v)
    · simpa [defectPacket.defect_eq] using defectPacket.modulus_dvd_v
    · exact bounds.v_abs_lt
  · apply integerWeightedDefect_eq_zero_of_abs_lt
      (M := family.combinedModulus) (defect := signed.integerWeightedDefect.y)
    · simpa [defectPacket.defect_eq] using defectPacket.modulus_dvd_y
    · exact bounds.y_abs_lt
  · apply integerWeightedDefect_eq_zero_of_abs_lt
      (M := family.combinedModulus) (defect := signed.integerWeightedDefect.z)
    · simpa [defectPacket.defect_eq] using defectPacket.modulus_dvd_z
    · exact bounds.z_abs_lt

/-- The second TERM-002 arithmetic obligation: once exact integer
reconstruction is known, each of the three explicit terminal row profiles is
incompatible with it.  Unlike the TERM-001 receiver, these fields do not
exclude a row without using the reconstruction conclusion. -/
structure AwaySevenBaseTerminalReconstructedRowMismatch
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {routing :
      AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily routing}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Prop where
  rowY_mismatch :
    AwaySevenBaseTerminalRowYProfile terminal →
      signed.weighted = signed.model.weightedScale signed.scale → False
  rowZ_mismatch :
    AwaySevenBaseTerminalRowZProfile terminal →
      signed.weighted = signed.model.weightedScale signed.scale → False
  rowSum_mismatch :
    AwaySevenBaseTerminalRowSumProfile terminal →
      signed.weighted = signed.model.weightedScale signed.scale → False

/-- The reduced TERM-002 receiver stores one concrete global CRT lift and only
the two missing arithmetic ingredients: strict defect bounds and the
reconstructed-row mismatch. -/
structure AwaySevenBaseTerminalArithmeticReceiver
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    Type where
  coherentRouting : AwaySevenBaseTerminalCoherentRoutingPacket terminal
  family :
    AwaySevenBaseTerminalPrimeScaleFamily coherentRouting.routing
  candidate :
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family
  signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate
  defectBounds : AwaySevenBaseTerminalDefectStrictBounds signed
  reconstructedRowMismatch :
    AwaySevenBaseTerminalReconstructedRowMismatch terminal signed

/-- Exact terminal exclusion bridge from the reduced TERM-002 arithmetic
receiver.  The obstruction branch is eliminated by the strict bounds; the
reconstructed branch is discharged by the row-sensitive mismatch. -/
theorem terminal_exclusion_of_receiver
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (receiver : AwaySevenBaseTerminalArithmeticReceiver terminal) :
    False := by
  rcases receiver.signed.signedReconstructionOutcome with
    hreconstructed | obstruction
  · rcases terminal.row_profile_decision with hy | hz | hs
    · exact receiver.reconstructedRowMismatch.rowY_mismatch hy hreconstructed
    · exact receiver.reconstructedRowMismatch.rowZ_mismatch hz hreconstructed
    · exact receiver.reconstructedRowMismatch.rowSum_mismatch hs hreconstructed
  · have hreconstructed :=
      exact_reconstruction_of_defect_strictBounds
        receiver.signed receiver.defectBounds
    have hzero :
        receiver.signed.integerWeightedDefect =
          AwayRoutingCoordinates.zero ℤ :=
      receiver.signed.integerWeightedDefect_eq_zero_iff.mpr hreconstructed
    apply obstruction.defect_ne_zero
    rw [obstruction.defectPacket.defect_eq]
    exact hzero

/-- End-to-end base-layer bridge requested by TERM-002.  It constructs the
actual terminal packet from the depth-one witness and leaves only the reduced,
independently reviewable arithmetic receiver as an input. -/
theorem no_terminal_base_layer_of_receiver
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (hreceiver :
      ∀ terminal : AwaySevenBaseTerminalUnitSectorPacket source r p,
        AwaySevenBaseTerminalArithmeticReceiver terminal)
    (layer : AwaySevenBaseLayerPacket p) :
    False := by
  rcases nonempty_awaySevenBaseTerminalUnitSectorPacket
      source r p layer.exponent_eq_one with ⟨terminal⟩
  exact terminal_exclusion_of_receiver terminal (hreceiver terminal)

/-- Populate the terminal exclusion statement's exact obligation from the
reduced arithmetic receiver, without entering the lifted/descent branch. -/
theorem terminal_exclusion_statement_of_receiver
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (hreceiver :
      ∀ terminal : AwaySevenBaseTerminalUnitSectorPacket source r p,
        AwaySevenBaseTerminalArithmeticReceiver terminal)
    (layer : AwaySevenBaseLayerPacket p)
    (statement : AwaySevenTerminalExclusionStatement source p) :
    statement.exclusionObligation := by
  have hfalse := no_terminal_base_layer_of_receiver hreceiver layer
  exact False.elim hfalse

end DkMath.FLT.Seven
