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

/-- The remaining row-sensitive arithmetic receiver. Its fields are precisely
the three branch exclusions; it does not assume terminal exclusion as a single
opaque proposition. -/
structure AwaySevenBaseTerminalArithmeticReceiver
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    Prop where
  rowY_impossible : AwaySevenBaseTerminalRowYProfile terminal → False
  rowZ_impossible : AwaySevenBaseTerminalRowZProfile terminal → False
  rowSum_impossible :
    AwaySevenBaseTerminalRowSumProfile terminal → False

/-- Exact terminal exclusion bridge from the three unresolved row arithmetic
branches. -/
theorem terminal_exclusion_of_receiver
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p)
    (receiver : AwaySevenBaseTerminalArithmeticReceiver terminal) :
    False := by
  rcases terminal.row_profile_decision with hy | hz | hs
  · exact receiver.rowY_impossible hy
  · exact receiver.rowZ_impossible hz
  · exact receiver.rowSum_impossible hs

end DkMath.FLT.Seven
