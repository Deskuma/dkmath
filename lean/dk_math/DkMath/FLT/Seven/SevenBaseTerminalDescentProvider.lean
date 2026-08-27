/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalCellCarryDependency

#print "file: DkMath.FLT.Seven.SevenBaseTerminalDescentProvider"

namespace DkMath.FLT.Seven

/-- Minimal integral reconstruction data sufficient to construct the next
away FLT7 counterexample at the old root-second-coordinate carrier.

Unlike `AwayDescentClosureProvider`, this seed exposes the genuinely
mathematical reconstruction fields: a new away coordinate normal form and the
identification of its exceptional endpoint factor with the required carrier.
-/
structure AwayDescentReconstructionSeed
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z) : Type where
  nextX : ℕ
  nextY : ℕ
  nextZ : ℕ
  nextNormal : AwayCoordinateNormalForm nextX nextY nextZ
  target_source :
    AwayExceptionalCarrierSource nextY nextZ
      (Int.natAbs p.normal.root.snd)

/-- The valuation-transfer packet determined by a descent reconstruction
seed. -/
def AwayDescentReconstructionSeed.nextRoute
    {x y z : ℕ} {p : AwayValuationTransferPacket x y z}
    (seed : AwayDescentReconstructionSeed p) :
    AwayValuationTransferPacket seed.nextX seed.nextY seed.nextZ := by
  let target := Int.natAbs p.normal.root.snd
  have hvaluation :
      padicValNat 7 target =
        1 + padicValNat 7 (Int.natAbs seed.nextNormal.root.snd) := by
    dsimp [target]
    cases seed.target_source with
    | right hy hz hsum htarget =>
        rw [htarget]
        exact away_right_padicValNat_transfer seed.nextNormal hy hz hsum
    | left hz hy hsum htarget =>
        rw [htarget]
        exact away_left_padicValNat_transfer seed.nextNormal hz hy hsum
    | sum hsum hy hz htarget =>
        rw [htarget]
        exact away_sum_padicValNat_transfer seed.nextNormal hsum hy hz
  exact {
    normal := seed.nextNormal
    carrier := target
    source := seed.target_source
    carrier_pos := p.root_snd_abs_pos
    root_snd_abs_pos :=
      Int.natAbs_pos.mpr seed.nextNormal.root_snd_ne_zero
    valuation_eq := hvaluation }

/-- Construct the recursive descent provider from the exact integral
reconstruction seed. -/
def AwayDescentReconstructionSeed.toClosureProvider
    {x y z : ℕ} {p : AwayValuationTransferPacket x y z}
    (seed : AwayDescentReconstructionSeed p) :
    AwayDescentClosureProvider x y z p where
  nextX := seed.nextX
  nextY := seed.nextY
  nextZ := seed.nextZ
  nextPack := seed.nextNormal.counterexample
  nextRoute := seed.nextRoute
  carrier_match := rfl

/-- Every existing closure provider contains an equivalent reconstruction
seed.  This proves that the seed states exactly the missing mathematics rather
than a stronger auxiliary assumption. -/
def AwayDescentClosureProvider.toReconstructionSeed
    {x y z : ℕ} {p : AwayValuationTransferPacket x y z}
    (provider : AwayDescentClosureProvider x y z p) :
    AwayDescentReconstructionSeed p where
  nextX := provider.nextX
  nextY := provider.nextY
  nextZ := provider.nextZ
  nextNormal := provider.nextRoute.normal
  target_source := by
    rw [← provider.carrier_match]
    exact provider.nextRoute.source

/-- The reconstruction seed is logically equivalent to the original descent
provider contract. -/
theorem nonempty_descentReconstructionSeed_iff_closureProvider
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    Nonempty (AwayDescentReconstructionSeed p) ↔
      Nonempty (AwayDescentClosureProvider x y z p) := by
  constructor
  · rintro ⟨seed⟩
    exact ⟨seed.toClosureProvider⟩
  · rintro ⟨provider⟩
    exact ⟨provider.toReconstructionSeed⟩

/-- A reconstruction seed realizes the already proved strict decrease of the
seven-adic carrier depth. -/
theorem away_depth_descent_of_reconstructionSeed
    {x y z : ℕ} {p : AwayValuationTransferPacket x y z}
    (seed : AwayDescentReconstructionSeed p) :
    padicValNat 7 seed.nextRoute.carrier <
      padicValNat 7 p.carrier :=
  away_depth_descent_of_closureProvider p seed.toClosureProvider

/-- Exact DESCENT-001 open packet.  It retains the complete TERM-008 carry
audit and names the remaining integral reconstruction proposition without
pretending that the local CRT data already inhabit it. -/
structure AwaySevenBaseTerminalDescentOpenPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type where
  carryAudit : AwaySevenBaseTerminalCellCarryDependencyAuditPacket signed
  reconstructionObligation : Prop
  reconstructionObligation_eq :
    reconstructionObligation =
      Nonempty (AwayDescentReconstructionSeed r.cubic.transfer)

/-- DESCENT-001 decision boundary: either the exact reconstruction seed has
constructed the provider, or the seed remains as an independently reviewable
integral obligation alongside all TERM-008 data. -/
inductive AwaySevenBaseTerminalDescentDecision
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    Type
  | descends (provider : AwayDescentClosureProvider x y z r.cubic.transfer)
  | open (packet : AwaySevenBaseTerminalDescentOpenPacket signed)

/-- Turn a supplied integral reconstruction seed into the closed DESCENT-001
branch. -/
def AwaySevenBaseTerminalSignedRepresentativePacket.descentDecisionOfSeed
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate)
    (seed : AwayDescentReconstructionSeed r.cubic.transfer) :
    AwaySevenBaseTerminalDescentDecision signed :=
  .descends seed.toClosureProvider

/-- Current unconditional DESCENT-001 result.  All proved terminal data is
retained, while the exact new-counterexample reconstruction seed stays open. -/
noncomputable def
    AwaySevenBaseTerminalSignedRepresentativePacket.descentDecisionOpen
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    (signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate) :
    AwaySevenBaseTerminalDescentDecision signed :=
  .open {
    carryAudit := signed.cellCarryDependencyAuditPacket
    reconstructionObligation :=
      Nonempty (AwayDescentReconstructionSeed r.cubic.transfer)
    reconstructionObligation_eq := rfl }

end DkMath.FLT.Seven
