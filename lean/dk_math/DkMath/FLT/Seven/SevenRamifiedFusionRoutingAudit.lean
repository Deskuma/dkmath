/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSectorEquiv
import DkMath.FLT.Seven.SevenRamifiedSignedRootRouting
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedSummit

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionRoutingAudit"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
set_option linter.style.longLine false

/-- The smallest provenance layer placed immediately before the common
ramified summit.  It deliberately does not duplicate the summit data. -/
structure RamifiedSummitProvenancePacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) : Type where
  row : EndpointRoutingRow
  row_eq : row = p.row
  row_eq_y_or_z : row = .y ∨ row = .z
  summit : PrimitiveRamifiedSummitPacket

namespace AwaySevenBaseTerminalUnitSectorPacket

/-- Row-Sum is eliminated while the surviving Y/Z label is retained beside
the common summit. -/
noncomputable def ramifiedSummitWithProvenance
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    RamifiedSummitProvenancePacket terminal := by
  have hrow : p.row = .y ∨ p.row = .z := by
    rcases terminal.row_profile_decision with hy | hz | hs
    · exact Or.inl hy.1
    · exact Or.inr hz.1
    · exact hs.false_of_swapped_away.elim
  exact {
    row := p.row
    row_eq := rfl
    row_eq_y_or_z := hrow
    summit := terminal.ramifiedSummit }

end AwaySevenBaseTerminalUnitSectorPacket

namespace RamifiedSignedRootRoutingPacket

theorem thirdRow_eq_one
    (p : RamifiedSignedRootRoutingPacket) :
    p.routing.c31 = 1 ∧ p.routing.c32 = 1 ∧ p.routing.c33 = 1 := by
  have hprod :
      p.routing.c31 * p.routing.c32 * p.routing.c33 = 1 := by
    simpa using p.routing.row3.symm
  rcases mul_eq_one.mp hprod with ⟨h12, h33⟩
  rcases mul_eq_one.mp h12 with ⟨h31, h32⟩
  exact ⟨h31, h32, h33⟩

private theorem activeRow_not_seven_dvd
    {g : ℤ} {x y z : ℕ}
    (hrow : Int.natAbs g = x * y * z)
    (hg : ¬(7 : ℤ) ∣ g) :
    ¬7 ∣ x ∧ ¬7 ∣ y ∧ ¬7 ∣ z := by
  have lift (t : ℕ) (ht : 7 ∣ t) (htrow : t ∣ x * y * z) : False := by
    apply hg
    apply Int.natAbs_dvd_natAbs.mp
    have hseven : 7 ∣ Int.natAbs g := by
      rw [hrow]
      exact dvd_trans ht htrow
    simpa using hseven
  constructor
  · intro hx
    exact lift x hx (by exact ⟨y * z, by ring⟩)
  constructor
  · intro hy
    exact lift y hy (by exact ⟨x * z, by ring⟩)
  · intro hz
    exact lift z hz (by exact ⟨x * y, by ring⟩)

/-- Every active cell has a modulo-seven unit shadow. -/
theorem activeCells_not_seven_dvd
    (p : RamifiedSignedRootRoutingPacket) :
    (¬7 ∣ p.routing.c11) ∧ (¬7 ∣ p.routing.c12) ∧
    (¬7 ∣ p.routing.c13) ∧ (¬7 ∣ p.routing.c21) ∧
    (¬7 ∣ p.routing.c22) ∧ (¬7 ∣ p.routing.c23) := by
  have hrow1 := activeRow_not_seven_dvd
    p.routing.row1 p.signedDepth.gapRoot_not_seven_dvd
  have hrow2 := activeRow_not_seven_dvd
    p.routing.row2 p.signedDepth.quotientRoot_not_seven_dvd
  exact ⟨hrow1.1, hrow1.2.1, hrow1.2.2,
    hrow2.1, hrow2.2.1, hrow2.2.2⟩

private def natUnit (n : ℕ) (h : ¬7 ∣ n) : (ZMod 7)ˣ :=
  Units.mk0 (n : ZMod 7) (by
    intro hz
    exact h ((ZMod.natCast_eq_zero_iff n 7).mp hz))

/-- Unit shadow of the active `2 × 3` board.  No signed orientation is
silently assigned to its natural-number cells. -/
structure ActiveUnitBoard where
  u11 : (ZMod 7)ˣ
  u12 : (ZMod 7)ˣ
  u13 : (ZMod 7)ˣ
  u21 : (ZMod 7)ˣ
  u22 : (ZMod 7)ˣ
  u23 : (ZMod 7)ˣ

def activeUnitBoard
    (p : RamifiedSignedRootRoutingPacket) : ActiveUnitBoard := by
  rcases p.activeCells_not_seven_dvd with
    ⟨h11, h12, h13, h21, h22, h23⟩
  exact {
    u11 := natUnit p.routing.c11 h11
    u12 := natUnit p.routing.c12 h12
    u13 := natUnit p.routing.c13 h13
    u21 := natUnit p.routing.c21 h21
    u22 := natUnit p.routing.c22 h22
    u23 := natUnit p.routing.c23 h23 }

/-- The signed margins erased by `Int.natAbs` in the routing construction. -/
structure SignedMarginOrientation
    (p : RamifiedSignedRootRoutingPacket) where
  rowGap : ℤ
  rowQuotient : ℤ
  columnLeft : ℤ
  columnRight : ℤ
  columnSeventh : ℤ
  rowGap_abs :
    Int.natAbs rowGap = Int.natAbs p.signedDepth.gapRoot
  rowQuotient_abs :
    Int.natAbs rowQuotient = Int.natAbs p.signedDepth.quotientRoot
  columnLeft_abs :
    Int.natAbs columnLeft = Int.natAbs
      (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst)
  columnRight_abs :
    Int.natAbs columnRight = Int.natAbs
      (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst +
       p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.snd)
  columnSeventh_abs :
    Int.natAbs columnSeventh = Int.natAbs
      (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.innerSndRoot ^ 7)

def signedMarginOrientation
    (p : RamifiedSignedRootRoutingPacket) :
    SignedMarginOrientation p :=
  ⟨p.signedDepth.gapRoot, p.signedDepth.quotientRoot,
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst,
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst +
      p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.snd,
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.innerSndRoot ^ 7,
    rfl, rfl, rfl, rfl, rfl⟩

/-- First independent `K_{2,3}` cycle ratio. -/
def cycleRatio12 (p : RamifiedSignedRootRoutingPacket) : (ZMod 7)ˣ :=
  let u := p.activeUnitBoard
  (u.u11 * u.u22) / (u.u12 * u.u21)

/-- Second independent `K_{2,3}` cycle ratio. -/
def cycleRatio23 (p : RamifiedSignedRootRoutingPacket) : (ZMod 7)ˣ :=
  let u := p.activeUnitBoard
  (u.u12 * u.u23) / (u.u13 * u.u22)

end RamifiedSignedRootRoutingPacket

/-- A routing audit attached to the same signed-depth object as the completed
paired theta jet. -/
structure RamifiedFusionRoutingAuditPacket where
  jet : RamifiedPairedThetaRootJetPacket
  routing : RamifiedSignedRootRoutingPacket
  signedDepth_eq : routing.signedDepth = jet.signedDepth

namespace RamifiedPairedThetaRootJetPacket

theorem nonempty_fusionRoutingAudit
    (p : RamifiedPairedThetaRootJetPacket) :
    Nonempty RamifiedFusionRoutingAuditPacket := by
  rcases p.signedDepth.nonempty_coherent_signedRootRouting with ⟨routing⟩
  exact ⟨⟨p, routing.1, routing.2⟩⟩

/-- Cyclotomic indices normalized relative to the FUSION slope.  This is a
torsor translation, not a declaration that any factor is distinguished. -/
def relativeCyclotomicIndex
    (p : RamifiedPairedThetaRootJetPacket)
    (k : (ZMod 7)ˣ) : (ZMod 7)ˣ :=
  k / p.fusionSlopeUnit

def relativeCyclotomicIndexEquiv
    (p : RamifiedPairedThetaRootJetPacket) :
    (ZMod 7)ˣ ≃ (ZMod 7)ˣ where
  toFun := p.relativeCyclotomicIndex
  invFun j := j * p.fusionSlopeUnit
  left_inv k := by
    simp [relativeCyclotomicIndex]
  right_inv j := by
    simp [relativeCyclotomicIndex]

theorem relativeCyclotomicIndex_eq_one_iff
    (p : RamifiedPairedThetaRootJetPacket) (k : (ZMod 7)ˣ) :
    p.relativeCyclotomicIndex k = 1 ↔ k = p.fusionSlopeUnit := by
  constructor
  · intro h
    apply p.relativeCyclotomicIndexEquiv.injective
    simpa [relativeCyclotomicIndexEquiv,
      relativeCyclotomicIndex] using h
  · rintro rfl
    simp [relativeCyclotomicIndex]

end RamifiedPairedThetaRootJetPacket

#print axioms
  AwaySevenBaseTerminalUnitSectorPacket.ramifiedSummitWithProvenance
#print axioms RamifiedSignedRootRoutingPacket.activeCells_not_seven_dvd
#print axioms
  RamifiedPairedThetaRootJetPacket.nonempty_fusionRoutingAudit
#print axioms
  RamifiedPairedThetaRootJetPacket.relativeCyclotomicIndex_eq_one_iff

end

end DkMath.FLT.Seven
