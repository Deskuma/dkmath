/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRamifiedGapUnitBridge

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedUnitClassAudit"

namespace DkMath.FLT.Seven

/-- Canonical reduction from level `k + 1` to level `k` in the tower of
seven-power residue rings. -/
noncomputable def sevenPowerReductionHom (k : ℕ) :
    ZMod (7 ^ (k + 1)) →+* ZMod (7 ^ k) :=
  ZMod.castHom (pow_dvd_pow 7 (Nat.le_succ k)) (ZMod (7 ^ k))

@[simp] theorem sevenPowerReductionHom_intCast (k : ℕ) (a : ℤ) :
    sevenPowerReductionHom k (a : ZMod (7 ^ (k + 1))) =
      (a : ZMod (7 ^ k)) := by
  simp [sevenPowerReductionHom]

/-- The explicit bridge units at adjacent levels are reductions of one
another.  Thus they form a coherent unit system, rather than unrelated
levelwise choices. -/
theorem RamifiedGapUnitBridgePacket.explicitUnit_reduction
    (p : RamifiedGapUnitBridgePacket) (k : ℕ) :
    sevenPowerReductionHom k (p.explicitUnit (k + 1)) =
      p.explicitUnit k := by
  let highInv : ZMod (7 ^ (k + 1)) :=
    ↑((p.leftUnit_isUnit (k + 1)).unit⁻¹)
  let lowInv : ZMod (7 ^ k) :=
    ↑((p.leftUnit_isUnit k).unit⁻¹)
  have hhigh :
      (p.leftUnit : ZMod (7 ^ (k + 1))) * highInv = 1 :=
    (p.leftUnit_isUnit (k + 1)).mul_val_inv
  have hmap :
      (p.leftUnit : ZMod (7 ^ k)) *
          sevenPowerReductionHom k highInv = 1 := by
    have := congrArg (sevenPowerReductionHom k) hhigh
    simpa using this
  have hlow :
      (p.leftUnit : ZMod (7 ^ k)) * lowInv = 1 :=
    (p.leftUnit_isUnit k).mul_val_inv
  have hinv :
      sevenPowerReductionHom k highInv = lowInv :=
    (p.leftUnit_isUnit k).mul_left_cancel (hmap.trans hlow.symm)
  simp only [explicitUnit, map_mul, sevenPowerReductionHom_intCast]
  change
    (p.rightUnit : ZMod (7 ^ k)) *
        sevenPowerReductionHom k highInv =
      (p.rightUnit : ZMod (7 ^ k)) * lowInv
  rw [hinv]

/-- The first nontrivial seventh-power audit for an explicit ramified bridge
unit. -/
def RamifiedGapUnitBridgePacket.IsSeventhPowerMod49
    (p : RamifiedGapUnitBridgePacket) : Prop :=
  ∃ w : ZMod 49, w ^ 7 = p.explicitUnit 2

set_option maxRecDepth 100000 in
private theorem zmod49_unit_is_seventhPower_iff :
    ∀ u : ZMod 49, IsUnit u →
      ((∃ w : ZMod 49, w ^ 7 = u) ↔ u ^ 7 = u) := by
  decide

/-- For a unit modulo `49`, membership in the seventh-power image is exactly
the fixed-point condition for the seventh-power map. -/
theorem RamifiedGapUnitBridgePacket.isSeventhPowerMod49_iff
    (p : RamifiedGapUnitBridgePacket) :
    p.IsSeventhPowerMod49 ↔
      (p.explicitUnit 2) ^ 7 = p.explicitUnit 2 := by
  exact zmod49_unit_is_seventhPower_iff
    (p.explicitUnit 2) (p.explicitUnit_isUnit 2)

set_option maxRecDepth 100000 in
/-- The complete six-element seventh-power unit image modulo `49`. -/
private theorem zmod49_unit_seventhPower_fixed_classifier :
    ∀ u : ZMod 49, IsUnit u →
      (u ^ 7 = u ↔
        u = 1 ∨ u = 18 ∨ u = 19 ∨ u = 30 ∨ u = 31 ∨ u = 48) := by
  decide

/-- RAMIFIED-004 finite residue classifier.  A general bridge packet reaches
the seventh-power branch precisely at these six unit residues. -/
theorem RamifiedGapUnitBridgePacket.isSeventhPowerMod49_iff_residue
    (p : RamifiedGapUnitBridgePacket) :
    p.IsSeventhPowerMod49 ↔
      p.explicitUnit 2 = 1 ∨
      p.explicitUnit 2 = 18 ∨
      p.explicitUnit 2 = 19 ∨
      p.explicitUnit 2 = 30 ∨
      p.explicitUnit 2 = 31 ∨
      p.explicitUnit 2 = 48 := by
  rw [p.isSeventhPowerMod49_iff]
  exact zmod49_unit_seventhPower_fixed_classifier
    (p.explicitUnit 2) (p.explicitUnit_isUnit 2)

/-- The mod-`49` unit-class question is a finite, decidable branch.  This
classification does not assert which branch a general ramified summit takes. -/
theorem RamifiedGapUnitBridgePacket.seventhPowerMod49_or_not
    (p : RamifiedGapUnitBridgePacket) :
    p.IsSeventhPowerMod49 ∨ ¬ p.IsSeventhPowerMod49 :=
  Classical.em _


end DkMath.FLT.Seven
