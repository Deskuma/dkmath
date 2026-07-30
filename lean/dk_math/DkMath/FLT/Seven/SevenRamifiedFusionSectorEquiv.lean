/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJet

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionSectorEquiv"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The order-two coordinate inside the modulo-seven unit group. -/
def sevenBinarySectorSubgroup : Subgroup ((ZMod 7)ˣ) where
  carrier := {u | u ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change a ^ 2 = 1 at ha
    change b ^ 2 = 1 at hb
    change (a * b) ^ 2 = 1
    rw [mul_pow, ha, hb, mul_one]
  inv_mem' := by
    intro a ha
    change a ^ 2 = 1 at ha
    change a⁻¹ ^ 2 = 1
    rw [inv_pow, ha, inv_one]

/-- The order-three coordinate inside the modulo-seven unit group. -/
def sevenTernarySectorSubgroup : Subgroup ((ZMod 7)ˣ) where
  carrier := {u | u ^ 3 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change a ^ 3 = 1 at ha
    change b ^ 3 = 1 at hb
    change (a * b) ^ 3 = 1
    rw [mul_pow, ha, hb, mul_one]
  inv_mem' := by
    intro a ha
    change a ^ 3 = 1 at ha
    change a⁻¹ ^ 3 = 1
    rw [inv_pow, ha, inv_one]

abbrev SevenBinarySector := sevenBinarySectorSubgroup
abbrev SevenTernarySector := sevenTernarySectorSubgroup

theorem sevenUnit_pow_six (s : (ZMod 7)ˣ) :
    s ^ 6 = 1 := by
  apply Units.ext
  apply mul_left_cancel₀ s.ne_zero
  change (s : ZMod 7) * (s : ZMod 7) ^ 6 =
    (s : ZMod 7) * 1
  rw [← pow_succ', ZMod.pow_card]
  ring

/-- The explicit CRT decomposition
`(ZMod 7)ˣ ≃ μ₂ × μ₃`, given by `s ↦ (s³,s²)`. -/
def sevenUnitSectorEquiv :
    (ZMod 7)ˣ ≃* SevenBinarySector × SevenTernarySector where
  toFun s :=
    (⟨s ^ 3, by
        change (s ^ 3) ^ 2 = 1
        rw [← pow_mul]
        norm_num
        exact sevenUnit_pow_six s⟩,
      ⟨s ^ 2, by
        change (s ^ 2) ^ 3 = 1
        rw [← pow_mul]
        norm_num
        exact sevenUnit_pow_six s⟩)
  invFun x := (x.1 : (ZMod 7)ˣ) / (x.2 : (ZMod 7)ˣ)
  left_inv s := by
    change s ^ 3 / s ^ 2 = s
    rw [div_eq_mul_inv]
    group
  right_inv x := by
    rcases x with ⟨r, c⟩
    apply Prod.ext
    · apply Subtype.ext
      change ((r : (ZMod 7)ˣ) / (c : (ZMod 7)ˣ)) ^ 3 =
        (r : (ZMod 7)ˣ)
      rw [div_pow, c.property, div_one]
      calc
        (r : (ZMod 7)ˣ) ^ 3 =
            (r : (ZMod 7)ˣ) ^ 2 *
              (r : (ZMod 7)ˣ) := by group
        _ = (r : (ZMod 7)ˣ) := by
          rw [r.property, one_mul]
    · apply Subtype.ext
      change ((r : (ZMod 7)ˣ) / (c : (ZMod 7)ˣ)) ^ 2 =
        (c : (ZMod 7)ˣ)
      rw [div_pow, r.property, one_div]
      have hc0 : (c : (ZMod 7)ˣ) ^ 3 = 1 := by
        exact c.property
      have hc :
          (c : (ZMod 7)ˣ) * (c : (ZMod 7)ˣ) ^ 2 = 1 := by
        simpa only [pow_succ'] using hc0
      exact inv_eq_of_mul_eq_one_left hc
  map_mul' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change (x * y) ^ 3 = x ^ 3 * y ^ 3
      exact mul_pow x y 3
    · apply Subtype.ext
      change (x * y) ^ 2 = x ^ 2 * y ^ 2
      exact mul_pow x y 2

namespace RamifiedPairedThetaRootJetPacket

def fusionSlopeUnit
    (p : RamifiedPairedThetaRootJetPacket) : (ZMod 7)ˣ :=
  Units.mk0 p.fusionSlope p.fusionSlope_ne_zero

def leftFusionSlopeUnit
    (p : RamifiedPairedThetaRootJetPacket) : (ZMod 7)ˣ :=
  Units.mk0 (-p.fusionSlope) (neg_ne_zero.mpr p.fusionSlope_ne_zero)

def rightUnitSectorAddress
    (p : RamifiedPairedThetaRootJetPacket) :
    SevenBinarySector × SevenTernarySector :=
  sevenUnitSectorEquiv p.fusionSlopeUnit

def leftUnitSectorAddress
    (p : RamifiedPairedThetaRootJetPacket) :
    SevenBinarySector × SevenTernarySector :=
  sevenUnitSectorEquiv p.leftFusionSlopeUnit

theorem rightUnitSectorAddress_reconstructs
    (p : RamifiedPairedThetaRootJetPacket) :
    sevenUnitSectorEquiv.symm p.rightUnitSectorAddress =
      p.fusionSlopeUnit :=
  sevenUnitSectorEquiv.symm_apply_apply p.fusionSlopeUnit

theorem leftUnitSectorAddress_reconstructs
    (p : RamifiedPairedThetaRootJetPacket) :
    sevenUnitSectorEquiv.symm p.leftUnitSectorAddress =
      p.leftFusionSlopeUnit :=
  sevenUnitSectorEquiv.symm_apply_apply p.leftFusionSlopeUnit

/-- The left and right roots occupy opposite binary rows. -/
theorem left_binarySector_eq_neg_right
    (p : RamifiedPairedThetaRootJetPacket) :
    (((p.leftUnitSectorAddress.1 : (ZMod 7)ˣ) : ZMod 7)) =
      -(((p.rightUnitSectorAddress.1 : (ZMod 7)ˣ) : ZMod 7)) := by
  change (-p.fusionSlope) ^ 3 = -(p.fusionSlope ^ 3)
  ring

/-- The left and right roots occupy the same ternary column. -/
theorem left_ternarySector_eq_right
    (p : RamifiedPairedThetaRootJetPacket) :
    (((p.leftUnitSectorAddress.2 : (ZMod 7)ˣ) : ZMod 7)) =
      (((p.rightUnitSectorAddress.2 : (ZMod 7)ˣ) : ZMod 7)) := by
  change (-p.fusionSlope) ^ 2 = p.fusionSlope ^ 2
  ring

end RamifiedPairedThetaRootJetPacket

#print axioms sevenUnitSectorEquiv
#print axioms
  RamifiedPairedThetaRootJetPacket.left_binarySector_eq_neg_right

end

end DkMath.FLT.Seven
