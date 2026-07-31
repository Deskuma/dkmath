/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionRoutingAudit

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCycleNormalForm"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
set_option maxRecDepth 2000

namespace RamifiedSignedRootRoutingPacket.ActiveUnitBoard

def rowMargin1 (u : ActiveUnitBoard) : (ZMod 7)ˣ :=
  u.u11 * u.u12 * u.u13

def rowMargin2 (u : ActiveUnitBoard) : (ZMod 7)ˣ :=
  u.u21 * u.u22 * u.u23

def columnMargin1 (u : ActiveUnitBoard) : (ZMod 7)ˣ :=
  u.u11 * u.u21

def columnMargin2 (u : ActiveUnitBoard) : (ZMod 7)ˣ :=
  u.u12 * u.u22

def columnMargin3 (u : ActiveUnitBoard) : (ZMod 7)ˣ :=
  u.u13 * u.u23

def cycleRatio12 (u : ActiveUnitBoard) : (ZMod 7)ˣ :=
  (u.u11 * u.u22) / (u.u12 * u.u21)

def cycleRatio23 (u : ActiveUnitBoard) : (ZMod 7)ˣ :=
  (u.u12 * u.u23) / (u.u13 * u.u22)

theorem cycleRatio12_div_cycleRatio23_eq
    (u : ActiveUnitBoard) :
    u.cycleRatio12 / u.cycleRatio23 =
      (u.rowMargin1 / u.rowMargin2) / u.columnMargin2 ^ 3 := by
  apply Units.ext
  simp [cycleRatio12, cycleRatio23, rowMargin1, rowMargin2,
    columnMargin2]
  field_simp
  exact congrArg Units.val (sevenUnit_pow_six u.u22)

theorem cycleRatio12_cube_eq
    (u : ActiveUnitBoard) :
    u.cycleRatio12 ^ 3 =
      (u.columnMargin1 / u.columnMargin2) ^ 3 := by
  apply Units.ext
  simp [cycleRatio12, columnMargin1, columnMargin2]
  field_simp
  have h21 : (u.u21 : ZMod 7) ^ 6 = 1 := by
    simpa using congrArg Units.val (sevenUnit_pow_six u.u21)
  have h22 : (u.u22 : ZMod 7) ^ 6 = 1 := by
    simpa using congrArg Units.val (sevenUnit_pow_six u.u22)
  rw [h21, h22]

theorem cycleRatio23_cube_eq
    (u : ActiveUnitBoard) :
    u.cycleRatio23 ^ 3 =
      (u.columnMargin2 / u.columnMargin3) ^ 3 := by
  apply Units.ext
  simp [cycleRatio23, columnMargin2, columnMargin3]
  field_simp
  have h22 : (u.u22 : ZMod 7) ^ 6 = 1 := by
    simpa using congrArg Units.val (sevenUnit_pow_six u.u22)
  have h23 : (u.u23 : ZMod 7) ^ 6 = 1 := by
    simpa using congrArg Units.val (sevenUnit_pow_six u.u23)
  rw [h22, h23]

/-- The visible common ternary multiplier on the two cycle ratios. -/
def cyclePhaseTwist
    (ω : SevenTernarySector) (u : ActiveUnitBoard) :
    ActiveUnitBoard :=
  let η : (ZMod 7)ˣ := (ω : (ZMod 7)ˣ) ^ 2
  {
    u11 := η * u.u11
    u12 := u.u12
    u13 := η⁻¹ * u.u13
    u21 := η⁻¹ * u.u21
    u22 := u.u22
    u23 := η * u.u23
  }

private theorem ternary_pow_four_eq
    (ω : SevenTernarySector) :
    (ω : (ZMod 7)ˣ) ^ 4 = (ω : (ZMod 7)ˣ) := by
  calc
    (ω : (ZMod 7)ˣ) ^ 4 =
        (ω : (ZMod 7)ˣ) ^ 3 * (ω : (ZMod 7)ˣ) := by
          rw [← pow_succ]
    _ = (ω : (ZMod 7)ˣ) := by rw [ω.property, one_mul]

theorem cyclePhaseTwist_margins
    (ω : SevenTernarySector) (u : ActiveUnitBoard) :
    (u.cyclePhaseTwist ω).rowMargin1 = u.rowMargin1 ∧
    (u.cyclePhaseTwist ω).rowMargin2 = u.rowMargin2 ∧
    (u.cyclePhaseTwist ω).columnMargin1 = u.columnMargin1 ∧
    (u.cyclePhaseTwist ω).columnMargin2 = u.columnMargin2 ∧
    (u.cyclePhaseTwist ω).columnMargin3 = u.columnMargin3 := by
  constructor
  · apply Units.ext
    simp [cyclePhaseTwist, rowMargin1]
    field_simp
  constructor
  · apply Units.ext
    simp [cyclePhaseTwist, rowMargin2]
    field_simp
  constructor
  · apply Units.ext
    simp [cyclePhaseTwist, columnMargin1]
    field_simp
  constructor
  · rfl
  · apply Units.ext
    simp [cyclePhaseTwist, columnMargin3]
    field_simp

theorem cyclePhaseTwist_cycles
    (ω : SevenTernarySector) (u : ActiveUnitBoard) :
    (u.cyclePhaseTwist ω).cycleRatio12 =
        (ω : (ZMod 7)ˣ) * u.cycleRatio12 ∧
    (u.cyclePhaseTwist ω).cycleRatio23 =
        (ω : (ZMod 7)ˣ) * u.cycleRatio23 := by
  have hω := ternary_pow_four_eq ω
  constructor
  · apply Units.ext
    simp [cyclePhaseTwist, cycleRatio12]
    field_simp
    have hωv : (((ω : (ZMod 7)ˣ) : ZMod 7) ^ 3) = 1 := by
      simpa using congrArg Units.val ω.property
    exact hωv
  · apply Units.ext
    simp [cyclePhaseTwist, cycleRatio23]
    field_simp
    have hωv : (((ω : (ZMod 7)ˣ) : ZMod 7) ^ 3) = 1 := by
      simpa using congrArg Units.val ω.property
    exact hωv

/-- A margin- and cycle-invisible ternary row gauge. -/
def hiddenRowTwist
    (ω : SevenTernarySector) (u : ActiveUnitBoard) :
    ActiveUnitBoard :=
  {
    u11 := (ω : (ZMod 7)ˣ) * u.u11
    u12 := (ω : (ZMod 7)ˣ) * u.u12
    u13 := (ω : (ZMod 7)ˣ) * u.u13
    u21 := (ω : (ZMod 7)ˣ)⁻¹ * u.u21
    u22 := (ω : (ZMod 7)ˣ)⁻¹ * u.u22
    u23 := (ω : (ZMod 7)ˣ)⁻¹ * u.u23
  }

theorem hiddenRowTwist_margins
    (ω : SevenTernarySector) (u : ActiveUnitBoard) :
    (u.hiddenRowTwist ω).rowMargin1 = u.rowMargin1 ∧
    (u.hiddenRowTwist ω).rowMargin2 = u.rowMargin2 ∧
    (u.hiddenRowTwist ω).columnMargin1 = u.columnMargin1 ∧
    (u.hiddenRowTwist ω).columnMargin2 = u.columnMargin2 ∧
    (u.hiddenRowTwist ω).columnMargin3 = u.columnMargin3 := by
  have hω : ((ω : (ZMod 7)ˣ) : ZMod 7) ^ 3 = 1 := by
    simpa using congrArg Units.val ω.property
  constructor
  · apply Units.ext
    simp only [hiddenRowTwist, rowMargin1, Units.val_mul]
    ring_nf
    rw [hω]
    simp
  constructor
  · apply Units.ext
    simp only [hiddenRowTwist, rowMargin2, Units.val_mul,
      Units.val_inv_eq_inv_val]
    field_simp
    rw [hω]
  constructor
  · apply Units.ext
    simp only [hiddenRowTwist, columnMargin1, Units.val_mul,
      Units.val_inv_eq_inv_val]
    field_simp
  constructor
  · apply Units.ext
    simp only [hiddenRowTwist, columnMargin2, Units.val_mul,
      Units.val_inv_eq_inv_val]
    field_simp
  · apply Units.ext
    simp only [hiddenRowTwist, columnMargin3, Units.val_mul,
      Units.val_inv_eq_inv_val]
    field_simp

theorem hiddenRowTwist_cycles
    (ω : SevenTernarySector) (u : ActiveUnitBoard) :
    (u.hiddenRowTwist ω).cycleRatio12 = u.cycleRatio12 ∧
    (u.hiddenRowTwist ω).cycleRatio23 = u.cycleRatio23 := by
  constructor
  · apply Units.ext
    simp only [hiddenRowTwist, cycleRatio12, Units.val_mul,
      Units.val_inv_eq_inv_val, div_eq_mul_inv]
    field_simp
  · apply Units.ext
    simp only [hiddenRowTwist, cycleRatio23, Units.val_mul,
      Units.val_inv_eq_inv_val, div_eq_mul_inv]
    field_simp

/-- Columnwise binary gauges whose total sign is one. -/
structure ColumnSignGauge where
  ε1 : SevenBinarySector
  ε2 : SevenBinarySector
  ε3 : SevenBinarySector
  product_eq :
    (ε1 : (ZMod 7)ˣ) * ε2 * ε3 = 1

def columnSignTwist
    (g : ColumnSignGauge) (u : ActiveUnitBoard) :
    ActiveUnitBoard :=
  {
    u11 := (g.ε1 : (ZMod 7)ˣ) * u.u11
    u12 := (g.ε2 : (ZMod 7)ˣ) * u.u12
    u13 := (g.ε3 : (ZMod 7)ˣ) * u.u13
    u21 := (g.ε1 : (ZMod 7)ˣ) * u.u21
    u22 := (g.ε2 : (ZMod 7)ˣ) * u.u22
    u23 := (g.ε3 : (ZMod 7)ˣ) * u.u23
  }

theorem columnSignTwist_margins_and_cycles
    (g : ColumnSignGauge) (u : ActiveUnitBoard) :
    (u.columnSignTwist g).rowMargin1 = u.rowMargin1 ∧
    (u.columnSignTwist g).rowMargin2 = u.rowMargin2 ∧
    (u.columnSignTwist g).columnMargin1 = u.columnMargin1 ∧
    (u.columnSignTwist g).columnMargin2 = u.columnMargin2 ∧
    (u.columnSignTwist g).columnMargin3 = u.columnMargin3 ∧
    (u.columnSignTwist g).cycleRatio12 = u.cycleRatio12 ∧
    (u.columnSignTwist g).cycleRatio23 = u.cycleRatio23 := by
  have hp :
      (((g.ε1 : (ZMod 7)ˣ) : ZMod 7) *
        (g.ε2 : (ZMod 7)ˣ) * (g.ε3 : (ZMod 7)ˣ)) = 1 := by
    simpa using congrArg Units.val g.product_eq
  have h1 : (((g.ε1 : (ZMod 7)ˣ) : ZMod 7) ^ 2) = 1 := by
    simpa using congrArg Units.val g.ε1.property
  have h2 : (((g.ε2 : (ZMod 7)ˣ) : ZMod 7) ^ 2) = 1 := by
    simpa using congrArg Units.val g.ε2.property
  have h3 : (((g.ε3 : (ZMod 7)ˣ) : ZMod 7) ^ 2) = 1 := by
    simpa using congrArg Units.val g.ε3.property
  constructor
  · apply Units.ext
    simp [columnSignTwist, rowMargin1]
    ring_nf at hp ⊢
    rw [hp]
    ring
  constructor
  · apply Units.ext
    simp [columnSignTwist, rowMargin2]
    ring_nf at hp ⊢
    rw [hp]
    ring
  constructor
  · apply Units.ext
    simp [columnSignTwist, columnMargin1]
    ring_nf at h1 ⊢
    rw [h1]
    ring
  constructor
  · apply Units.ext
    simp [columnSignTwist, columnMargin2]
    ring_nf at h2 ⊢
    rw [h2]
    ring
  constructor
  · apply Units.ext
    simp [columnSignTwist, columnMargin3]
    ring_nf at h3 ⊢
    rw [h3]
    ring
  constructor
  · apply Units.ext
    simp [columnSignTwist, cycleRatio12]
    field_simp
  · apply Units.ext
    simp [columnSignTwist, cycleRatio23]
    field_simp

/-- Equality of the five unit-shadow margins. -/
def SameMargins (u v : ActiveUnitBoard) : Prop :=
  u.rowMargin1 = v.rowMargin1 ∧
  u.rowMargin2 = v.rowMargin2 ∧
  u.columnMargin1 = v.columnMargin1 ∧
  u.columnMargin2 = v.columnMargin2 ∧
  u.columnMargin3 = v.columnMargin3

/-- Equality of the two oriented cycle ratios. -/
def SameCycles (u v : ActiveUnitBoard) : Prop :=
  u.cycleRatio12 = v.cycleRatio12 ∧
  u.cycleRatio23 = v.cycleRatio23

private def ternaryTwo : SevenTernarySector :=
  ⟨Units.mk0 (2 : ZMod 7) (by decide), by
    apply Units.ext
    decide⟩

private def oneBoard : ActiveUnitBoard :=
  ⟨1, 1, 1, 1, 1, 1⟩

private theorem cyclePhaseTwist_two_ne_one :
    oneBoard.cyclePhaseTwist ternaryTwo ≠ oneBoard := by
  intro h
  have hu := congrArg ActiveUnitBoard.u11 h
  have hv := congrArg Units.val hu
  exact (by decide : (2 : ZMod 7) ^ 2 ≠ 1) (by
    simpa [cyclePhaseTwist, ternaryTwo, oneBoard] using hv)

private theorem hiddenRowTwist_two_ne_one :
    oneBoard.hiddenRowTwist ternaryTwo ≠ oneBoard := by
  intro h
  have hu := congrArg ActiveUnitBoard.u11 h
  have hv := congrArg Units.val hu
  exact (by decide : (2 : ZMod 7) ≠ 1) (by
    simpa [hiddenRowTwist, ternaryTwo, oneBoard] using hv)

/-- The exact natural gcd routing is not ambiguous.  This theorem instead
shows that reconstructing cycle ratios from only the five unit-shadow margins
is insufficient. -/
theorem margins_do_not_determine_cycles :
    ∃ u v : ActiveUnitBoard,
      SameMargins u v ∧
      ¬SameCycles u v := by
  refine ⟨oneBoard, oneBoard.cyclePhaseTwist ternaryTwo, ?_, ?_⟩
  · have hm := cyclePhaseTwist_margins ternaryTwo oneBoard
    exact
      ⟨hm.1.symm, hm.2.1.symm, hm.2.2.1.symm,
        hm.2.2.2.1.symm, hm.2.2.2.2.symm⟩
  · intro h
    have hcycles := cyclePhaseTwist_cycles ternaryTwo oneBoard
    have hω : (ternaryTwo : (ZMod 7)ˣ) = 1 := by
      calc
        (ternaryTwo : (ZMod 7)ˣ) =
            (ternaryTwo : (ZMod 7)ˣ) * oneBoard.cycleRatio12 := by
              simp [oneBoard, cycleRatio12]
        _ = (oneBoard.cyclePhaseTwist ternaryTwo).cycleRatio12 :=
          hcycles.1.symm
        _ = oneBoard.cycleRatio12 := h.1.symm
        _ = 1 := by simp [oneBoard, cycleRatio12]
    have hv := congrArg Units.val hω
    exact (by decide : (2 : ZMod 7) ≠ 1) (by
      simpa [ternaryTwo] using hv)

/-- Even the five margins together with both cycle ratios do not reconstruct
the full unit-shadow board: a hidden ternary row gauge remains. -/
theorem margins_and_cycles_do_not_determine_board :
    ∃ u v : ActiveUnitBoard,
      SameMargins u v ∧ SameCycles u v ∧ u ≠ v := by
  have hm := hiddenRowTwist_margins ternaryTwo oneBoard
  have hc := hiddenRowTwist_cycles ternaryTwo oneBoard
  refine
    ⟨oneBoard, oneBoard.hiddenRowTwist ternaryTwo,
      ⟨hm.1.symm, hm.2.1.symm, hm.2.2.1.symm,
        hm.2.2.2.1.symm, hm.2.2.2.2.symm⟩,
      ⟨hc.1.symm, hc.2.symm⟩, ?_⟩
  exact Ne.symm hiddenRowTwist_two_ne_one

end RamifiedSignedRootRoutingPacket.ActiveUnitBoard


end

end DkMath.FLT.Seven
