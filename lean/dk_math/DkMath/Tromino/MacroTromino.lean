/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.MacroCell
import DkMath.Tromino.Restoration

#print "file: DkMath.Tromino.MacroTromino"

namespace DkMath.Tromino

open DkMath.Polyomino
open DkMath.Polyomino.Tromino

/-!
# One-level macro-coordinate Tromino frame

The coordinates in this module reuse the finite `Shape` carrier, but they are
macro positions, not atomic lattice cells. Each occupied macro position stores
one certified `FourColorMacroCell` payload.
-/

/-- A finite macro-coordinate footprint with a certified macro payload map. -/
structure MacroShape where
  shape : Shape
  payload : Cell → FourColorMacroCell

@[ext] theorem MacroShape.ext'
    {P Q : MacroShape} (hshape : P.shape = Q.shape)
    (hpayload : P.payload = Q.payload) : P = Q := by
  cases P
  cases Q
  simp_all

/-- Restrict a macro shape to a finite macro-coordinate subset. -/
def restrictMacroShape (P : MacroShape) (S : Shape) : MacroShape :=
  { shape := P.shape ∩ S
    payload := P.payload }

@[simp] theorem restrictMacroShape_payload
    (P : MacroShape) (S : Shape) (c : Cell) :
    (restrictMacroShape P S).payload c = P.payload c := rfl

/-- A typed missing macro slot: footprint plus the payload to restore there. -/
structure MacroGapSlot where
  footprint : Shape
  expected : FourColorMacroCell

/-- Restore a target macro shape from a retained body and one typed gap slot. -/
def macroRestoreRel
    (target body : MacroShape) (gap : MacroGapSlot) : Prop :=
  Disjoint body.shape gap.footprint ∧
    body.shape ∪ gap.footprint = target.shape ∧
    (∀ c ∈ body.shape, body.payload c = target.payload c) ∧
    (∀ c ∈ gap.footprint, gap.expected = target.payload c)

/-- The macro body and gap footprints have the same restoration relation as shapes. -/
theorem macroRestoreRel_shape_part
    {target body : MacroShape} {gap : MacroGapSlot}
    (h : macroRestoreRel target body gap) :
    shapeRestoreRel target.shape body.shape gap.footprint := by
  exact ⟨h.1, h.2.1⟩

/-- Fixed target/body macro restoration has a unique gap footprint. -/
theorem macroRestoreRel_gap_footprint_unique
    {target body : MacroShape} {gap₁ gap₂ : MacroGapSlot}
    (h₁ : macroRestoreRel target body gap₁)
    (h₂ : macroRestoreRel target body gap₂) :
    gap₁.footprint = gap₂.footprint := by
  exact shapeRestoreRel_gap_unique
    (macroRestoreRel_shape_part h₁) (macroRestoreRel_shape_part h₂)

/-- A nonempty fixed gap footprint forces a unique expected macro payload. -/
theorem macroRestoreRel_expected_unique
    {target body : MacroShape} {gap₁ gap₂ : MacroGapSlot}
    (hfootprint : gap₁.footprint = gap₂.footprint)
    (hne : gap₁.footprint.Nonempty)
    (h₁ : macroRestoreRel target body gap₁)
    (h₂ : macroRestoreRel target body gap₂) :
    gap₁.expected = gap₂.expected := by
  rcases hne with ⟨c, hc⟩
  have hc₂ : c ∈ gap₂.footprint := by
    rw [← hfootprint]
    exact hc
  exact (h₁.2.2.2 c hc).trans (h₂.2.2.2 c hc₂).symm

/-- The canonical 2x2 macro-coordinate frame, with the atomic macro payload everywhere. -/
def canonicalMacroFrame : MacroShape :=
  { shape := block2
    payload := fun _ => atomicFourColorMacroCell }

@[simp] theorem canonicalMacroFrame_shape :
    canonicalMacroFrame.shape = block2 := rfl

theorem canonicalMacroFrame_shape_card :
    canonicalMacroFrame.shape.card = 4 := by
  simpa [canonicalMacroFrame, area] using area_block2

@[simp] theorem canonicalMacroFrame_payload (c : Cell) :
    canonicalMacroFrame.payload c = atomicFourColorMacroCell := rfl

/-- The L-shaped retained macro body obtained by restricting the frame. -/
def canonicalMacroBody : MacroShape :=
  restrictMacroShape canonicalMacroFrame L_tromino

theorem canonicalMacroBody_shape :
    canonicalMacroBody.shape = L_tromino := by
  have hsub : L_tromino ⊆ block2 := by
    rw [block2_eq_L_union_hole]
    exact Finset.subset_union_left
  change block2 ∩ L_tromino = L_tromino
  exact Finset.inter_eq_right.mpr hsub

@[simp] theorem canonicalMacroBody_payload (c : Cell) :
    canonicalMacroBody.payload c = atomicFourColorMacroCell := by
  rfl

/-- The typed one-position macro gap in the canonical frame. -/
def canonicalMacroGap : MacroGapSlot :=
  { footprint := hole2
    expected := atomicFourColorMacroCell }

@[simp] theorem canonicalMacroGap_footprint :
    canonicalMacroGap.footprint = hole2 := rfl

@[simp] theorem canonicalMacroGap_expected :
    canonicalMacroGap.expected = atomicFourColorMacroCell := rfl

theorem canonicalMacroGap_footprint_card :
    canonicalMacroGap.footprint.card = 1 := by
  simp [canonicalMacroGap, hole2]

/-- The canonical L-plus-gap macro restoration certificate. -/
theorem canonical_macroRestoreRel :
    macroRestoreRel canonicalMacroFrame canonicalMacroBody canonicalMacroGap := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [canonicalMacroBody_shape]
    exact disjoint_L_hole
  · rw [canonicalMacroBody_shape]
    exact block2_eq_L_union_hole.symm
  · intro c hc
    rfl
  · intro c hc
    rfl

/-- Number of occupied macro coordinates. -/
def macroPositionCount (P : MacroShape) : ℕ := P.shape.card

theorem canonicalMacroFrame_macroPositionCount :
    macroPositionCount canonicalMacroFrame = 4 := by
  simpa [macroPositionCount] using canonicalMacroFrame_shape_card

theorem canonicalMacroBody_macroPositionCount :
    macroPositionCount canonicalMacroBody = 3 := by
  rw [macroPositionCount, canonicalMacroBody_shape]
  simp [L_tromino]

theorem canonicalMacroGap_macroPositionCount :
    canonicalMacroGap.footprint.card = 1 :=
  canonicalMacroGap_footprint_card

theorem canonical_macro_count_split :
    macroPositionCount canonicalMacroBody +
        canonicalMacroGap.footprint.card =
      macroPositionCount canonicalMacroFrame := by
  rw [canonicalMacroBody_macroPositionCount,
    canonicalMacroGap_macroPositionCount,
    canonicalMacroFrame_macroPositionCount]

/-- Sum of atomic payload counts over the occupied macro coordinates. -/
def atomicPayloadMass (P : MacroShape) : ℕ :=
  Finset.sum P.shape (fun c => atomicCellCount (P.payload c))

theorem atomicPayloadMass_eq_four_mul_card_of_constant
    (P : MacroShape) (M : FourColorMacroCell)
    (hpayload : ∀ c ∈ P.shape, P.payload c = M) :
    atomicPayloadMass P = 4 * P.shape.card := by
  calc
    atomicPayloadMass P = Finset.sum P.shape (fun _ => atomicCellCount M) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [hpayload c hc]
    _ = Finset.sum P.shape (fun _ => 4) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact atomicCellCount_eq_four M
    _ = 4 * P.shape.card := by
      simp [Nat.mul_comm]

theorem canonicalMacroBody_atomicPayloadMass :
    atomicPayloadMass canonicalMacroBody = 12 := by
  rw [atomicPayloadMass_eq_four_mul_card_of_constant canonicalMacroBody
    atomicFourColorMacroCell]
  · rw [canonicalMacroBody_shape]
    simp [L_tromino]
  · intro c hc
    exact canonicalMacroBody_payload c

theorem canonicalMacroGap_atomicPayloadMass :
    atomicCellCount canonicalMacroGap.expected = 4 :=
  atomicCellCount_eq_four canonicalMacroGap.expected

theorem canonicalMacroFrame_atomicPayloadMass :
    atomicPayloadMass canonicalMacroFrame = 16 := by
  rw [atomicPayloadMass_eq_four_mul_card_of_constant canonicalMacroFrame
    atomicFourColorMacroCell]
  · rw [canonicalMacroFrame_shape_card]
  · intro c hc
    exact canonicalMacroFrame_payload c

theorem canonical_atomic_mass_split :
    atomicPayloadMass canonicalMacroBody +
        atomicCellCount canonicalMacroGap.expected =
      atomicPayloadMass canonicalMacroFrame := by
  rw [canonicalMacroBody_atomicPayloadMass,
    canonicalMacroGap_atomicPayloadMass,
    canonicalMacroFrame_atomicPayloadMass]

theorem canonical_atomic_mass_scale :
    atomicPayloadMass canonicalMacroFrame =
      4 * macroPositionCount canonicalMacroFrame := by
  rw [canonicalMacroFrame_atomicPayloadMass,
    canonicalMacroFrame_macroPositionCount]

end DkMath.Tromino
