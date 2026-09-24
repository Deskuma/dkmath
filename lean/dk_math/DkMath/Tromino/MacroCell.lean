/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FourColorCell

#print "file: DkMath.Tromino.MacroCell"

namespace DkMath.Tromino

open DkMath.Polyomino.Tromino

/-!
# Level-0 four-state macro cell

This module packages one complete four-state colored shape as one macro unit.
It is intentionally not a recursive or scaled macro-cell construction.
-/

/-- A level-0 macro unit carrying a certified complete colored payload. -/
structure FourColorMacroCell where
  payload : ColoredShape
  complete : CompleteFourState payload

@[ext] theorem FourColorMacroCell.ext'
    {M N : FourColorMacroCell} (hpayload : M.payload = N.payload) : M = N := by
  cases M
  cases N
  cases hpayload
  rfl

/-- Collapse a certified complete colored shape to one level-0 macro unit. -/
def collapseFourColorCell
    (P : ColoredShape) (hP : CompleteFourState P) : FourColorMacroCell :=
  { payload := P
    complete := hP }

/-- Expand a level-0 macro unit back to its certified colored payload. -/
def expandFourColorMacroCell (M : FourColorMacroCell) : ColoredShape :=
  M.payload

/-- Expansion after collapse is definitionally the original payload. -/
theorem expand_collapseFourColorCell
    (P : ColoredShape) (hP : CompleteFourState P) :
    expandFourColorMacroCell (collapseFourColorCell P hP) = P := rfl

/-- Collapse after expansion is exact, up to proof irrelevance. -/
theorem collapse_expandFourColorMacroCell (M : FourColorMacroCell) :
    collapseFourColorCell (expandFourColorMacroCell M) M.complete = M := by
  cases M
  rfl

/-- The canonical atomic colored cell viewed as one level-0 macro unit. -/
def atomicFourColorMacroCell : FourColorMacroCell :=
  collapseFourColorCell atomicFourColorCell atomicFourColorCell_complete

@[simp] theorem expand_atomicFourColorMacroCell :
    expandFourColorMacroCell atomicFourColorMacroCell = atomicFourColorCell :=
  rfl

theorem atomicFourColorMacroCell_complete :
    CompleteFourState (expandFourColorMacroCell atomicFourColorMacroCell) :=
  atomicFourColorCell_complete

theorem atomicFourColorMacroCell_shape_card :
    (expandFourColorMacroCell atomicFourColorMacroCell).shape.card = 4 :=
  atomicFourColorCell_card

/-- Every level-0 macro wrapper counts as one macro unit. -/
def macroCount (_M : FourColorMacroCell) : ℕ := 1

/-- The number of atomic cells in the expanded payload. -/
def atomicCellCount (M : FourColorMacroCell) : ℕ :=
  (expandFourColorMacroCell M).shape.card

theorem atomicCellCount_eq_four (M : FourColorMacroCell) :
    atomicCellCount M = 4 := by
  exact M.complete.1

theorem macroCount_eq_one (M : FourColorMacroCell) :
    macroCount M = 1 := rfl

theorem atomicCellCount_eq_four_mul_macroCount (M : FourColorMacroCell) :
    atomicCellCount M = 4 * macroCount M := by
  rw [atomicCellCount_eq_four, macroCount_eq_one]

/-- Uniform exchange lifted to certified level-0 macro units. -/
def exchangeFourColorMacroCell
    (delta : TrominoState) (M : FourColorMacroCell) : FourColorMacroCell :=
  { payload := uniformExchangeColoredShape delta (expandFourColorMacroCell M)
    complete := completeFourState_uniformExchangeColoredShape M.complete delta }

/-- Expansion commutes with the lifted macro exchange action. -/
theorem expand_exchangeFourColorMacroCell
    (delta : TrominoState) (M : FourColorMacroCell) :
    expandFourColorMacroCell (exchangeFourColorMacroCell delta M) =
      uniformExchangeColoredShape delta (expandFourColorMacroCell M) := rfl

/-- Zero exchange leaves a macro unit unchanged. -/
theorem exchangeFourColorMacroCell_zero (M : FourColorMacroCell) :
    exchangeFourColorMacroCell 0 M = M := by
  apply FourColorMacroCell.ext'
  exact uniformExchangeColoredShape_zero (expandFourColorMacroCell M)

/-- Every lifted exchange is involutive. -/
theorem exchangeFourColorMacroCell_involutive
    (delta : TrominoState) (M : FourColorMacroCell) :
    exchangeFourColorMacroCell delta
        (exchangeFourColorMacroCell delta M) = M := by
  apply FourColorMacroCell.ext'
  exact uniformExchangeColoredShape_involutive delta
    (expandFourColorMacroCell M)

/-- Macro exchange preserves the atomic footprint count. -/
theorem atomicCellCount_exchangeFourColorMacroCell
    (delta : TrominoState) (M : FourColorMacroCell) :
    atomicCellCount (exchangeFourColorMacroCell delta M) =
      atomicCellCount M := by
  simp [atomicCellCount, exchangeFourColorMacroCell,
    expandFourColorMacroCell, uniformExchangeColoredShape]

/-- The canonical macro exchange orbit is injective in its delta. -/
theorem exchangeFourColorMacroCell_atomic_injective :
    Function.Injective (fun delta =>
      exchangeFourColorMacroCell delta atomicFourColorMacroCell) := by
  intro delta₁ delta₂ hdelta
  have hnonempty :
      (expandFourColorMacroCell atomicFourColorMacroCell).shape.Nonempty := by
    change atomicFourColorCell.shape.Nonempty
    exact ⟨(0, 0), by simp [atomicFourColorCell, block2]⟩
  have hpayload :
      uniformExchangeColoredShape delta₁
          (expandFourColorMacroCell atomicFourColorMacroCell) =
        uniformExchangeColoredShape delta₂
          (expandFourColorMacroCell atomicFourColorMacroCell) := by
    simpa [exchangeFourColorMacroCell] using
      congrArg (fun M : FourColorMacroCell => M.payload) hdelta
  exact uniformExchangeColoredShape_injective_of_nonempty hnonempty hpayload

end DkMath.Tromino
