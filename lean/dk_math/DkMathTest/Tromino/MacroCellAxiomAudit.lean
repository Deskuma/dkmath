/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.MacroCell

#print "file: DkMathTest.Tromino.MacroCellAxiomAudit"

namespace DkMathTest.Tromino.MacroCellAxiomAudit

open DkMath.Polyomino
open DkMath.Polyomino.Tromino
open DkMath.Tromino

example (P : ColoredShape) (hP : CompleteFourState P) :
    expandFourColorMacroCell (collapseFourColorCell P hP) = P :=
  expand_collapseFourColorCell P hP

example (M : FourColorMacroCell) :
    collapseFourColorCell (expandFourColorMacroCell M) M.complete = M :=
  collapse_expandFourColorMacroCell M

example :
    expandFourColorMacroCell atomicFourColorMacroCell = atomicFourColorCell :=
  expand_atomicFourColorMacroCell

example :
    (expandFourColorMacroCell atomicFourColorMacroCell).shape = block2 := by
  simp

example :
    (expandFourColorMacroCell atomicFourColorMacroCell).shape.card = 4 :=
  atomicFourColorMacroCell_shape_card

example : macroCount atomicFourColorMacroCell = 1 :=
  macroCount_eq_one atomicFourColorMacroCell

example : atomicCellCount atomicFourColorMacroCell = 4 :=
  atomicCellCount_eq_four atomicFourColorMacroCell

example :
    atomicCellCount atomicFourColorMacroCell =
      4 * macroCount atomicFourColorMacroCell :=
  atomicCellCount_eq_four_mul_macroCount atomicFourColorMacroCell

example (delta : TrominoState) (M : FourColorMacroCell) :
    expandFourColorMacroCell (exchangeFourColorMacroCell delta M) =
      uniformExchangeColoredShape delta (expandFourColorMacroCell M) :=
  expand_exchangeFourColorMacroCell delta M

example (M : FourColorMacroCell) :
    exchangeFourColorMacroCell 0 M = M :=
  exchangeFourColorMacroCell_zero M

example (delta : TrominoState) (M : FourColorMacroCell) :
    exchangeFourColorMacroCell delta
        (exchangeFourColorMacroCell delta M) = M :=
  exchangeFourColorMacroCell_involutive delta M

example (delta : TrominoState) (M : FourColorMacroCell) :
    atomicCellCount (exchangeFourColorMacroCell delta M) =
      atomicCellCount M :=
  atomicCellCount_exchangeFourColorMacroCell delta M

example : Function.Injective (fun delta =>
    exchangeFourColorMacroCell delta atomicFourColorMacroCell) :=
  exchangeFourColorMacroCell_atomic_injective

example : macroCount atomicFourColorMacroCell = 1 := by
  decide

#print axioms DkMath.Tromino.expand_collapseFourColorCell
#print axioms DkMath.Tromino.collapse_expandFourColorMacroCell
#print axioms DkMath.Tromino.atomicFourColorMacroCell_complete
#print axioms DkMath.Tromino.atomicCellCount_eq_four
#print axioms DkMath.Tromino.atomicCellCount_eq_four_mul_macroCount
#print axioms DkMath.Tromino.expand_exchangeFourColorMacroCell
#print axioms DkMath.Tromino.exchangeFourColorMacroCell_zero
#print axioms DkMath.Tromino.exchangeFourColorMacroCell_involutive
#print axioms DkMath.Tromino.atomicCellCount_exchangeFourColorMacroCell
#print axioms DkMath.Tromino.exchangeFourColorMacroCell_atomic_injective

end DkMathTest.Tromino.MacroCellAxiomAudit
