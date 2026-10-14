/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FourColorCell

#print "file: DkMathTest.Tromino.FourColorCellAxiomAudit"

namespace DkMathTest.Tromino.FourColorCellAxiomAudit

open DkMath.Polyomino
open DkMath.Polyomino.Tromino
open DkMath.Tromino

example : atomicFourColorCell.shape = block2 :=
  atomicFourColorCell_shape

example : atomicFourColorCell.shape.card = 4 :=
  atomicFourColorCell_card

example : CompleteFourState atomicFourColorCell :=
  atomicFourColorCell_complete

example : ∀ s : TrominoState,
    ∃! c, c ∈ atomicFourColorCell.shape ∧
      atomicFourColorCell.color c = s := by
  intro s
  exact completeFourState_existsUnique_cell atomicFourColorCell_complete s

example : PairwiseDistinctOnShape atomicFourColorCell :=
  atomicFourColorCell_pairwiseDistinct

example : internalProper atomicFourColorCell :=
  atomicFourColorCell_internalProper

example (delta : TrominoState) :
    CompleteFourState
      (uniformExchangeColoredShape delta atomicFourColorCell) :=
  atomicFourColorCell_exchange_complete delta

example (delta : TrominoState) (c₁ c₂ : DkMath.Polyomino.Cell) :
    (uniformExchangeColoredShape delta atomicFourColorCell).color c₁ ≠
        (uniformExchangeColoredShape delta atomicFourColorCell).color c₂ ↔
      atomicFourColorCell.color c₁ ≠ atomicFourColorCell.color c₂ :=
  uniformExchangeColoredShape_ne_iff delta atomicFourColorCell c₁ c₂

example (delta : TrominoState) (s : TrominoState) :
    stateMultiplicity (uniformExchangeColoredShape delta atomicFourColorCell) s =
      stateMultiplicity atomicFourColorCell (exchange delta s) :=
  stateMultiplicity_uniformExchangeColoredShape delta atomicFourColorCell s

example (delta : TrominoState) :
    PairwiseDistinctOnShape
      (uniformExchangeColoredShape delta atomicFourColorCell) :=
  pairwiseDistinct_uniformExchangeColoredShape
    atomicFourColorCell_pairwiseDistinct delta

example (delta : TrominoState) :
    internalProper
      (uniformExchangeColoredShape delta atomicFourColorCell) :=
  internalProper_uniformExchangeColoredShape
    atomicFourColorCell_internalProper delta

example : uniformExchangeColoredShape 0 atomicFourColorCell =
    atomicFourColorCell :=
  uniformExchangeColoredShape_zero atomicFourColorCell

example (delta : TrominoState) :
    uniformExchangeColoredShape delta
        (uniformExchangeColoredShape delta atomicFourColorCell) =
      atomicFourColorCell :=
  uniformExchangeColoredShape_involutive delta atomicFourColorCell

example : Function.Injective
    (fun delta => uniformExchangeColoredShape delta atomicFourColorCell) := by
  apply uniformExchangeColoredShape_injective_of_nonempty
  exact ⟨(0, 0), by simp [atomicFourColorCell, block2]⟩

example :
    (compatibleExchanges
      ({⟨(0, 0), (0, 0)⟩} : Finset BoundaryContact)).card = 3 := by
  decide

#print axioms DkMath.Tromino.completeFourState_existsUnique_cell
#print axioms DkMath.Tromino.completeFourState_stateMultiplicity
#print axioms DkMath.Tromino.uniformExchangeColoredShape_ne_iff
#print axioms DkMath.Tromino.stateMultiplicity_uniformExchangeColoredShape
#print axioms DkMath.Tromino.completeFourState_uniformExchangeColoredShape
#print axioms DkMath.Tromino.pairwiseDistinct_uniformExchangeColoredShape
#print axioms DkMath.Tromino.internalProper_uniformExchangeColoredShape
#print axioms DkMath.Tromino.atomicFourColorCell_complete
#print axioms DkMath.Tromino.atomicFourColorCell_internalProper
#print axioms DkMath.Tromino.uniformExchangeColoredShape_zero
#print axioms DkMath.Tromino.uniformExchangeColoredShape_involutive
#print axioms DkMath.Tromino.uniformExchangeColoredShape_injective_of_nonempty
#print axioms DkMath.Tromino.compatibleExchanges_eq_availableExchanges_zero

end DkMathTest.Tromino.FourColorCellAxiomAudit
