/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PieceExchange

#print "file: DkMathTest.Tromino.PieceExchangeAxiomAudit"

namespace DkMathTest.Tromino.PieceExchangeAxiomAudit

open DkMath.Tromino

private def zeroState : TrominoState := 0
private def stateA : TrominoState := (1, 0)
private def stateB : TrominoState := (0, 1)
private def stateC : TrominoState := (1, 1)

private def contact (inside outside : TrominoState) : BoundaryContact :=
  ⟨inside, outside⟩

example {I : Type*} (delta : TrominoState) (c : I → TrominoState) (i j : I) :
    uniformExchange delta c i = uniformExchange delta c j ↔ c i = c j :=
  uniformExchange_eq_iff delta c i j

example (contact₀ : BoundaryContact) (delta : TrominoState) :
    exchange delta contact₀.inside = contact₀.outside ↔
      delta = forbiddenDelta contact₀ :=
  exchange_eq_contact_iff contact₀ delta

example (contact₀ : BoundaryContact) :
    forbiddenDelta contact₀ = 0 ↔ contact₀.inside = contact₀.outside :=
  forbiddenDelta_eq_zero_iff contact₀

example (contacts : Finset BoundaryContact) (delta : TrominoState) :
    delta ∈ forbiddenExchangeSet contacts ↔
      ∃ contact₀ ∈ contacts, forbiddenDelta contact₀ = delta :=
  mem_forbiddenExchangeSet_iff

example (contacts : Finset BoundaryContact) (delta : TrominoState) :
    boundaryCompatible delta contacts ↔
      delta ∉ forbiddenExchangeSet contacts :=
  boundaryCompatible_iff_not_mem

example (contacts : Finset BoundaryContact)
    (h : forbiddenExchangeSet contacts ≠ Finset.univ) :
    ∃ delta, boundaryCompatible delta contacts :=
  exists_boundaryCompatible_of_forbiddenExchangeSet_ne_univ contacts h

example (contacts : Finset BoundaryContact)
    (hcurrent : ¬ boundaryCompatible 0 contacts)
    (h : forbiddenExchangeSet contacts ≠ Finset.univ) :
    ∃ delta, delta ≠ 0 ∧ boundaryCompatible delta contacts :=
  exists_nonzero_boundaryCompatible_of_not_compatible_zero contacts hcurrent h

example : (compatibleExchanges ∅).card = 4 :=
  card_compatibleExchanges_empty

example :
    (forbiddenExchangeSet {contact zeroState zeroState}).card = 1 := by
  simp [forbiddenExchangeSet]

example :
    (compatibleExchanges {contact zeroState zeroState}).card = 3 := by
  rw [card_compatibleExchanges]
  simp [forbiddenExchangeSet]

example :
    (forbiddenExchangeSet
      {contact zeroState stateA, contact stateA zeroState}).card = 1 := by
  simp [forbiddenExchangeSet, forbiddenDelta, contact, zeroState, stateA]

example :
    (compatibleExchanges
      {contact zeroState stateA, contact zeroState stateB,
       contact zeroState stateC}).card = 1 := by
  rw [card_compatibleExchanges]
  decide

example :
    ¬ ∃ delta, boundaryCompatible delta
      {contact zeroState zeroState, contact zeroState stateA,
       contact zeroState stateB, contact zeroState stateC} := by
  apply no_boundaryCompatible_of_forbiddenExchangeSet_eq_univ
  decide

#print axioms DkMath.Tromino.uniformExchange_eq_iff
#print axioms DkMath.Tromino.exchange_eq_contact_iff
#print axioms DkMath.Tromino.boundaryCompatible_iff_not_mem
#print axioms DkMath.Tromino.exists_boundaryCompatible_of_forbiddenExchangeSet_ne_univ
#print axioms DkMath.Tromino.exists_nonzero_boundaryCompatible_of_not_compatible_zero
#print axioms DkMath.Tromino.card_compatibleExchanges

end DkMathTest.Tromino.PieceExchangeAxiomAudit
