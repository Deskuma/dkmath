/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.BoundaryPairing

#print "file: DkMathTest.Tromino.BoundaryPairingAxiomAudit"

namespace DkMathTest.Tromino.BoundaryPairingAxiomAudit

open DkMath.Tromino

def contactA : BoundaryContact := { inside := 0, outside := deltaA }
def contactB : BoundaryContact := { inside := 0, outside := deltaB }
def contactC : BoundaryContact := { inside := 0, outside := deltaC }

def emptySignature : BoundarySignature where
  arity := 0
  contact := fun i => Fin.elim0 i
  proper := by intro i; exact Fin.elim0 i

def evenSignature : BoundarySignature where
  arity := 6
  contact := ![contactA, contactA, contactB, contactB, contactC, contactC]
  proper := by intro i; fin_cases i <;> decide

def oddSignature : BoundarySignature where
  arity := 9
  contact := ![contactA, contactA, contactA, contactB, contactB, contactB,
    contactC, contactC, contactC]
  proper := by intro i; fin_cases i <;> decide

def invalidSignature : BoundarySignature where
  arity := 4
  contact := ![contactA, contactA, contactB, contactC]
  proper := by intro i; fin_cases i <;> decide

def duplicateSignature : BoundarySignature where
  arity := 2
  contact := ![contactA, contactA]
  proper := by intro i; fin_cases i <;> decide

example : (residualPorts (canonicalBoundaryPairing emptySignature)).card = 0 := by decide

example : residualPorts (canonicalBoundaryPairing evenSignature) = ∅ := by
  apply canonicalBoundaryPairing_even_perfect
  all_goals decide

example : (residualPorts (canonicalBoundaryPairing oddSignature)).card = 3 := by
  apply canonicalBoundaryPairing_odd_residual_card
  all_goals decide

example :
    ((residualPorts (canonicalBoundaryPairing oddSignature)).filter
      (fun i => boundaryDelta oddSignature i = deltaA)).card = 1 := by
  rw [residualPorts_canonical_card_by_label]
  decide

example :
    ((residualPorts (canonicalBoundaryPairing oddSignature)).filter
      (fun i => boundaryDelta oddSignature i = deltaB)).card = 1 := by
  rw [residualPorts_canonical_card_by_label]
  decide

example :
    ((residualPorts (canonicalBoundaryPairing oddSignature)).filter
      (fun i => boundaryDelta oddSignature i = deltaC)).card = 1 := by
  rw [residualPorts_canonical_card_by_label]
  decide

example : (residualPorts (canonicalBoundaryPairing invalidSignature)).card = 2 := by
  rw [canonicalBoundaryPairing_residual_card]
  decide

example :
    ((residualPorts (canonicalBoundaryPairing invalidSignature)).filter
      (fun i => boundaryDelta invalidSignature i = deltaB)).card = 1 := by
  rw [residualPorts_canonical_card_by_label]
  decide

example :
    ((residualPorts (canonicalBoundaryPairing invalidSignature)).filter
      (fun i => boundaryDelta invalidSignature i = deltaC)).card = 1 := by
  rw [residualPorts_canonical_card_by_label]
  decide

example : (residualPorts (canonicalBoundaryPairing duplicateSignature)).card = 0 := by
  rw [canonicalBoundaryPairing_residual_card]
  decide

example :
    canonicalMate duplicateSignature ⟨0, by decide⟩ ≠ ⟨0, by decide⟩ := by
  have hempty : residualPorts (canonicalBoundaryPairing duplicateSignature) = ∅ := by
    apply canonicalBoundaryPairing_even_perfect
    all_goals decide
  apply (canonicalBoundaryPairing_transition_ready duplicateSignature
    ⟨0, by decide⟩ (by rw [hempty]; simp)).1

example :
    canonicalMate duplicateSignature ⟨1, by decide⟩ ≠ ⟨1, by decide⟩ := by
  have hempty : residualPorts (canonicalBoundaryPairing duplicateSignature) = ∅ := by
    apply canonicalBoundaryPairing_even_perfect
    all_goals decide
  apply (canonicalBoundaryPairing_transition_ready duplicateSignature
    ⟨1, by decide⟩ (by rw [hempty]; simp)).1

example (S : BoundarySignature) (i : Fin S.arity)
    (hi : i ∉ residualPorts (canonicalBoundaryPairing S)) :
    canonicalMate S i ≠ i ∧
      boundaryDelta S (canonicalMate S i) = boundaryDelta S i ∧
        canonicalMate S (canonicalMate S i) = i :=
  canonicalBoundaryPairing_transition_ready S i hi

#print axioms DkMath.Tromino.adjacentMate_involutive
#print axioms DkMath.Tromino.adjacentMate_card_residual
#print axioms DkMath.Tromino.fiberPairing_involutive
#print axioms DkMath.Tromino.residualPorts_canonical_card_by_label
#print axioms DkMath.Tromino.canonicalBoundaryPairing_residual_card
#print axioms DkMath.Tromino.canonicalBoundaryPairing_even_perfect
#print axioms DkMath.Tromino.canonicalBoundaryPairing_odd_residual_card
#print axioms DkMath.Tromino.canonicalBoundaryPairing_conserved_decomposition
#print axioms DkMath.Tromino.canonicalBoundaryPairing_transition_ready

end DkMathTest.Tromino.BoundaryPairingAxiomAudit
