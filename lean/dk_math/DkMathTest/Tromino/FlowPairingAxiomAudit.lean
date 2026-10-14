/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowPairing

#print "file: DkMathTest.Tromino.FlowPairingAxiomAudit"

namespace DkMathTest.Tromino.FlowPairingAxiomAudit

open DkMath.Tromino

def emptyFlow : FlowSignature where
  arity := 0
  label := fun i => Fin.elim0 i
  nonzero := by intro i; exact Fin.elim0 i

def evenFlow : FlowSignature where
  arity := 6
  label := ![deltaA, deltaA, deltaB, deltaB, deltaC, deltaC]
  nonzero := by
    intro i
    fin_cases i <;> simp [deltaA_ne_zero, deltaB_ne_zero, deltaC_ne_zero]

def oddFlow : FlowSignature where
  arity := 9
  label := ![deltaA, deltaA, deltaA, deltaB, deltaB, deltaB,
    deltaC, deltaC, deltaC]
  nonzero := by
    intro i
    fin_cases i <;> simp [deltaA_ne_zero, deltaB_ne_zero, deltaC_ne_zero]

def invalidFlow : FlowSignature where
  arity := 4
  label := ![deltaA, deltaA, deltaB, deltaC]
  nonzero := by
    intro i
    fin_cases i <;> simp [deltaA_ne_zero, deltaB_ne_zero, deltaC_ne_zero]

def duplicateFlow : FlowSignature where
  arity := 2
  label := ![deltaA, deltaA]
  nonzero := by
    intro i
    fin_cases i <;> exact deltaA_ne_zero

example : (flowResidualPorts (canonicalFlowPairing emptyFlow)).card = 0 := by
  rw [canonicalFlowPairing_residual_card]
  decide

example : flowResidualPorts (canonicalFlowPairing evenFlow) = ∅ := by
  apply canonicalFlowPairing_even_perfect
  all_goals decide

example : (flowResidualPorts (canonicalFlowPairing oddFlow)).card = 3 := by
  apply canonicalFlowPairing_odd_residual_card
  all_goals decide

example :
    (flowResidualPortsWithLabel (canonicalFlowPairing oddFlow) deltaA).card = 1 ∧
      (flowResidualPortsWithLabel (canonicalFlowPairing oddFlow) deltaB).card = 1 ∧
        (flowResidualPortsWithLabel (canonicalFlowPairing oddFlow) deltaC).card = 1 := by
  apply canonicalFlowPairing_odd_one_each
  all_goals decide

example : (flowResidualPorts (canonicalFlowPairing invalidFlow)).card = 2 := by
  rw [canonicalFlowPairing_residual_card]
  decide

example :
    (flowResidualPortsWithLabel (canonicalFlowPairing invalidFlow) deltaB).card = 1 := by
  rw [flowResidualPorts_canonical_card_by_label]
  decide

example :
    (flowResidualPortsWithLabel (canonicalFlowPairing invalidFlow) deltaC).card = 1 := by
  rw [flowResidualPorts_canonical_card_by_label]
  decide

example :
    canonicalFlowMate duplicateFlow ⟨0, by decide⟩ = ⟨1, by decide⟩ := by
  have hempty : flowResidualPorts (canonicalFlowPairing duplicateFlow) = ∅ := by
    apply canonicalFlowPairing_even_perfect
    all_goals decide
  have hready := canonicalFlowPairing_transition_ready duplicateFlow
    ⟨0, by decide⟩ (by rw [hempty]; simp)
  apply Fin.ext
  change (canonicalFlowMate duplicateFlow ⟨0, by decide⟩).val = 1
  have hne : canonicalFlowMate duplicateFlow ⟨0, by decide⟩ ≠
      (⟨0, by decide⟩ : Fin duplicateFlow.arity) := hready.1
  have hneval : (canonicalFlowMate duplicateFlow ⟨0, by decide⟩).val ≠ 0 := by
    intro h
    apply hne
    apply Fin.ext
    exact h
  have hlt : (canonicalFlowMate duplicateFlow ⟨0, by decide⟩).val < 2 := by
    simpa [duplicateFlow] using
      (canonicalFlowMate duplicateFlow ⟨0, by decide⟩).isLt
  omega

example :
    canonicalFlowMate duplicateFlow ⟨1, by decide⟩ = ⟨0, by decide⟩ := by
  have hempty : flowResidualPorts (canonicalFlowPairing duplicateFlow) = ∅ := by
    apply canonicalFlowPairing_even_perfect
    all_goals decide
  have hready := canonicalFlowPairing_transition_ready duplicateFlow
    ⟨1, by decide⟩ (by rw [hempty]; simp)
  apply Fin.ext
  change (canonicalFlowMate duplicateFlow ⟨1, by decide⟩).val = 0
  have hne : canonicalFlowMate duplicateFlow ⟨1, by decide⟩ ≠
      (⟨1, by decide⟩ : Fin duplicateFlow.arity) := hready.1
  have hneval : (canonicalFlowMate duplicateFlow ⟨1, by decide⟩).val ≠ 1 := by
    intro h
    apply hne
    apply Fin.ext
    exact h
  have hlt : (canonicalFlowMate duplicateFlow ⟨1, by decide⟩).val < 2 := by
    simpa [duplicateFlow] using
      (canonicalFlowMate duplicateFlow ⟨1, by decide⟩).isLt
  omega

example :
    canonicalFlowMate duplicateFlow ⟨0, by decide⟩ ≠ ⟨0, by decide⟩ := by
  have hempty : flowResidualPorts (canonicalFlowPairing duplicateFlow) = ∅ := by
    apply canonicalFlowPairing_even_perfect
    all_goals decide
  exact (canonicalFlowPairing_transition_ready duplicateFlow
    ⟨0, by decide⟩ (by rw [hempty]; simp)).1

def contactA : BoundaryContact := { inside := 0, outside := deltaA }
def contactB : BoundaryContact := { inside := 0, outside := deltaB }
def contactC : BoundaryContact := { inside := 0, outside := deltaC }

def evenSignature : BoundarySignature where
  arity := 6
  contact := ![contactA, contactA, contactB, contactB, contactC, contactC]
  proper := by intro i; fin_cases i <;> decide

example (i : Fin evenSignature.arity) :
    (canonicalBoundaryPairing evenSignature).mate i =
      (canonicalFlowPairing evenSignature.toFlowSignature).mate i :=
  canonicalBoundaryPairing_mate_eq_canonicalFlowPairing_mate evenSignature i

example :
    flowResidualPorts (canonicalFlowPairing evenSignature.toFlowSignature) =
      residualPorts (canonicalBoundaryPairing evenSignature) :=
  canonicalFlowResidual_toFlowSignature evenSignature

example (P : BoundaryPairing evenSignature) :
    flowResidualPorts P.toFlowPairing = residualPorts P :=
  flowResidualPorts_toFlowPairing P

example (F : FlowSignature) (i : Fin F.arity)
    (hi : i ∉ flowResidualPorts (canonicalFlowPairing F)) :
    canonicalFlowMate F i ≠ i ∧
      F.label (canonicalFlowMate F i) = F.label i ∧
        canonicalFlowMate F (canonicalFlowMate F i) = i :=
  canonicalFlowPairing_transition_ready F i hi

#print axioms DkMath.Tromino.flowFiberMate_involutive
#print axioms DkMath.Tromino.flowFiberResidualPorts_card
#print axioms DkMath.Tromino.flowResidualPorts_canonical_card_by_label
#print axioms DkMath.Tromino.canonicalFlowPairing_residual_card
#print axioms DkMath.Tromino.canonicalFlowPairing_conserved_decomposition
#print axioms DkMath.Tromino.canonicalBoundaryPairing_mate_eq_canonicalFlowPairing_mate
#print axioms DkMath.Tromino.canonicalFlowResidual_toFlowSignature

end DkMathTest.Tromino.FlowPairingAxiomAudit
