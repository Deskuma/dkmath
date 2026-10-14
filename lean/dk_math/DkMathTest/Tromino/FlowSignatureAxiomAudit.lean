/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowSignature

#print "file: DkMathTest.Tromino.FlowSignatureAxiomAudit"

namespace DkMathTest.Tromino.FlowSignatureAxiomAudit

open DkMath.Tromino

def emptyFlow : FlowSignature where
  arity := 0
  label := fun i => Fin.elim0 i
  nonzero := by intro i; exact Fin.elim0 i

def evenFlow : FlowSignature where
  arity := 6
  label := ![deltaA, deltaA, deltaB, deltaB, deltaC, deltaC]
  nonzero := by intro i; fin_cases i <;> simp [deltaA_ne_zero, deltaB_ne_zero, deltaC_ne_zero]

def oddFlow : FlowSignature where
  arity := 9
  label := ![deltaA, deltaA, deltaA, deltaB, deltaB, deltaB,
    deltaC, deltaC, deltaC]
  nonzero := by intro i; fin_cases i <;> simp [deltaA_ne_zero, deltaB_ne_zero, deltaC_ne_zero]

def invalidFlow : FlowSignature where
  arity := 4
  label := ![deltaA, deltaA, deltaB, deltaC]
  nonzero := by intro i; fin_cases i <;> simp [deltaA_ne_zero, deltaB_ne_zero, deltaC_ne_zero]

def duplicateFlow : FlowSignature where
  arity := 2
  label := ![deltaA, deltaA]
  nonzero := by intro i; fin_cases i <;> exact deltaA_ne_zero

example : FlowConserved emptyFlow := by
  change Finset.sum (Finset.univ : Finset (Fin 0)) emptyFlow.label = 0
  rw [Finset.univ_eq_empty]
  rfl

example : FlowConserved evenFlow := by
  change flowSum evenFlow = 0
  decide

example : FlowConserved oddFlow := by
  change flowSum oddFlow = 0
  decide

example : ¬ FlowConserved invalidFlow := by
  change ¬ flowSum invalidFlow = 0
  decide

example : flowLabelCount evenFlow deltaA = 2 := by decide
example : flowLabelCount evenFlow deltaB = 2 := by decide
example : flowLabelCount evenFlow deltaC = 2 := by decide
example : flowLabelCount oddFlow deltaA = 3 := by decide
example : flowLabelCount oddFlow deltaB = 3 := by decide
example : flowLabelCount oddFlow deltaC = 3 := by decide
example : flowLabelCount duplicateFlow deltaA = 2 := by decide

example : flowLabelCount evenFlow 0 = 0 := flowLabelCount_zero evenFlow

example : flowLabelCount evenFlow deltaA + flowLabelCount evenFlow deltaB +
    flowLabelCount evenFlow deltaC = evenFlow.arity := flowLabelCount_sum evenFlow

example : FlowConserved evenFlow →
    (flowLabelCount evenFlow deltaA % 2 = 0 ∧
      flowLabelCount evenFlow deltaB % 2 = 0 ∧ flowLabelCount evenFlow deltaC % 2 = 0) := by
  intro h
  exact (flowConserved_even_or_odd evenFlow h).resolve_right (by decide)

example : FlowConserved oddFlow →
    (flowLabelCount oddFlow deltaA % 2 = 1 ∧
      flowLabelCount oddFlow deltaB % 2 = 1 ∧ flowLabelCount oddFlow deltaC % 2 = 1) := by
  intro h
  exact (flowConserved_even_or_odd oddFlow h).resolve_left (by decide)

def contactA : BoundaryContact := { inside := 0, outside := deltaA }
def contactB : BoundaryContact := { inside := 0, outside := deltaB }
def contactC : BoundaryContact := { inside := 0, outside := deltaC }

def evenBoundarySignature : BoundarySignature where
  arity := 6
  contact := ![contactA, contactA, contactB, contactB, contactC, contactC]
  proper := by intro i; fin_cases i <;> decide

example (i : Fin evenBoundarySignature.arity) :
    evenBoundarySignature.toFlowSignature.label i = boundaryDelta evenBoundarySignature i :=
  BoundarySignature.toFlowSignature_label evenBoundarySignature i

example : flowSum evenBoundarySignature.toFlowSignature = boundarySum evenBoundarySignature :=
  flowSum_toFlowSignature evenBoundarySignature

example : FlowConserved evenBoundarySignature.toFlowSignature ↔
    BoundaryConserved evenBoundarySignature :=
  flowConserved_toFlowSignature_iff evenBoundarySignature

example (delta : TrominoState) :
    flowLabelCount evenBoundarySignature.toFlowSignature delta =
      boundaryLabelCount evenBoundarySignature delta :=
  flowLabelCount_toFlowSignature evenBoundarySignature delta

example : BoundaryConserved evenBoundarySignature := by
  change boundarySum evenBoundarySignature = 0
  decide

example : FlowConserved evenBoundarySignature.toFlowSignature := by
  rw [flowConserved_toFlowSignature_iff]
  change boundarySum evenBoundarySignature = 0
  decide

example (gamma : TrominoState) (c : BoundaryContact) :
    contactDelta (exchangeBoundaryContact gamma c) = contactDelta c :=
  contactDelta_exchangeBoundaryContact gamma c

example (x : TrominoState) :
    contactDelta { inside := x, outside := x + deltaA } = deltaA :=
  contactDelta_same_of_translation x deltaA

#print axioms DkMath.Tromino.flowLabelCount_sum
#print axioms DkMath.Tromino.flowSum_fst
#print axioms DkMath.Tromino.flowSum_snd
#print axioms DkMath.Tromino.flowConserved_iff_parity
#print axioms DkMath.Tromino.flowConserved_even_or_odd
#print axioms DkMath.Tromino.flowSum_toFlowSignature
#print axioms DkMath.Tromino.contactDelta_exchangeBoundaryContact

end DkMathTest.Tromino.FlowSignatureAxiomAudit
