/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.BoundarySignature

#print "file: DkMathTest.Tromino.BoundarySignatureAxiomAudit"

namespace DkMathTest.Tromino.BoundarySignatureAxiomAudit

open DkMath.Tromino

def contactA : BoundaryContact :=
  { inside := 0, outside := deltaA }

def contactB : BoundaryContact :=
  { inside := 0, outside := deltaB }

def contactC : BoundaryContact :=
  { inside := 0, outside := deltaC }

def evenSignature : BoundarySignature where
  arity := 6
  contact := ![contactA, contactA, contactB, contactB, contactC, contactC]
  proper := by
    intro i
    fin_cases i <;> decide

def oddSignature : BoundarySignature where
  arity := 9
  contact :=
    ![contactA, contactA, contactA, contactB, contactB, contactB,
      contactC, contactC, contactC]
  proper := by
    intro i
    fin_cases i <;> decide

def invalidSignature : BoundarySignature where
  arity := 4
  contact := ![contactA, contactA, contactB, contactC]
  proper := by
    intro i
    fin_cases i <;> decide

def duplicateSignature : BoundarySignature where
  arity := 2
  contact := ![contactA, contactA]
  proper := by
    intro i
    fin_cases i <;> decide

example (contact : BoundaryContact) :
    contactDelta contact = 0 ↔ contact.inside = contact.outside :=
  contactDelta_eq_zero_iff contact

example : deltaA ≠ 0 ∧ deltaB ≠ 0 ∧ deltaC ≠ 0 := by
  exact ⟨deltaA_ne_zero, deltaB_ne_zero, deltaC_ne_zero⟩

example : deltaA + deltaB = deltaC ∧
    deltaB + deltaC = deltaA ∧ deltaC + deltaA = deltaB := by
  exact ⟨deltaA_add_deltaB, deltaB_add_deltaC, deltaC_add_deltaA⟩

example (S : BoundarySignature) (i : Fin S.arity) :
    boundaryDelta S i ≠ 0 :=
  boundaryDelta_ne_zero S i

example (S : BoundarySignature) :
    boundaryLabelCount S deltaA + boundaryLabelCount S deltaB +
        boundaryLabelCount S deltaC = S.arity :=
  boundaryLabelCount_sum S

example : BoundaryConserved emptyBoundarySignature :=
  emptyBoundarySignature_conserved

example : boundaryLabelCount emptyBoundarySignature deltaA = 0 := by decide

example : boundaryLabelCount evenSignature deltaA = 2 := by decide
example : boundaryLabelCount evenSignature deltaB = 2 := by decide
example : boundaryLabelCount evenSignature deltaC = 2 := by decide

example : BoundaryConserved evenSignature := by
  apply (boundaryConserved_iff_parity evenSignature).mpr
  decide

example : boundaryLabelCount oddSignature deltaA = 3 := by decide
example : boundaryLabelCount oddSignature deltaB = 3 := by decide
example : boundaryLabelCount oddSignature deltaC = 3 := by decide

example : BoundaryConserved oddSignature := by
  apply (boundaryConserved_iff_parity oddSignature).mpr
  decide

example : boundaryLabelCount invalidSignature deltaA = 2 := by decide
example : boundaryLabelCount invalidSignature deltaB = 1 := by decide
example : boundaryLabelCount invalidSignature deltaC = 1 := by decide

example : ¬ BoundaryConserved invalidSignature := by
  change ¬ boundarySum invalidSignature = 0
  decide

example : boundaryLabelCount duplicateSignature deltaA = 2 := by decide

example : (forbiddenExchangeSet {contactA}).card = 1 := by
  simp [forbiddenExchangeSet, contactA, forbiddenDelta]

example : BoundaryConserved evenSignature →
    ((boundaryLabelCount evenSignature deltaA % 2 = 0 ∧
        boundaryLabelCount evenSignature deltaB % 2 = 0 ∧
          boundaryLabelCount evenSignature deltaC % 2 = 0) ∨
      (boundaryLabelCount evenSignature deltaA % 2 = 1 ∧
        boundaryLabelCount evenSignature deltaB % 2 = 1 ∧
          boundaryLabelCount evenSignature deltaC % 2 = 1)) :=
  boundaryConserved_even_or_odd evenSignature

#print axioms DkMath.Tromino.contactDelta_eq_zero_iff
#print axioms DkMath.Tromino.boundaryLabelCount_sum
#print axioms DkMath.Tromino.boundarySum_fst
#print axioms DkMath.Tromino.boundarySum_snd
#print axioms DkMath.Tromino.boundaryConserved_iff_parity
#print axioms DkMath.Tromino.boundaryConserved_even_or_odd
#print axioms DkMath.Tromino.emptyBoundarySignature_conserved

end DkMathTest.Tromino.BoundarySignatureAxiomAudit
