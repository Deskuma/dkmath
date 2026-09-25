/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.TransitionGraph

#print "file: DkMathTest.Tromino.TransitionGraphAxiomAudit"

namespace DkMathTest.Tromino.TransitionGraphAxiomAudit

open DkMath.Tromino

def contactA : BoundaryContact := { inside := 0, outside := deltaA }

def aaSignature : BoundarySignature where
  arity := 2
  contact := ![contactA, contactA]
  proper := by intro i; fin_cases i <;> decide

def twoRegionNetwork : BoundaryNetwork where
  regionCount := 2
  signature := fun _ => aaSignature

def swapRegion (r : Fin 2) : Fin 2 := ⟨1 - r.val, by omega⟩

theorem swapRegion_involutive (r : Fin 2) : swapRegion (swapRegion r) = r := by
  apply Fin.ext
  dsimp [swapRegion]
  omega

theorem swapRegion_ne (r : Fin 2) : swapRegion r ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [swapRegion] at hv
  omega

def twoRegionCrossing : BoundaryCrossing twoRegionNetwork where
  cross := fun p => ⟨swapRegion p.1, p.2⟩
  cross_involutive := by
    intro p
    apply Sigma.ext
    · exact swapRegion_involutive p.1
    · exact heq_of_eq rfl
  cross_changes_region := by
    intro p
    exact swapRegion_ne p.1
  cross_sameLabel := by
    intro p
    rfl

def twoRegionClosed : ClosedBoundaryNetwork where
  toBoundaryNetwork := twoRegionNetwork
  crossing := twoRegionCrossing
  pairing := fun _ => canonicalBoundaryPairing aaSignature
  perfect := by
    intro r
    change residualPorts (canonicalBoundaryPairing aaSignature) = ∅
    apply canonicalBoundaryPairing_even_perfect
    all_goals decide

example : Fintype.card (NetworkPort twoRegionClosed.toBoundaryNetwork) = 4 := by
  decide

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    crossPort twoRegionClosed (crossPort twoRegionClosed p) = p :=
  crossPort_involutive twoRegionClosed p

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    localMatePort twoRegionClosed (localMatePort twoRegionClosed p) = p :=
  localMatePort_involutive twoRegionClosed p

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    (transitionNeighbors twoRegionClosed p).card = 2 :=
  transitionNeighbors_card twoRegionClosed p

example {p q : NetworkPort twoRegionClosed.toBoundaryNetwork}
    (h : TransitionAdj twoRegionClosed p q) : TransitionAdj twoRegionClosed q p :=
  transitionAdj_symm twoRegionClosed h

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    ¬ TransitionAdj twoRegionClosed p p :=
  transitionAdj_irrefl twoRegionClosed p

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    transitionStepInv twoRegionClosed (transitionStep twoRegionClosed p) = p :=
  transitionStepInv_left twoRegionClosed p

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    ∃ n : Nat, 0 < n ∧ (transitionStep twoRegionClosed)^[n] p = p :=
  transitionStep_periodic twoRegionClosed p

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    boundaryDelta (twoRegionClosed.toBoundaryNetwork.signature
      (transitionStep twoRegionClosed p).1) (transitionStep twoRegionClosed p).2 =
      boundaryDelta (twoRegionClosed.toBoundaryNetwork.signature p.1) p.2 :=
  transitionStep_sameLabel twoRegionClosed p

#print axioms DkMath.Tromino.crossPort_involutive
#print axioms DkMath.Tromino.localMatePort_involutive
#print axioms DkMath.Tromino.transitionNeighbors_card
#print axioms DkMath.Tromino.transitionAdj_symm
#print axioms DkMath.Tromino.transitionStep_injective
#print axioms DkMath.Tromino.transitionStep_surjective
#print axioms DkMath.Tromino.transitionStep_periodic
#print axioms DkMath.Tromino.transitionStep_iterate_sameLabel

end DkMathTest.Tromino.TransitionGraphAxiomAudit
