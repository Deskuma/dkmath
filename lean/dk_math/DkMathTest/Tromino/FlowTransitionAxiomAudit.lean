/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowTransition

#print "file: DkMathTest.Tromino.FlowTransitionAxiomAudit"

namespace DkMathTest.Tromino.FlowTransitionAxiomAudit

open DkMath.Tromino

def aaFlow : FlowSignature where
  arity := 2
  label := ![deltaA, deltaA]
  nonzero := by
    intro i
    fin_cases i <;> exact deltaA_ne_zero

def twoRegionFlowNetwork : FlowNetwork where
  regionCount := 2
  signature := fun _ => aaFlow

def swapRegion (r : Fin 2) : Fin 2 := ⟨1 - r.val, by omega⟩

theorem swapRegion_involutive (r : Fin 2) :
    swapRegion (swapRegion r) = r := by
  apply Fin.ext
  dsimp [swapRegion]
  omega

theorem swapRegion_ne (r : Fin 2) : swapRegion r ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [swapRegion] at hv
  omega

def twoRegionFlowCrossing : FlowCrossing twoRegionFlowNetwork where
  cross := fun p => ⟨swapRegion p.1, p.2⟩
  involutive := by
    intro p
    apply Sigma.ext
    · exact swapRegion_involutive p.1
    · exact heq_of_eq rfl
  changesRegion := by
    intro p
    exact swapRegion_ne p.1
  sameLabel := by
    intro p
    rfl

def twoRegionFlowClosed : ClosedFlowNetwork where
  toFlowNetwork := twoRegionFlowNetwork
  crossing := twoRegionFlowCrossing
  pairing := fun _ => canonicalFlowPairing aaFlow
  perfect := by
    intro r
    change flowResidualPorts (canonicalFlowPairing aaFlow) = ∅
    apply canonicalFlowPairing_even_perfect
    all_goals decide

example : Fintype.card (FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) = 4 := by
  decide

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    flowCrossPort twoRegionFlowClosed (flowCrossPort twoRegionFlowClosed p) = p :=
  flowCrossPort_involutive twoRegionFlowClosed p

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    flowLocalMatePort twoRegionFlowClosed (flowLocalMatePort twoRegionFlowClosed p) = p :=
  flowLocalMatePort_involutive twoRegionFlowClosed p

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    flowCrossPort twoRegionFlowClosed p ≠ p :=
  flowCrossPort_ne twoRegionFlowClosed p

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    flowLocalMatePort twoRegionFlowClosed p ≠ p :=
  flowLocalMatePort_ne twoRegionFlowClosed p

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    flowCrossPort twoRegionFlowClosed p ≠ flowLocalMatePort twoRegionFlowClosed p :=
  flowCrossPort_ne_localMatePort twoRegionFlowClosed p

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    (flowTransitionNeighbors twoRegionFlowClosed p).card = 2 :=
  flowTransitionNeighbors_card twoRegionFlowClosed p

example {p q : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork}
    (h : FlowTransitionAdj twoRegionFlowClosed p q) :
    FlowTransitionAdj twoRegionFlowClosed q p :=
  flowTransitionAdj_symm twoRegionFlowClosed h

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    ¬ FlowTransitionAdj twoRegionFlowClosed p p :=
  flowTransitionAdj_irrefl twoRegionFlowClosed p

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    (twoRegionFlowClosed.toFlowNetwork.signature
      (flowTransitionStep twoRegionFlowClosed p).1).label
        (flowTransitionStep twoRegionFlowClosed p).2 =
      (twoRegionFlowClosed.toFlowNetwork.signature p.1).label p.2 :=
  flowTransitionStep_sameLabel twoRegionFlowClosed p

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    ∃ n : Nat, 0 < n ∧
      (flowTransitionStep twoRegionFlowClosed)^[n] p = p :=
  flowTransitionStep_periodic twoRegionFlowClosed p

def contactA : BoundaryContact := { inside := 0, outside := deltaA }

def aaSignature : BoundarySignature where
  arity := 2
  contact := ![contactA, contactA]
  proper := by intro i; fin_cases i <;> decide

def twoRegionNetwork : BoundaryNetwork where
  regionCount := 2
  signature := fun _ => aaSignature

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

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    flowCrossPort twoRegionClosed.toClosedFlowNetwork p = crossPort twoRegionClosed p :=
  flowCrossPort_toFlowNetwork twoRegionClosed p

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    flowLocalMatePort twoRegionClosed.toClosedFlowNetwork p =
      localMatePort twoRegionClosed p :=
  flowLocalMatePort_toFlowNetwork twoRegionClosed p

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    flowTransitionStep twoRegionClosed.toClosedFlowNetwork p =
      transitionStep twoRegionClosed p :=
  flowTransitionStep_toFlowNetwork twoRegionClosed p

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    (twoRegionClosed.toClosedFlowNetwork.toFlowNetwork.signature
      (flowTransitionStep twoRegionClosed.toClosedFlowNetwork p).1).label
        (flowTransitionStep twoRegionClosed.toClosedFlowNetwork p).2 =
      boundaryDelta (twoRegionClosed.toBoundaryNetwork.signature
        (transitionStep twoRegionClosed p).1) (transitionStep twoRegionClosed p).2 :=
  flowTransitionStep_sameLabel_toFlowNetwork twoRegionClosed p

example (p : NetworkPort twoRegionClosed.toBoundaryNetwork) :
    ∃ n : Nat, 0 < n ∧
      (flowTransitionStep twoRegionClosed.toClosedFlowNetwork)^[n] p = p :=
  flowTransitionStep_periodic_toFlowNetwork twoRegionClosed p

#print axioms DkMath.Tromino.flowCrossPort_involutive
#print axioms DkMath.Tromino.flowLocalMatePort_involutive
#print axioms DkMath.Tromino.flowTransitionNeighbors_card
#print axioms DkMath.Tromino.flowTransitionAdj_symm
#print axioms DkMath.Tromino.flowTransitionStep_injective
#print axioms DkMath.Tromino.flowTransitionStep_surjective
#print axioms DkMath.Tromino.flowTransitionStep_periodic
#print axioms DkMath.Tromino.flowTransitionStep_iterate_sameLabel
#print axioms DkMath.Tromino.flowTransitionStep_toFlowNetwork

end DkMathTest.Tromino.FlowTransitionAxiomAudit
