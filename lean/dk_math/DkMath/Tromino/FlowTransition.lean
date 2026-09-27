/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowPairing
import DkMath.Tromino.TransitionGraph

#print "file: DkMath.Tromino.FlowTransition"

namespace DkMath.Tromino

structure FlowNetwork where
  regionCount : Nat
  signature : Fin regionCount → FlowSignature

abbrev FlowNetworkPort (N : FlowNetwork) :=
  Sigma (fun r : Fin N.regionCount => Fin (N.signature r).arity)

structure FlowCrossing (N : FlowNetwork) where
  cross : FlowNetworkPort N → FlowNetworkPort N
  involutive : Function.Involutive cross
  changesRegion : ∀ p, (cross p).1 ≠ p.1
  sameLabel : ∀ p,
    (N.signature (cross p).1).label (cross p).2 =
      (N.signature p.1).label p.2

structure ClosedFlowNetwork extends FlowNetwork where
  crossing : FlowCrossing toFlowNetwork
  pairing : ∀ r, FlowPairing (toFlowNetwork.signature r)
  perfect : ∀ r, flowResidualPorts (pairing r) = ∅

def flowCrossPort (N : ClosedFlowNetwork) :
    FlowNetworkPort N.toFlowNetwork → FlowNetworkPort N.toFlowNetwork :=
  N.crossing.cross

theorem flowCrossPort_involutive (N : ClosedFlowNetwork) :
    Function.Involutive (flowCrossPort N) := N.crossing.involutive

theorem flowCrossPort_changes_region (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (flowCrossPort N p).1 ≠ p.1 := N.crossing.changesRegion p

theorem flowCrossPort_sameLabel (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (N.toFlowNetwork.signature (flowCrossPort N p).1).label (flowCrossPort N p).2 =
      (N.toFlowNetwork.signature p.1).label p.2 := N.crossing.sameLabel p

theorem flowCrossPort_ne (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) : flowCrossPort N p ≠ p := by
  intro h
  exact flowCrossPort_changes_region N p (congrArg Sigma.fst h)

def flowLocalMatePort (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) : FlowNetworkPort N.toFlowNetwork :=
  ⟨p.1, (N.pairing p.1).mate p.2⟩

theorem flowLocalMatePort_involutive (N : ClosedFlowNetwork) :
    Function.Involutive (flowLocalMatePort N) := by
  intro p
  cases p with
  | mk r i =>
    change (⟨r, (N.pairing r).mate ((N.pairing r).mate i)⟩ :
      FlowNetworkPort N.toFlowNetwork) = ⟨r, i⟩
    exact Sigma.ext rfl (heq_of_eq ((N.pairing r).involutive i))

theorem flowLocalMatePort_region (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (flowLocalMatePort N p).1 = p.1 := rfl

theorem flowLocalMatePort_sameLabel (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (N.toFlowNetwork.signature p.1).label (flowLocalMatePort N p).2 =
      (N.toFlowNetwork.signature p.1).label p.2 :=
  (N.pairing p.1).sameLabel p.2

theorem flowLocalMatePort_ne (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) : flowLocalMatePort N p ≠ p := by
  intro h
  have hnot : p.2 ∉ flowResidualPorts (N.pairing p.1) := by
    rw [N.perfect p.1]
    simp
  apply flowMate_ne_of_not_mem_residualPorts (N.pairing p.1) hnot
  exact eq_of_heq ((Sigma.mk.inj_iff.mp h).2)

theorem flowCrossPort_ne_localMatePort (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    flowCrossPort N p ≠ flowLocalMatePort N p := by
  intro h
  apply flowCrossPort_changes_region N p
  calc
    (flowCrossPort N p).1 = (flowLocalMatePort N p).1 := congrArg Sigma.fst h
    _ = p.1 := rfl

def flowTransitionNeighbors (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    Finset (FlowNetworkPort N.toFlowNetwork) :=
  {flowCrossPort N p, flowLocalMatePort N p}

theorem flowTransitionNeighbors_card (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (flowTransitionNeighbors N p).card = 2 := by
  simp [flowTransitionNeighbors, flowCrossPort_ne_localMatePort N p]

def FlowTransitionAdj (N : ClosedFlowNetwork)
    (p q : FlowNetworkPort N.toFlowNetwork) : Prop :=
  q = flowCrossPort N p ∨ q = flowLocalMatePort N p

theorem flowTransitionAdj_iff_mem_flowTransitionNeighbors
    (N : ClosedFlowNetwork) (p q : FlowNetworkPort N.toFlowNetwork) :
    FlowTransitionAdj N p q ↔ q ∈ flowTransitionNeighbors N p := by
  simp [FlowTransitionAdj, flowTransitionNeighbors]

theorem flowTransitionAdj_symm (N : ClosedFlowNetwork)
    {p q : FlowNetworkPort N.toFlowNetwork} :
    FlowTransitionAdj N p q → FlowTransitionAdj N q p := by
  rintro (rfl | rfl)
  · exact Or.inl (flowCrossPort_involutive N p).symm
  · exact Or.inr (flowLocalMatePort_involutive N p).symm

theorem flowTransitionAdj_irrefl (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    ¬ FlowTransitionAdj N p p := by
  intro h
  rcases h with h | h
  · exact flowCrossPort_ne N p h.symm
  · exact flowLocalMatePort_ne N p h.symm

theorem flowTransitionAdj_degree_two (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (flowTransitionNeighbors N p).card = 2 :=
  flowTransitionNeighbors_card N p

def flowTransitionStep (N : ClosedFlowNetwork) :
    FlowNetworkPort N.toFlowNetwork → FlowNetworkPort N.toFlowNetwork :=
  fun p => flowLocalMatePort N (flowCrossPort N p)

def flowTransitionStepInv (N : ClosedFlowNetwork) :
    FlowNetworkPort N.toFlowNetwork → FlowNetworkPort N.toFlowNetwork :=
  fun p => flowCrossPort N (flowLocalMatePort N p)

theorem flowTransitionStepInv_left (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    flowTransitionStepInv N (flowTransitionStep N p) = p := by
  simp only [flowTransitionStepInv, flowTransitionStep]
  rw [flowLocalMatePort_involutive, flowCrossPort_involutive]

theorem flowTransitionStepInv_right (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    flowTransitionStep N (flowTransitionStepInv N p) = p := by
  simp only [flowTransitionStep, flowTransitionStepInv]
  rw [flowCrossPort_involutive, flowLocalMatePort_involutive]

theorem flowTransitionStep_injective (N : ClosedFlowNetwork) :
    Function.Injective (flowTransitionStep N) := by
  intro p q h
  have h' := congrArg (flowTransitionStepInv N) h
  rw [flowTransitionStepInv_left N p, flowTransitionStepInv_left N q] at h'
  exact h'

theorem flowTransitionStep_surjective (N : ClosedFlowNetwork) :
    Function.Surjective (flowTransitionStep N) := by
  intro p
  exact ⟨flowTransitionStepInv N p, flowTransitionStepInv_right N p⟩

def flowTransitionEquiv (N : ClosedFlowNetwork) :
    FlowNetworkPort N.toFlowNetwork ≃ FlowNetworkPort N.toFlowNetwork where
  toFun := flowTransitionStep N
  invFun := flowTransitionStepInv N
  left_inv := flowTransitionStepInv_left N
  right_inv := flowTransitionStepInv_right N

theorem flowTransitionStep_sameLabel (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (N.toFlowNetwork.signature (flowTransitionStep N p).1).label
        (flowTransitionStep N p).2 =
      (N.toFlowNetwork.signature p.1).label p.2 := by
  calc
    (N.toFlowNetwork.signature (flowTransitionStep N p).1).label
          (flowTransitionStep N p).2 =
        (N.toFlowNetwork.signature (flowCrossPort N p).1).label
          (flowCrossPort N p).2 :=
      flowLocalMatePort_sameLabel N (flowCrossPort N p)
    _ = (N.toFlowNetwork.signature p.1).label p.2 :=
      flowCrossPort_sameLabel N p

theorem flowTransitionStep_iterate_sameLabel (N : ClosedFlowNetwork)
    (n : Nat) (p : FlowNetworkPort N.toFlowNetwork) :
    (N.toFlowNetwork.signature ((flowTransitionStep N)^[n] p).1).label
        ((flowTransitionStep N)^[n] p).2 =
      (N.toFlowNetwork.signature p.1).label p.2 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    calc
      (N.toFlowNetwork.signature ((flowTransitionStep N)^[n]
          (flowTransitionStep N p)).1).label
          ((flowTransitionStep N)^[n] (flowTransitionStep N p)).2 =
          (N.toFlowNetwork.signature (flowTransitionStep N p).1).label
            (flowTransitionStep N p).2 :=
        ih (flowTransitionStep N p)
      _ = (N.toFlowNetwork.signature p.1).label p.2 :=
        flowTransitionStep_sameLabel N p

theorem flowTransitionStep_periodic (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    ∃ n : Nat, 0 < n ∧ (flowTransitionStep N)^[n] p = p := by
  let e : Equiv.Perm (FlowNetworkPort N.toFlowNetwork) := flowTransitionEquiv N
  refine ⟨orderOf e, orderOf_pos e, ?_⟩
  have hpow : e ^ orderOf e = 1 := pow_orderOf_eq_one e
  have happly := congrArg
    (fun f : Equiv.Perm (FlowNetworkPort N.toFlowNetwork) => f p) hpow
  rw [Equiv.Perm.coe_pow] at happly
  change ((flowTransitionStep N)^[orderOf e]) p = p at happly
  exact happly

theorem flowTransitionStep_periodic_sameLabel (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    ∃ n : Nat, 0 < n ∧ (flowTransitionStep N)^[n] p = p ∧
      (N.toFlowNetwork.signature ((flowTransitionStep N)^[n] p).1).label
          ((flowTransitionStep N)^[n] p).2 =
        (N.toFlowNetwork.signature p.1).label p.2 := by
  rcases flowTransitionStep_periodic N p with ⟨n, hn, hcycle⟩
  exact ⟨n, hn, hcycle, flowTransitionStep_iterate_sameLabel N n p⟩

def BoundaryNetwork.toFlowNetwork (N : BoundaryNetwork) : FlowNetwork where
  regionCount := N.regionCount
  signature := fun r => (N.signature r).toFlowSignature

def BoundaryCrossing.toFlowCrossing {N : BoundaryNetwork}
    (C : BoundaryCrossing N) : FlowCrossing N.toFlowNetwork where
  cross := C.cross
  involutive := C.cross_involutive
  changesRegion := C.cross_changes_region
  sameLabel := C.cross_sameLabel

def ClosedBoundaryNetwork.toClosedFlowNetwork (N : ClosedBoundaryNetwork) :
    ClosedFlowNetwork where
  toFlowNetwork := N.toBoundaryNetwork.toFlowNetwork
  crossing := N.crossing.toFlowCrossing
  pairing := fun r => (N.pairing r).toFlowPairing
  perfect := by
    intro r
    change flowResidualPorts
      ((N.pairing (show Fin N.regionCount from r)).toFlowPairing) = ∅
    rw [flowResidualPorts_toFlowPairing]
    exact N.perfect r

theorem flowCrossPort_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    flowCrossPort N.toClosedFlowNetwork p = crossPort N p := rfl

theorem flowLocalMatePort_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    flowLocalMatePort N.toClosedFlowNetwork p = localMatePort N p := rfl

theorem flowTransitionStep_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    flowTransitionStep N.toClosedFlowNetwork p = transitionStep N p := rfl

theorem flowTransitionStep_sameLabel_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    (N.toFlowNetwork.signature (flowTransitionStep N.toClosedFlowNetwork p).1).label
        (flowTransitionStep N.toClosedFlowNetwork p).2 =
      boundaryDelta (N.toBoundaryNetwork.signature (transitionStep N p).1)
        (transitionStep N p).2 := by
  rfl

theorem flowTransitionStep_periodic_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    ∃ n : Nat, 0 < n ∧
      (flowTransitionStep N.toClosedFlowNetwork)^[n] p = p := by
  exact flowTransitionStep_periodic N.toClosedFlowNetwork p

end DkMath.Tromino
