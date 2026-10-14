/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowPairing
import DkMath.Tromino.TransitionGraph

#print "file: DkMath.Tromino.FlowTransition"

/-!
# The flow-network transition graph

This is the label-aware version of `TransitionGraph`. A crossing moves a port
to another region and a perfect local pairing moves within the current
region; their composition is a finite permutation preserving the flow label.
The port and boundary presentations are definitionally parallel, so the final
conversion lemmas transport transition facts without changing the finite
combinatorics.
-/

namespace DkMath.Tromino

/-- A finite flow network carrying a nonzero V4 signature at each region. -/
structure FlowNetwork where
  regionCount : Nat
  signature : Fin regionCount → FlowSignature

/-- A dependent region-and-slot port of a flow network. -/
abbrev FlowNetworkPort (N : FlowNetwork) :=
  Sigma (fun r : Fin N.regionCount => Fin (N.signature r).arity)

/-- A region-changing crossing involution preserving the flow label of each
port. -/
structure FlowCrossing (N : FlowNetwork) where
  cross : FlowNetworkPort N → FlowNetworkPort N
  involutive : Function.Involutive cross
  changesRegion : ∀ p, (cross p).1 ≠ p.1
  sameLabel : ∀ p,
    (N.signature (cross p).1).label (cross p).2 =
      (N.signature p.1).label p.2

/-- A closed flow network with perfect local pairings and a label-preserving
crossing involution. -/
structure ClosedFlowNetwork extends FlowNetwork where
  crossing : FlowCrossing toFlowNetwork
  pairing : ∀ r, FlowPairing (toFlowNetwork.signature r)
  perfect : ∀ r, flowResidualPorts (pairing r) = ∅

/-- The crossing permutation on a closed flow network. -/
def flowCrossPort (N : ClosedFlowNetwork) :
    FlowNetworkPort N.toFlowNetwork → FlowNetworkPort N.toFlowNetwork :=
  N.crossing.cross

/-- Flow crossing twice returns to the original port. -/
theorem flowCrossPort_involutive (N : ClosedFlowNetwork) :
    Function.Involutive (flowCrossPort N) := N.crossing.involutive

/-- Flow crossing changes the region index. -/
theorem flowCrossPort_changes_region (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (flowCrossPort N p).1 ≠ p.1 := N.crossing.changesRegion p

/-- Flow crossing preserves the V4 edge label. -/
theorem flowCrossPort_sameLabel (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (N.toFlowNetwork.signature (flowCrossPort N p).1).label (flowCrossPort N p).2 =
      (N.toFlowNetwork.signature p.1).label p.2 := N.crossing.sameLabel p

/-- A flow crossing port is not fixed. -/
theorem flowCrossPort_ne (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) : flowCrossPort N p ≠ p := by
  intro h
  exact flowCrossPort_changes_region N p (congrArg Sigma.fst h)

/-- The local pairing involution in a flow region. -/
def flowLocalMatePort (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) : FlowNetworkPort N.toFlowNetwork :=
  ⟨p.1, (N.pairing p.1).mate p.2⟩

/-- Flow local pairing twice returns to the original port. -/
theorem flowLocalMatePort_involutive (N : ClosedFlowNetwork) :
    Function.Involutive (flowLocalMatePort N) := by
  intro p
  cases p with
  | mk r i =>
    change (⟨r, (N.pairing r).mate ((N.pairing r).mate i)⟩ :
      FlowNetworkPort N.toFlowNetwork) = ⟨r, i⟩
    exact Sigma.ext rfl (heq_of_eq ((N.pairing r).involutive i))

/-- Flow local pairing preserves the region index. -/
theorem flowLocalMatePort_region (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (flowLocalMatePort N p).1 = p.1 := rfl

/-- Flow local pairing preserves the V4 label. -/
theorem flowLocalMatePort_sameLabel (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (N.toFlowNetwork.signature p.1).label (flowLocalMatePort N p).2 =
      (N.toFlowNetwork.signature p.1).label p.2 :=
  (N.pairing p.1).sameLabel p.2

/-- Perfect flow pairing has no fixed port. -/
theorem flowLocalMatePort_ne (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) : flowLocalMatePort N p ≠ p := by
  intro h
  have hnot : p.2 ∉ flowResidualPorts (N.pairing p.1) := by
    rw [N.perfect p.1]
    simp
  apply flowMate_ne_of_not_mem_residualPorts (N.pairing p.1) hnot
  exact eq_of_heq ((Sigma.mk.inj_iff.mp h).2)

/-- Flow crossing and local pairing give distinct neighbors. -/
theorem flowCrossPort_ne_localMatePort (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    flowCrossPort N p ≠ flowLocalMatePort N p := by
  intro h
  apply flowCrossPort_changes_region N p
  calc
    (flowCrossPort N p).1 = (flowLocalMatePort N p).1 := congrArg Sigma.fst h
    _ = p.1 := rfl

/-- The two flow-transition neighbors obtained from crossing and local pairing. -/
def flowTransitionNeighbors (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    Finset (FlowNetworkPort N.toFlowNetwork) :=
  {flowCrossPort N p, flowLocalMatePort N p}

/-- Every flow transition vertex has exactly two neighbors. -/
theorem flowTransitionNeighbors_card (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (flowTransitionNeighbors N p).card = 2 := by
  simp [flowTransitionNeighbors, flowCrossPort_ne_localMatePort N p]

/-- Undirected adjacency generated by the two involutive flow moves. -/
def FlowTransitionAdj (N : ClosedFlowNetwork)
    (p q : FlowNetworkPort N.toFlowNetwork) : Prop :=
  q = flowCrossPort N p ∨ q = flowLocalMatePort N p

/-- Flow adjacency is membership in the two-neighbor set. -/
theorem flowTransitionAdj_iff_mem_flowTransitionNeighbors
    (N : ClosedFlowNetwork) (p q : FlowNetworkPort N.toFlowNetwork) :
    FlowTransitionAdj N p q ↔ q ∈ flowTransitionNeighbors N p := by
  simp [FlowTransitionAdj, flowTransitionNeighbors]

/-- Flow transition adjacency is symmetric. -/
theorem flowTransitionAdj_symm (N : ClosedFlowNetwork)
    {p q : FlowNetworkPort N.toFlowNetwork} :
    FlowTransitionAdj N p q → FlowTransitionAdj N q p := by
  rintro (rfl | rfl)
  · exact Or.inl (flowCrossPort_involutive N p).symm
  · exact Or.inr (flowLocalMatePort_involutive N p).symm

/-- Flow transition adjacency has no loops. -/
theorem flowTransitionAdj_irrefl (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    ¬ FlowTransitionAdj N p p := by
  intro h
  rcases h with h | h
  · exact flowCrossPort_ne N p h.symm
  · exact flowLocalMatePort_ne N p h.symm

/-- The flow transition graph is 2-regular. -/
theorem flowTransitionAdj_degree_two (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    (flowTransitionNeighbors N p).card = 2 :=
  flowTransitionNeighbors_card N p

/-- One directed flow transition: crossing followed by local pairing in the new
region. -/
def flowTransitionStep (N : ClosedFlowNetwork) :
    FlowNetworkPort N.toFlowNetwork → FlowNetworkPort N.toFlowNetwork :=
  fun p => flowLocalMatePort N (flowCrossPort N p)

/-- The inverse flow transition, reversing the order of the two moves. -/
def flowTransitionStepInv (N : ClosedFlowNetwork) :
    FlowNetworkPort N.toFlowNetwork → FlowNetworkPort N.toFlowNetwork :=
  fun p => flowCrossPort N (flowLocalMatePort N p)

/-- The inverse is a left inverse of the flow transition. -/
theorem flowTransitionStepInv_left (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    flowTransitionStepInv N (flowTransitionStep N p) = p := by
  simp only [flowTransitionStepInv, flowTransitionStep]
  rw [flowLocalMatePort_involutive, flowCrossPort_involutive]

/-- The inverse is a right inverse of the flow transition. -/
theorem flowTransitionStepInv_right (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    flowTransitionStep N (flowTransitionStepInv N p) = p := by
  simp only [flowTransitionStep, flowTransitionStepInv]
  rw [flowCrossPort_involutive, flowLocalMatePort_involutive]

/-- The flow transition step is injective. -/
theorem flowTransitionStep_injective (N : ClosedFlowNetwork) :
    Function.Injective (flowTransitionStep N) := by
  intro p q h
  have h' := congrArg (flowTransitionStepInv N) h
  rw [flowTransitionStepInv_left N p, flowTransitionStepInv_left N q] at h'
  exact h'

/-- The flow transition step is surjective. -/
theorem flowTransitionStep_surjective (N : ClosedFlowNetwork) :
    Function.Surjective (flowTransitionStep N) := by
  intro p
  exact ⟨flowTransitionStepInv N p, flowTransitionStepInv_right N p⟩

/-- Package the flow transition and its inverse as a finite permutation. -/
def flowTransitionEquiv (N : ClosedFlowNetwork) :
    FlowNetworkPort N.toFlowNetwork ≃ FlowNetworkPort N.toFlowNetwork where
  toFun := flowTransitionStep N
  invFun := flowTransitionStepInv N
  left_inv := flowTransitionStepInv_left N
  right_inv := flowTransitionStepInv_right N

/-- One flow transition preserves the V4 label. -/
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

/-- Every flow transition iterate preserves the V4 label. -/
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

/-- Finiteness of the flow-port permutation gives a positive return time for
every flow port. -/
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

/-- A periodic flow orbit returns with its initial V4 label invariant. -/
theorem flowTransitionStep_periodic_sameLabel (N : ClosedFlowNetwork)
    (p : FlowNetworkPort N.toFlowNetwork) :
    ∃ n : Nat, 0 < n ∧ (flowTransitionStep N)^[n] p = p ∧
      (N.toFlowNetwork.signature ((flowTransitionStep N)^[n] p).1).label
          ((flowTransitionStep N)^[n] p).2 =
        (N.toFlowNetwork.signature p.1).label p.2 := by
  rcases flowTransitionStep_periodic N p with ⟨n, hn, hcycle⟩
  exact ⟨n, hn, hcycle, flowTransitionStep_iterate_sameLabel N n p⟩

/-- Forget boundary contact representatives and retain only the flow signatures
of a boundary network. -/
def BoundaryNetwork.toFlowNetwork (N : BoundaryNetwork) : FlowNetwork where
  regionCount := N.regionCount
  signature := fun r => (N.signature r).toFlowSignature

/-- Transport a boundary crossing to the definitionally parallel flow
presentation. -/
def BoundaryCrossing.toFlowCrossing {N : BoundaryNetwork}
    (C : BoundaryCrossing N) : FlowCrossing N.toFlowNetwork where
  cross := C.cross
  involutive := C.cross_involutive
  changesRegion := C.cross_changes_region
  sameLabel := C.cross_sameLabel

/-- Transport a closed boundary network, including its perfect pairings, into
the flow presentation. -/
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

/-- The transported flow crossing agrees with the boundary crossing. -/
theorem flowCrossPort_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    flowCrossPort N.toClosedFlowNetwork p = crossPort N p := rfl

/-- The transported flow mate agrees with the boundary mate. -/
theorem flowLocalMatePort_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    flowLocalMatePort N.toClosedFlowNetwork p = localMatePort N p := rfl

/-- The transported flow transition agrees with the boundary transition. -/
theorem flowTransitionStep_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    flowTransitionStep N.toClosedFlowNetwork p = transitionStep N p := rfl

/-- Label preservation transports across the boundary/flow encoding. -/
theorem flowTransitionStep_sameLabel_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    (N.toFlowNetwork.signature (flowTransitionStep N.toClosedFlowNetwork p).1).label
        (flowTransitionStep N.toClosedFlowNetwork p).2 =
      boundaryDelta (N.toBoundaryNetwork.signature (transitionStep N p).1)
        (transitionStep N p).2 := by
  rfl

/-- Periodicity transports from the boundary network to the flow network. -/
theorem flowTransitionStep_periodic_toFlowNetwork (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    ∃ n : Nat, 0 < n ∧
      (flowTransitionStep N.toClosedFlowNetwork)^[n] p = p := by
  exact flowTransitionStep_periodic N.toClosedFlowNetwork p

end DkMath.Tromino
