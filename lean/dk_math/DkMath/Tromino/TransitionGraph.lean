/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.BoundaryPairing

#print "file: DkMath.Tromino.TransitionGraph"

namespace DkMath.Tromino

structure BoundaryNetwork where
  regionCount : Nat
  signature : Fin regionCount → BoundarySignature

abbrev NetworkPort (N : BoundaryNetwork) :=
  Sigma (fun r : Fin N.regionCount => Fin (N.signature r).arity)

structure BoundaryCrossing (N : BoundaryNetwork) where
  cross : NetworkPort N → NetworkPort N
  cross_involutive : Function.Involutive cross
  cross_changes_region : ∀ p, (cross p).1 ≠ p.1
  cross_sameLabel : ∀ p,
    boundaryDelta (N.signature (cross p).1) (cross p).2 =
      boundaryDelta (N.signature p.1) p.2

structure ClosedBoundaryNetwork extends BoundaryNetwork where
  crossing : BoundaryCrossing toBoundaryNetwork
  pairing : ∀ r, BoundaryPairing (toBoundaryNetwork.signature r)
  perfect : ∀ r, residualPorts (pairing r) = ∅

def crossPort (N : ClosedBoundaryNetwork) :
    NetworkPort N.toBoundaryNetwork → NetworkPort N.toBoundaryNetwork := N.crossing.cross

theorem crossPort_involutive (N : ClosedBoundaryNetwork) :
    Function.Involutive (crossPort N) := N.crossing.cross_involutive

theorem crossPort_changes_region (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) :
    (crossPort N p).1 ≠ p.1 := N.crossing.cross_changes_region p

theorem crossPort_sameLabel (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) :
    boundaryDelta (N.toBoundaryNetwork.signature (crossPort N p).1) (crossPort N p).2 =
      boundaryDelta (N.toBoundaryNetwork.signature p.1) p.2 := N.crossing.cross_sameLabel p

theorem crossPort_ne (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) :
    crossPort N p ≠ p := by
  intro h
  exact crossPort_changes_region N p (congrArg Sigma.fst h)

def localMatePort (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) :
    NetworkPort N.toBoundaryNetwork := ⟨p.1, (N.pairing p.1).mate p.2⟩

theorem localMatePort_involutive (N : ClosedBoundaryNetwork) :
    Function.Involutive (localMatePort N) := by
  intro p
  cases p with
  | mk r i =>
    change (⟨r, (N.pairing r).mate ((N.pairing r).mate i)⟩ :
      NetworkPort N.toBoundaryNetwork) = ⟨r, i⟩
    exact Sigma.ext rfl (heq_of_eq ((N.pairing r).involutive i))

theorem localMatePort_region (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) :
    (localMatePort N p).1 = p.1 := rfl

theorem localMatePort_sameLabel (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) :
    boundaryDelta (N.toBoundaryNetwork.signature p.1) (localMatePort N p).2 =
      boundaryDelta (N.toBoundaryNetwork.signature p.1) p.2 :=
  (N.pairing p.1).sameLabel p.2

theorem localMatePort_ne (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) :
    localMatePort N p ≠ p := by
  intro h
  have hnot : p.2 ∉ residualPorts (N.pairing p.1) := by
    rw [N.perfect p.1]
    simp
  apply mate_ne_of_not_mem_residualPorts (N.pairing p.1) hnot
  exact eq_of_heq ((Sigma.mk.inj_iff.mp h).2)

theorem crossPort_ne_localMatePort (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) : crossPort N p ≠ localMatePort N p := by
  intro h
  apply crossPort_changes_region N p
  calc
    (crossPort N p).1 = (localMatePort N p).1 := congrArg Sigma.fst h
    _ = p.1 := rfl

def transitionNeighbors (N : ClosedBoundaryNetwork) (p : NetworkPort N.toBoundaryNetwork) :
    Finset (NetworkPort N.toBoundaryNetwork) := {crossPort N p, localMatePort N p}

theorem transitionNeighbors_card (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) : (transitionNeighbors N p).card = 2 := by
  simp [transitionNeighbors, crossPort_ne_localMatePort N p]

def TransitionAdj (N : ClosedBoundaryNetwork)
    (p q : NetworkPort N.toBoundaryNetwork) : Prop :=
  q = crossPort N p ∨ q = localMatePort N p

theorem transitionAdj_iff_mem_transitionNeighbors (N : ClosedBoundaryNetwork)
    (p q : NetworkPort N.toBoundaryNetwork) :
    TransitionAdj N p q ↔ q ∈ transitionNeighbors N p := by
  simp [TransitionAdj, transitionNeighbors]

theorem transitionAdj_symm (N : ClosedBoundaryNetwork)
    {p q : NetworkPort N.toBoundaryNetwork} : TransitionAdj N p q → TransitionAdj N q p := by
  rintro (rfl | rfl)
  · exact Or.inl (crossPort_involutive N p).symm
  · exact Or.inr (localMatePort_involutive N p).symm

theorem transitionAdj_irrefl (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) : ¬ TransitionAdj N p p := by
  intro h
  rcases h with h | h
  · exact crossPort_ne N p h.symm
  · exact localMatePort_ne N p h.symm

theorem transitionAdj_degree_two (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) : (transitionNeighbors N p).card = 2 :=
  transitionNeighbors_card N p

def transitionStep (N : ClosedBoundaryNetwork) :
    NetworkPort N.toBoundaryNetwork → NetworkPort N.toBoundaryNetwork :=
  fun p => localMatePort N (crossPort N p)

def transitionStepInv (N : ClosedBoundaryNetwork) :
    NetworkPort N.toBoundaryNetwork → NetworkPort N.toBoundaryNetwork :=
  fun p => crossPort N (localMatePort N p)

theorem transitionStepInv_left (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) : transitionStepInv N (transitionStep N p) = p := by
  simp only [transitionStepInv, transitionStep]
  rw [localMatePort_involutive, crossPort_involutive]

theorem transitionStepInv_right (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) : transitionStep N (transitionStepInv N p) = p := by
  simp only [transitionStep, transitionStepInv]
  rw [crossPort_involutive, localMatePort_involutive]

theorem transitionStep_injective (N : ClosedBoundaryNetwork) :
    Function.Injective (transitionStep N) := by
  intro p q h
  have h' := congrArg (transitionStepInv N) h
  rw [transitionStepInv_left N p, transitionStepInv_left N q] at h'
  exact h'

theorem transitionStep_surjective (N : ClosedBoundaryNetwork) :
    Function.Surjective (transitionStep N) := by
  intro p
  exact ⟨transitionStepInv N p, transitionStepInv_right N p⟩

def transitionEquiv (N : ClosedBoundaryNetwork) :
    NetworkPort N.toBoundaryNetwork ≃ NetworkPort N.toBoundaryNetwork where
  toFun := transitionStep N
  invFun := transitionStepInv N
  left_inv := transitionStepInv_left N
  right_inv := transitionStepInv_right N

theorem transitionStep_sameLabel (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    boundaryDelta (N.toBoundaryNetwork.signature (transitionStep N p).1) (transitionStep N p).2 =
      boundaryDelta (N.toBoundaryNetwork.signature p.1) p.2 := by
  calc
    boundaryDelta (N.toBoundaryNetwork.signature (transitionStep N p).1) (transitionStep N p).2 =
        boundaryDelta (N.toBoundaryNetwork.signature (crossPort N p).1) (crossPort N p).2 :=
      localMatePort_sameLabel N (crossPort N p)
    _ = boundaryDelta (N.toBoundaryNetwork.signature p.1) p.2 := crossPort_sameLabel N p

theorem transitionStep_iterate_sameLabel (N : ClosedBoundaryNetwork)
    (n : Nat) (p : NetworkPort N.toBoundaryNetwork) :
    boundaryDelta (N.toBoundaryNetwork.signature ((transitionStep N)^[n] p).1)
        ((transitionStep N)^[n] p).2 = boundaryDelta (N.toBoundaryNetwork.signature p.1) p.2 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    calc
      boundaryDelta (N.toBoundaryNetwork.signature ((transitionStep N)^[n]
          (transitionStep N p)).1) ((transitionStep N)^[n] (transitionStep N p)).2 =
          boundaryDelta (N.toBoundaryNetwork.signature (transitionStep N p).1) (transitionStep N p).2 :=
        ih (transitionStep N p)
      _ = boundaryDelta (N.toBoundaryNetwork.signature p.1) p.2 := transitionStep_sameLabel N p

theorem transitionStep_periodic (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    ∃ n : Nat, 0 < n ∧ (transitionStep N)^[n] p = p := by
  let e : Equiv.Perm (NetworkPort N.toBoundaryNetwork) := transitionEquiv N
  refine ⟨orderOf e, orderOf_pos e, ?_⟩
  have hpow : e ^ orderOf e = 1 := pow_orderOf_eq_one e
  have happly := congrArg (fun f : Equiv.Perm (NetworkPort N.toBoundaryNetwork) => f p) hpow
  rw [Equiv.Perm.coe_pow] at happly
  change ((transitionStep N)^[orderOf e]) p = p at happly
  exact happly

theorem transitionStep_periodic_sameLabel (N : ClosedBoundaryNetwork)
    (p : NetworkPort N.toBoundaryNetwork) :
    ∃ n : Nat, 0 < n ∧ (transitionStep N)^[n] p = p ∧
      boundaryDelta (N.toBoundaryNetwork.signature ((transitionStep N)^[n] p).1)
          ((transitionStep N)^[n] p).2 = boundaryDelta (N.toBoundaryNetwork.signature p.1) p.2 := by
  rcases transitionStep_periodic N p with ⟨n, hn, hcycle⟩
  exact ⟨n, hn, hcycle, transitionStep_iterate_sameLabel N n p⟩

end DkMath.Tromino
