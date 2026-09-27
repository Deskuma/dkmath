/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortNetwork
import DkMath.Tromino.RotationSystem

#print "file: DkMath.Tromino.PortRotationSystem"

/-!
# Local rotations of ports

A local rotation is a permutation of the ports in each region.  Its
iterates describe cyclic vertex boundaries, while composing it with the
crossing involution gives the face-step permutation.  The conversion
theorems at the end identify this port language with the corresponding
flow-network language without changing the finite combinatorics.
-/

namespace DkMath.Tromino

/-- A region-preserving permutation of the finite port carrier. -/
structure PortLocalRotation (P : PortNetwork) where
  rotate : PortNetworkPort P ≃ PortNetworkPort P
  preservesRegion : ∀ p, (rotate p).1 = p.1

/-- The inverse rotation also stays inside each region. -/
theorem PortLocalRotation.symm_preservesRegion
    {P : PortNetwork} (R : PortLocalRotation P) (p : PortNetworkPort P) :
    (R.rotate.symm p).1 = p.1 := by
  have hrot := congrArg Sigma.fst (R.rotate.apply_symm_apply p)
  have hpres := R.preservesRegion (R.rotate.symm p)
  exact hpres.symm.trans hrot

/-- Every forward rotation iterate preserves its region index. -/
theorem PortLocalRotation.iterate_preservesRegion
    {P : PortNetwork} (R : PortLocalRotation P) (n : Nat)
    (p : PortNetworkPort P) :
    ((R.rotate : PortNetworkPort P → PortNetworkPort P)^[n] p).1 = p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (R.preservesRegion _).trans ih

/-- Every inverse rotation iterate preserves its region index. -/
theorem PortLocalRotation.symm_iterate_preservesRegion
    {P : PortNetwork} (R : PortLocalRotation P) (n : Nat)
    (p : PortNetworkPort P) :
    ((R.rotate.symm : PortNetworkPort P → PortNetworkPort P)^[n] p).1 = p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (R.symm_preservesRegion _).trans ih

/-- Every pair of slots in a region lies on one rotation orbit. -/
def PortRegionRotationCyclic {P : PortNetwork} (R : PortLocalRotation P)
    (r : Fin P.regionCount) : Prop :=
  ∀ i j : Fin (P.arity r),
    ∃ n : Nat, (R.rotate^[n]) ⟨r, i⟩ = ⟨r, j⟩

/-- A rotation system adds cyclicity to a local rotation. -/
structure PortRotationSystem (P : PortNetwork) extends PortLocalRotation P where
  cyclic : ∀ r, PortRegionRotationCyclic toPortLocalRotation r

/-- Cyclicity supplies a rotation iterate between any two local slots. -/
theorem PortRotationSystem.rotation_reaches
    {P : PortNetwork} (R : PortRotationSystem P)
    (r : Fin P.regionCount) (i j : Fin (P.arity r)) :
    ∃ n : Nat, (R.rotate^[n]) ⟨r, i⟩ = ⟨r, j⟩ :=
  R.cyclic r i j

/-- The source region of a crossing edge is the port's region. -/
def portEdgeSource {P : PortNetwork} (_C : PortCrossing P)
    (p : PortNetworkPort P) : Fin P.regionCount := p.1

/-- The target region of a crossing edge is the crossed port's region. -/
def portEdgeTarget {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : Fin P.regionCount := (C.cross p).1

/-- One face step crosses an edge and then rotates at the new region. -/
def portFaceStep {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortNetworkPort P → PortNetworkPort P :=
  fun p => R.rotate (C.cross p)

/-- The face step is a permutation of the finite port carrier. -/
def portFaceEquiv {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortNetworkPort P ≃ PortNetworkPort P where
  toFun := portFaceStep R C
  invFun := fun p => C.cross (R.rotate.symm p)
  left_inv := by
    intro p
    simp only [portFaceStep]
    rw [R.rotate.symm_apply_apply, C.involutive]
  right_inv := by
    intro p
    simp only [portFaceStep]
    rw [C.involutive, R.rotate.apply_symm_apply]

/-- The face permutation acts by the face-step function. -/
theorem portFaceEquiv_apply {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    portFaceEquiv R C p = portFaceStep R C p := rfl

/-- The inverse face permutation crosses after inverse rotation. -/
theorem portFaceEquiv_symm_apply {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceEquiv R C).symm p = C.cross (R.rotate.symm p) := rfl

/-- A face step starts in the region reached by crossing the current port. -/
theorem portFaceStep_source {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    portEdgeSource C (portFaceStep R C p) = portEdgeTarget C p := by
  exact R.preservesRegion (C.cross p)

/-- Finiteness forces every face step orbit to return. -/
theorem portFaceStep_periodic {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    ∃ n : Nat, 0 < n ∧ (portFaceStep R C)^[n] p = p := by
  let e : Equiv.Perm (PortNetworkPort P) := portFaceEquiv R C
  refine ⟨orderOf e, orderOf_pos e, ?_⟩
  have hpow : e ^ orderOf e = 1 := pow_orderOf_eq_one e
  have happly := congrArg
    (fun f : Equiv.Perm (PortNetworkPort P) => f p) hpow
  rw [Equiv.Perm.coe_pow] at happly
  change ((portFaceStep R C)^[orderOf e]) p = p at happly
  exact happly

/-- Predicate for returning to a dart after a prescribed number of face steps. -/
def PortFaceReturn {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) (n : Nat) : Prop :=
  (portFaceStep R C)^[n] p = p

/-- The least positive face-return time. -/
def firstPortFaceReturn {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : Nat :=
  Nat.find (portFaceStep_periodic R C p)

/-- The first return is positive and is a genuine return. -/
theorem firstPortFaceReturn_spec {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    0 < firstPortFaceReturn R C p ∧
      PortFaceReturn R C p (firstPortFaceReturn R C p) := by
  exact Nat.find_spec (portFaceStep_periodic R C p)

/-- No positive return occurs before the first return time. -/
theorem firstPortFaceReturn_min {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) {m : Nat}
    (hm : 0 < m ∧ PortFaceReturn R C p m) :
    firstPortFaceReturn R C p ≤ m := by
  exact Nat.find_min' (portFaceStep_periodic R C p) hm

/-- A return time is primitive when it has no smaller positive return. -/
def PortFacePrimitiveReturn {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) (n : Nat) : Prop :=
  0 < n ∧ PortFaceReturn R C p n ∧
    ∀ m, 0 < m → m < n → ¬ PortFaceReturn R C p m

/-- The least return time is primitive by construction. -/
theorem firstPortFaceReturn_primitive {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    PortFacePrimitiveReturn R C p (firstPortFaceReturn R C p) := by
  refine ⟨(firstPortFaceReturn_spec R C p).1,
    (firstPortFaceReturn_spec R C p).2, ?_⟩
  intro m hmpos hmlt hreturn
  exact (not_lt_of_ge (firstPortFaceReturn_min R C p ⟨hmpos, hreturn⟩)) hmlt

/-- Forget a flow rotation's label packaging. -/
def FlowLocalRotation.toPortLocalRotation {N : FlowNetwork}
    (R : FlowLocalRotation N) : PortLocalRotation N.toPortNetwork where
  rotate := R.rotate
  preservesRegion := R.preservesRegion

/-- The forgotten rotation acts as the original flow rotation. -/
@[simp] theorem FlowLocalRotation.toPortLocalRotation_rotate
    {N : FlowNetwork} (R : FlowLocalRotation N)
    (p : PortNetworkPort N.toPortNetwork) :
    R.toPortLocalRotation.rotate p = R.rotate p := rfl

/-- Forget flow labels while retaining cyclic local rotations. -/
def FlowRotationSystem.toPortRotationSystem {N : FlowNetwork}
    (R : FlowRotationSystem N) : PortRotationSystem N.toPortNetwork where
  toPortLocalRotation := R.toPortLocalRotation
  cyclic := by
    intro r i j
    exact R.cyclic r i j

/-- The forgotten rotation system has the original action. -/
theorem FlowRotationSystem.toPortRotationSystem_rotate
    {N : FlowNetwork} (R : FlowRotationSystem N)
    (p : PortNetworkPort N.toPortNetwork) :
    R.toPortRotationSystem.rotate p = R.rotate p := rfl

/-- Port face steps agree with flow face steps after erasure. -/
theorem portFaceStep_of_flow_erasure {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p : PortNetworkPort N.toPortNetwork) :
    portFaceStep R.toPortLocalRotation C.toPortCrossing p =
      faceStep R C p := rfl

/-- Restore a port rotation as a flow rotation using any assignment. -/
def PortLocalRotation.toFlowLocalRotation {P : PortNetwork}
    {C : PortCrossing P} (R : PortLocalRotation P)
    (A : V4FlowAssignment C) : FlowLocalRotation A.toFlowNetwork where
  rotate := R.rotate
  preservesRegion := R.preservesRegion

/-- The restored flow rotation has the original port action. -/
theorem PortLocalRotation.toFlowLocalRotation_rotate {P : PortNetwork}
    {C : PortCrossing P} (R : PortLocalRotation P)
    (A : V4FlowAssignment C) (p : PortNetworkPort P) :
    (R.toFlowLocalRotation A).rotate p = R.rotate p := rfl

/-- Restore a port rotation system in the flow presentation. -/
def PortRotationSystem.toFlowRotationSystem {P : PortNetwork}
    {C : PortCrossing P} (R : PortRotationSystem P)
    (A : V4FlowAssignment C) : FlowRotationSystem A.toFlowNetwork where
  toFlowLocalRotation := R.toFlowLocalRotation A
  cyclic := by
    intro r i j
    exact R.cyclic r i j

/-- Flow lifting preserves the port face-step permutation. -/
theorem portFaceStep_of_flow_lift {P : PortNetwork} {C : PortCrossing P}
    (R : PortLocalRotation P) (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    faceStep (R.toFlowLocalRotation A) A.toFlowCrossing p =
      portFaceStep R C p := rfl

/-- The induced face step does not depend on the chosen labels. -/
theorem portFaceStep_assignment_independent {P : PortNetwork}
    {C : PortCrossing P} (R : PortLocalRotation P)
    (A B : V4FlowAssignment C) (p : PortNetworkPort P) :
    faceStep (R.toFlowLocalRotation A) A.toFlowCrossing p =
      faceStep (R.toFlowLocalRotation B) B.toFlowCrossing p := by
  rw [portFaceStep_of_flow_lift, portFaceStep_of_flow_lift]

/-- Erasing and restoring a flow face step is a round trip. -/
theorem portFaceStep_round_trip {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p : PortNetworkPort N.toPortNetwork) :
    faceStep (R.toPortLocalRotation.toFlowLocalRotation
      C.toV4FlowAssignment) C.toV4FlowAssignment.toFlowCrossing p =
      faceStep R C p := by
  rw [portFaceStep_of_flow_lift, portFaceStep_of_flow_erasure]

end DkMath.Tromino
