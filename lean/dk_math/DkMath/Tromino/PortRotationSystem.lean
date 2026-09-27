/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortNetwork
import DkMath.Tromino.RotationSystem

#print "file: DkMath.Tromino.PortRotationSystem"

namespace DkMath.Tromino

structure PortLocalRotation (P : PortNetwork) where
  rotate : PortNetworkPort P ≃ PortNetworkPort P
  preservesRegion : ∀ p, (rotate p).1 = p.1

theorem PortLocalRotation.symm_preservesRegion
    {P : PortNetwork} (R : PortLocalRotation P) (p : PortNetworkPort P) :
    (R.rotate.symm p).1 = p.1 := by
  have hrot := congrArg Sigma.fst (R.rotate.apply_symm_apply p)
  have hpres := R.preservesRegion (R.rotate.symm p)
  exact hpres.symm.trans hrot

theorem PortLocalRotation.iterate_preservesRegion
    {P : PortNetwork} (R : PortLocalRotation P) (n : Nat)
    (p : PortNetworkPort P) :
    ((R.rotate : PortNetworkPort P → PortNetworkPort P)^[n] p).1 = p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (R.preservesRegion _).trans ih

theorem PortLocalRotation.symm_iterate_preservesRegion
    {P : PortNetwork} (R : PortLocalRotation P) (n : Nat)
    (p : PortNetworkPort P) :
    ((R.rotate.symm : PortNetworkPort P → PortNetworkPort P)^[n] p).1 = p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (R.symm_preservesRegion _).trans ih

def PortRegionRotationCyclic {P : PortNetwork} (R : PortLocalRotation P)
    (r : Fin P.regionCount) : Prop :=
  ∀ i j : Fin (P.arity r),
    ∃ n : Nat, (R.rotate^[n]) ⟨r, i⟩ = ⟨r, j⟩

structure PortRotationSystem (P : PortNetwork) extends PortLocalRotation P where
  cyclic : ∀ r, PortRegionRotationCyclic toPortLocalRotation r

theorem PortRotationSystem.rotation_reaches
    {P : PortNetwork} (R : PortRotationSystem P)
    (r : Fin P.regionCount) (i j : Fin (P.arity r)) :
    ∃ n : Nat, (R.rotate^[n]) ⟨r, i⟩ = ⟨r, j⟩ :=
  R.cyclic r i j

def portEdgeSource {P : PortNetwork} (_C : PortCrossing P)
    (p : PortNetworkPort P) : Fin P.regionCount := p.1

def portEdgeTarget {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : Fin P.regionCount := (C.cross p).1

def portFaceStep {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortNetworkPort P → PortNetworkPort P :=
  fun p => R.rotate (C.cross p)

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

theorem portFaceEquiv_apply {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    portFaceEquiv R C p = portFaceStep R C p := rfl

theorem portFaceEquiv_symm_apply {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceEquiv R C).symm p = C.cross (R.rotate.symm p) := rfl

theorem portFaceStep_source {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    portEdgeSource C (portFaceStep R C p) = portEdgeTarget C p := by
  exact R.preservesRegion (C.cross p)

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

def PortFaceReturn {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) (n : Nat) : Prop :=
  (portFaceStep R C)^[n] p = p

def firstPortFaceReturn {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : Nat :=
  Nat.find (portFaceStep_periodic R C p)

theorem firstPortFaceReturn_spec {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    0 < firstPortFaceReturn R C p ∧
      PortFaceReturn R C p (firstPortFaceReturn R C p) := by
  exact Nat.find_spec (portFaceStep_periodic R C p)

theorem firstPortFaceReturn_min {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) {m : Nat}
    (hm : 0 < m ∧ PortFaceReturn R C p m) :
    firstPortFaceReturn R C p ≤ m := by
  exact Nat.find_min' (portFaceStep_periodic R C p) hm

def PortFacePrimitiveReturn {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) (n : Nat) : Prop :=
  0 < n ∧ PortFaceReturn R C p n ∧
    ∀ m, 0 < m → m < n → ¬ PortFaceReturn R C p m

theorem firstPortFaceReturn_primitive {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    PortFacePrimitiveReturn R C p (firstPortFaceReturn R C p) := by
  refine ⟨(firstPortFaceReturn_spec R C p).1,
    (firstPortFaceReturn_spec R C p).2, ?_⟩
  intro m hmpos hmlt hreturn
  exact (not_lt_of_ge (firstPortFaceReturn_min R C p ⟨hmpos, hreturn⟩)) hmlt

def FlowLocalRotation.toPortLocalRotation {N : FlowNetwork}
    (R : FlowLocalRotation N) : PortLocalRotation N.toPortNetwork where
  rotate := R.rotate
  preservesRegion := R.preservesRegion

@[simp] theorem FlowLocalRotation.toPortLocalRotation_rotate
    {N : FlowNetwork} (R : FlowLocalRotation N)
    (p : PortNetworkPort N.toPortNetwork) :
    R.toPortLocalRotation.rotate p = R.rotate p := rfl

def FlowRotationSystem.toPortRotationSystem {N : FlowNetwork}
    (R : FlowRotationSystem N) : PortRotationSystem N.toPortNetwork where
  toPortLocalRotation := R.toPortLocalRotation
  cyclic := by
    intro r i j
    exact R.cyclic r i j

theorem FlowRotationSystem.toPortRotationSystem_rotate
    {N : FlowNetwork} (R : FlowRotationSystem N)
    (p : PortNetworkPort N.toPortNetwork) :
    R.toPortRotationSystem.rotate p = R.rotate p := rfl

theorem portFaceStep_of_flow_erasure {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p : PortNetworkPort N.toPortNetwork) :
    portFaceStep R.toPortLocalRotation C.toPortCrossing p =
      faceStep R C p := rfl

def PortLocalRotation.toFlowLocalRotation {P : PortNetwork}
    {C : PortCrossing P} (R : PortLocalRotation P)
    (A : V4FlowAssignment C) : FlowLocalRotation A.toFlowNetwork where
  rotate := R.rotate
  preservesRegion := R.preservesRegion

theorem PortLocalRotation.toFlowLocalRotation_rotate {P : PortNetwork}
    {C : PortCrossing P} (R : PortLocalRotation P)
    (A : V4FlowAssignment C) (p : PortNetworkPort P) :
    (R.toFlowLocalRotation A).rotate p = R.rotate p := rfl

def PortRotationSystem.toFlowRotationSystem {P : PortNetwork}
    {C : PortCrossing P} (R : PortRotationSystem P)
    (A : V4FlowAssignment C) : FlowRotationSystem A.toFlowNetwork where
  toFlowLocalRotation := R.toFlowLocalRotation A
  cyclic := by
    intro r i j
    exact R.cyclic r i j

theorem portFaceStep_of_flow_lift {P : PortNetwork} {C : PortCrossing P}
    (R : PortLocalRotation P) (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    faceStep (R.toFlowLocalRotation A) A.toFlowCrossing p =
      portFaceStep R C p := rfl

theorem portFaceStep_assignment_independent {P : PortNetwork}
    {C : PortCrossing P} (R : PortLocalRotation P)
    (A B : V4FlowAssignment C) (p : PortNetworkPort P) :
    faceStep (R.toFlowLocalRotation A) A.toFlowCrossing p =
      faceStep (R.toFlowLocalRotation B) B.toFlowCrossing p := by
  rw [portFaceStep_of_flow_lift, portFaceStep_of_flow_lift]

theorem portFaceStep_round_trip {N : FlowNetwork}
    (R : FlowLocalRotation N) (C : FlowCrossing N)
    (p : PortNetworkPort N.toPortNetwork) :
    faceStep (R.toPortLocalRotation.toFlowLocalRotation
      C.toV4FlowAssignment) C.toV4FlowAssignment.toFlowCrossing p =
      faceStep R C p := by
  rw [portFaceStep_of_flow_lift, portFaceStep_of_flow_erasure]

end DkMath.Tromino
