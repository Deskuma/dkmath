/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.GraphColoringBridge

#print "file: DkMath.Tromino.RotationSystem"

namespace DkMath.Tromino

structure FlowLocalRotation (N : FlowNetwork) where
  rotate : FlowNetworkPort N ≃ FlowNetworkPort N
  preservesRegion : ∀ p, (rotate p).1 = p.1

theorem FlowLocalRotation.symm_preservesRegion
    {N : FlowNetwork} (R : FlowLocalRotation N) (p : FlowNetworkPort N) :
    (R.rotate.symm p).1 = p.1 := by
  have hrot := congrArg Sigma.fst (R.rotate.apply_symm_apply p)
  have hpres := R.preservesRegion (R.rotate.symm p)
  exact hpres.symm.trans hrot

theorem FlowLocalRotation.iterate_preservesRegion
    {N : FlowNetwork} (R : FlowLocalRotation N) (n : Nat)
    (p : FlowNetworkPort N) :
    ((R.rotate : FlowNetworkPort N → FlowNetworkPort N)^[n] p).1 = p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (R.preservesRegion _).trans ih

theorem FlowLocalRotation.symm_iterate_preservesRegion
    {N : FlowNetwork} (R : FlowLocalRotation N) (n : Nat)
    (p : FlowNetworkPort N) :
    ((R.rotate.symm : FlowNetworkPort N → FlowNetworkPort N)^[n] p).1 = p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (R.symm_preservesRegion _).trans ih

def RegionRotationCyclic {N : FlowNetwork} (R : FlowLocalRotation N)
    (r : Fin N.regionCount) : Prop :=
  ∀ i j : Fin (N.signature r).arity,
    ∃ n : Nat, (R.rotate^[n]) ⟨r, i⟩ = ⟨r, j⟩

structure FlowRotationSystem (N : FlowNetwork) extends FlowLocalRotation N where
  cyclic : ∀ r, RegionRotationCyclic toFlowLocalRotation r

theorem FlowRotationSystem.rotation_reaches
    {N : FlowNetwork} (R : FlowRotationSystem N)
    (r : Fin N.regionCount) (i j : Fin (N.signature r).arity) :
    ∃ n : Nat, (R.rotate^[n]) ⟨r, i⟩ = ⟨r, j⟩ :=
  R.cyclic r i j

def flowCrossEquiv {N : FlowNetwork} (C : FlowCrossing N) :
    FlowNetworkPort N ≃ FlowNetworkPort N where
  toFun := C.cross
  invFun := C.cross
  left_inv := C.involutive
  right_inv := C.involutive

@[simp] theorem flowCrossEquiv_apply {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : flowCrossEquiv C p = C.cross p := rfl

theorem flowCrossEquiv_symm_apply {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : (flowCrossEquiv C).symm p = C.cross p := rfl

theorem flowCrossEquiv_involutive {N : FlowNetwork} (C : FlowCrossing N) :
    Function.Involutive (flowCrossEquiv C) := C.involutive

def faceStep {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) : FlowNetworkPort N → FlowNetworkPort N :=
  fun p => R.rotate (C.cross p)

def faceEquiv {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) : FlowNetworkPort N ≃ FlowNetworkPort N where
  toFun := faceStep R C
  invFun := fun p => C.cross (R.rotate.symm p)
  left_inv := by
    intro p
    simp only [faceStep]
    rw [R.rotate.symm_apply_apply, C.involutive]
  right_inv := by
    intro p
    simp only [faceStep]
    rw [C.involutive, R.rotate.apply_symm_apply]

theorem faceEquiv_apply {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    faceEquiv R C p = faceStep R C p := rfl

theorem faceEquiv_symm_apply {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    (faceEquiv R C).symm p = C.cross (R.rotate.symm p) := rfl

theorem faceStep_source {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    flowEdgeSource C (faceStep R C p) = flowEdgeTarget C p := by
  simp only [faceStep, flowEdgeSource, flowEdgeTarget]
  exact R.preservesRegion (C.cross p)

theorem faceStep_rotate_source {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    (flowPortToDart C (R.rotate p)).fst = (flowPortToDart C p).fst := by
  simp only [flowPortToDart_fst, flowEdgeSource]
  exact R.preservesRegion p

theorem faceStep_periodic {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    ∃ n : Nat, 0 < n ∧ (faceStep R C)^[n] p = p := by
  let e : Equiv.Perm (FlowNetworkPort N) := faceEquiv R C
  refine ⟨orderOf e, orderOf_pos e, ?_⟩
  have hpow : e ^ orderOf e = 1 := pow_orderOf_eq_one e
  have happly := congrArg
    (fun f : Equiv.Perm (FlowNetworkPort N) => f p) hpow
  rw [Equiv.Perm.coe_pow] at happly
  change ((faceStep R C)^[orderOf e]) p = p at happly
  exact happly

def FaceReturn {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) (n : Nat) : Prop :=
  (faceStep R C)^[n] p = p

def firstFaceReturn {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) : Nat :=
  Nat.find (faceStep_periodic R C p)

theorem firstFaceReturn_spec {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    0 < firstFaceReturn R C p ∧
      FaceReturn R C p (firstFaceReturn R C p) := by
  exact Nat.find_spec (faceStep_periodic R C p)

theorem firstFaceReturn_min {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) {m : Nat}
    (hm : 0 < m ∧ FaceReturn R C p m) :
    firstFaceReturn R C p ≤ m := by
  exact Nat.find_min' (faceStep_periodic R C p) hm

def FacePrimitiveReturn {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) (n : Nat) : Prop :=
  0 < n ∧ FaceReturn R C p n ∧
    ∀ m, 0 < m → m < n → ¬ FaceReturn R C p m

theorem firstFaceReturn_primitive {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    FacePrimitiveReturn R C p (firstFaceReturn R C p) := by
  refine ⟨(firstFaceReturn_spec R C p).1, (firstFaceReturn_spec R C p).2, ?_⟩
  intro m hmpos hmlt hreturn
  exact (not_lt_of_ge (firstFaceReturn_min R C p ⟨hmpos, hreturn⟩)) hmlt

theorem faceStep_eq_flowTransitionStep_of_rotate_eq_mate
    {N : ClosedFlowNetwork} (R : FlowLocalRotation N.toFlowNetwork)
    (hrotate : ∀ p, R.rotate p = flowLocalMatePort N p)
    (p : FlowNetworkPort N.toFlowNetwork) :
    faceStep R N.crossing p = flowTransitionStep N p := by
  simp only [faceStep, flowTransitionStep, flowCrossPort]
  rw [hrotate]

end DkMath.Tromino
