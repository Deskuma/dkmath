/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.GraphColoringBridge

#print "file: DkMath.Tromino.RotationSystem"

/-!
# Flow rotation systems

A local rotation is a permutation of the ports inside each region.  A flow
rotation system adds cyclicity, so every local port can reach every other
port in that region.  Composing the rotation with the crossing involution
produces the face-step permutation and its finite return times.
-/

namespace DkMath.Tromino

/-- A region-preserving permutation of flow-network ports. -/
structure FlowLocalRotation (N : FlowNetwork) where
  rotate : FlowNetworkPort N ≃ FlowNetworkPort N
  preservesRegion : ∀ p, (rotate p).1 = p.1

/-- The inverse local rotation also preserves regions. -/
theorem FlowLocalRotation.symm_preservesRegion
    {N : FlowNetwork} (R : FlowLocalRotation N) (p : FlowNetworkPort N) :
    (R.rotate.symm p).1 = p.1 := by
  have hrot := congrArg Sigma.fst (R.rotate.apply_symm_apply p)
  have hpres := R.preservesRegion (R.rotate.symm p)
  exact hpres.symm.trans hrot

/-- Forward rotation iterates stay in the original region. -/
theorem FlowLocalRotation.iterate_preservesRegion
    {N : FlowNetwork} (R : FlowLocalRotation N) (n : Nat)
    (p : FlowNetworkPort N) :
    ((R.rotate : FlowNetworkPort N → FlowNetworkPort N)^[n] p).1 = p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (R.preservesRegion _).trans ih

/-- Inverse rotation iterates stay in the original region. -/
theorem FlowLocalRotation.symm_iterate_preservesRegion
    {N : FlowNetwork} (R : FlowLocalRotation N) (n : Nat)
    (p : FlowNetworkPort N) :
    ((R.rotate.symm : FlowNetworkPort N → FlowNetworkPort N)^[n] p).1 = p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (R.symm_preservesRegion _).trans ih

/-- Every pair of local slots is connected by a rotation iterate. -/
def RegionRotationCyclic {N : FlowNetwork} (R : FlowLocalRotation N)
    (r : Fin N.regionCount) : Prop :=
  ∀ i j : Fin (N.signature r).arity,
    ∃ n : Nat, (R.rotate^[n]) ⟨r, i⟩ = ⟨r, j⟩

/-- A local rotation system with cyclic rotation at every region. -/
structure FlowRotationSystem (N : FlowNetwork) extends FlowLocalRotation N where
  cyclic : ∀ r, RegionRotationCyclic toFlowLocalRotation r

/-- Cyclicity gives an iterate from any local slot to any other. -/
theorem FlowRotationSystem.rotation_reaches
    {N : FlowNetwork} (R : FlowRotationSystem N)
    (r : Fin N.regionCount) (i j : Fin (N.signature r).arity) :
    ∃ n : Nat, (R.rotate^[n]) ⟨r, i⟩ = ⟨r, j⟩ :=
  R.cyclic r i j

/-- Package a flow crossing involution as a permutation. -/
def flowCrossEquiv {N : FlowNetwork} (C : FlowCrossing N) :
    FlowNetworkPort N ≃ FlowNetworkPort N where
  toFun := C.cross
  invFun := C.cross
  left_inv := C.involutive
  right_inv := C.involutive

/-- The crossing equivalence acts by the original crossing map. -/
@[simp] theorem flowCrossEquiv_apply {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : flowCrossEquiv C p = C.cross p := rfl

/-- The inverse crossing equivalence has the same involution action. -/
theorem flowCrossEquiv_symm_apply {N : FlowNetwork} (C : FlowCrossing N)
    (p : FlowNetworkPort N) : (flowCrossEquiv C).symm p = C.cross p := rfl

/-- The crossing equivalence is self-inverse. -/
theorem flowCrossEquiv_involutive {N : FlowNetwork} (C : FlowCrossing N) :
    Function.Involutive (flowCrossEquiv C) := C.involutive

/-- One face step crosses a port and then rotates in the new region. -/
def faceStep {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) : FlowNetworkPort N → FlowNetworkPort N :=
  fun p => R.rotate (C.cross p)

/-- The face-step function is a permutation of the port carrier. -/
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

/-- The face equivalence acts by the face-step function. -/
theorem faceEquiv_apply {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    faceEquiv R C p = faceStep R C p := rfl

/-- The inverse face permutation crosses after inverse rotation. -/
theorem faceEquiv_symm_apply {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    (faceEquiv R C).symm p = C.cross (R.rotate.symm p) := rfl

/-- A face step starts in the region reached by crossing. -/
theorem faceStep_source {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    flowEdgeSource C (faceStep R C p) = flowEdgeTarget C p := by
  simp only [faceStep, flowEdgeSource, flowEdgeTarget]
  exact R.preservesRegion (C.cross p)

/-- The face step is the rotated endpoint of the crossed edge. -/
theorem faceStep_rotate_source {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    (flowPortToDart C (R.rotate p)).fst = (flowPortToDart C p).fst := by
  simp only [flowPortToDart_fst, flowEdgeSource]
  exact R.preservesRegion p

/-- Finiteness of the face permutation gives a positive return time. -/
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

/-- Predicate for returning to a port after a prescribed face length. -/
def FaceReturn {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) (n : Nat) : Prop :=
  (faceStep R C)^[n] p = p

/-- The least positive face-return length. -/
def firstFaceReturn {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) : Nat :=
  Nat.find (faceStep_periodic R C p)

/-- The first face return is positive and valid. -/
theorem firstFaceReturn_spec {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    0 < firstFaceReturn R C p ∧
      FaceReturn R C p (firstFaceReturn R C p) := by
  exact Nat.find_spec (faceStep_periodic R C p)

/-- No positive face return occurs earlier than the first return. -/
theorem firstFaceReturn_min {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) {m : Nat}
    (hm : 0 < m ∧ FaceReturn R C p m) :
    firstFaceReturn R C p ≤ m := by
  exact Nat.find_min' (faceStep_periodic R C p) hm

/-- A face return with no smaller positive return. -/
def FacePrimitiveReturn {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) (n : Nat) : Prop :=
  0 < n ∧ FaceReturn R C p n ∧
    ∀ m, 0 < m → m < n → ¬ FaceReturn R C p m

/-- The first face return is primitive. -/
theorem firstFaceReturn_primitive {N : FlowNetwork} (R : FlowLocalRotation N)
    (C : FlowCrossing N) (p : FlowNetworkPort N) :
    FacePrimitiveReturn R C p (firstFaceReturn R C p) := by
  refine ⟨(firstFaceReturn_spec R C p).1, (firstFaceReturn_spec R C p).2, ?_⟩
  intro m hmpos hmlt hreturn
  exact (not_lt_of_ge (firstFaceReturn_min R C p ⟨hmpos, hreturn⟩)) hmlt

/-- When rotation is local pairing, face steps equal transition steps. -/
theorem faceStep_eq_flowTransitionStep_of_rotate_eq_mate
    {N : ClosedFlowNetwork} (R : FlowLocalRotation N.toFlowNetwork)
    (hrotate : ∀ p, R.rotate p = flowLocalMatePort N p)
    (p : FlowNetworkPort N.toFlowNetwork) :
    faceStep R N.crossing p = flowTransitionStep N p := by
  simp only [faceStep, flowTransitionStep, flowCrossPort]
  rw [hrotate]

end DkMath.Tromino
