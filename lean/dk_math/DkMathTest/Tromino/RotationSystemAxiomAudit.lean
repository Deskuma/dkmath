/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RotationSystem
import DkMathTest.Tromino.FlowTransitionXorAxiomAudit
import DkMathTest.Tromino.GraphColoringBridgeAxiomAudit

#print "file: DkMathTest.Tromino.RotationSystemAxiomAudit"

namespace DkMathTest.Tromino.RotationSystemAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.FlowTransitionXorAxiomAudit
open DkMathTest.Tromino.GraphColoringBridgeAxiomAudit

def aaaFlow : FlowSignature where
  arity := 3
  label := ![deltaA, deltaA, deltaA]
  nonzero := by
    intro i
    fin_cases i <;> exact deltaA_ne_zero

def twoThreeNetwork : FlowNetwork where
  regionCount := 2
  signature := fun _ => aaaFlow

def twoThreeCrossing : FlowCrossing twoThreeNetwork where
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

def rotate3 (i : Fin 3) : Fin 3 :=
  if i.val = 0 then ⟨1, by decide⟩
  else if i.val = 1 then ⟨2, by decide⟩
  else ⟨0, by omega⟩

def rotate3Inv (i : Fin 3) : Fin 3 :=
  if i.val = 0 then ⟨2, by decide⟩
  else if i.val = 1 then ⟨0, by decide⟩
  else ⟨1, by omega⟩

theorem rotate3Inv_rotate3 (i : Fin 3) : rotate3Inv (rotate3 i) = i := by
  fin_cases i <;> rfl

theorem rotate3_rotate3Inv (i : Fin 3) : rotate3 (rotate3Inv i) = i := by
  fin_cases i <;> rfl

def twoThreeRotateEquiv :
    FlowNetworkPort twoThreeNetwork ≃ FlowNetworkPort twoThreeNetwork where
  toFun := fun p => ⟨p.1, rotate3 p.2⟩
  invFun := fun p => ⟨p.1, rotate3Inv p.2⟩
  left_inv := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (rotate3Inv_rotate3 i)
  right_inv := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (rotate3_rotate3Inv i)

def twoThreeRotation : FlowLocalRotation twoThreeNetwork where
  rotate := twoThreeRotateEquiv
  preservesRegion := by intro p; rfl

theorem rotate3_iterate (i j : Fin 3) :
    ∃ n : Nat, (rotate3^[n]) i = j := by
  fin_cases i <;> fin_cases j
  · exact ⟨0, rfl⟩
  · exact ⟨1, by simp [rotate3]⟩
  · exact ⟨2, by simp [rotate3]⟩
  · exact ⟨2, by simp [rotate3]⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, by simp [rotate3]⟩
  · exact ⟨1, by simp [rotate3]⟩
  · exact ⟨2, by simp [rotate3]⟩
  · exact ⟨0, rfl⟩

theorem twoThreeRotate_iterate (r : Fin 2) (i : Fin 3) (n : Nat) :
    (twoThreeRotation.rotate^[n]) ⟨r, i⟩ =
      ⟨r, (rotate3^[n]) i⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [ih]
    rw [Function.iterate_succ_apply']
    rfl

def twoThreeRotationSystem : FlowRotationSystem twoThreeNetwork where
  toFlowLocalRotation := twoThreeRotation
  cyclic := by
    intro r i j
    obtain ⟨n, hn⟩ := rotate3_iterate i j
    exact ⟨n, by
      calc
        (twoThreeRotation.rotate^[n]) ⟨r, i⟩ =
            ⟨r, (rotate3^[n]) i⟩ := twoThreeRotate_iterate r i n
        _ = ⟨r, j⟩ := by rw [hn]⟩

def p23 : FlowNetworkPort twoThreeNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

theorem faceStep_23_0 :
    faceStep twoThreeRotation twoThreeCrossing p23 =
      ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ := by
  rfl

example :
    (faceStep twoThreeRotation twoThreeCrossing)^[6] p23 = p23 := by
  decide

example : faceStep twoThreeRotation twoThreeCrossing p23 ≠ p23 := by
  rw [faceStep_23_0]
  decide

example :
    ∃ n : Nat, 0 < n ∧
      (faceStep twoThreeRotation twoThreeCrossing)^[n] p23 = p23 :=
  faceStep_periodic twoThreeRotation twoThreeCrossing p23

example :
    flowEdgeSource twoThreeCrossing
        (faceStep twoThreeRotation twoThreeCrossing p23) =
      flowEdgeTarget twoThreeCrossing p23 :=
  faceStep_source twoThreeRotation twoThreeCrossing p23

example :
    (flowPortToDart twoThreeCrossing
        (twoThreeRotation.rotate p23)).fst =
      (flowPortToDart twoThreeCrossing p23).fst :=
  faceStep_rotate_source twoThreeRotation twoThreeCrossing p23

def mateRotation : FlowLocalRotation twoRegionFlowClosed.toFlowNetwork where
  rotate :=
    { toFun := flowLocalMatePort twoRegionFlowClosed
      invFun := flowLocalMatePort twoRegionFlowClosed
      left_inv := flowLocalMatePort_involutive twoRegionFlowClosed
      right_inv := flowLocalMatePort_involutive twoRegionFlowClosed }
  preservesRegion := by intro p; rfl

example (p : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork) :
    faceStep mateRotation twoRegionFlowClosed.crossing p =
      flowTransitionStep twoRegionFlowClosed p := by
  exact faceStep_eq_flowTransitionStep_of_rotate_eq_mate mateRotation
    (fun _ => rfl) p

#print axioms DkMath.Tromino.FlowLocalRotation.iterate_preservesRegion
#print axioms DkMath.Tromino.flowCrossEquiv
#print axioms DkMath.Tromino.faceEquiv
#print axioms DkMath.Tromino.faceStep_periodic
#print axioms DkMath.Tromino.faceStep_eq_flowTransitionStep_of_rotate_eq_mate

end DkMathTest.Tromino.RotationSystemAxiomAudit
