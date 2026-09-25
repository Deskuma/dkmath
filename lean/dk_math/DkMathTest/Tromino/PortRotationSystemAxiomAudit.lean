/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortRotationSystem
import DkMathTest.Tromino.RotationSystemAxiomAudit

#print "file: DkMathTest.Tromino.PortRotationSystemAxiomAudit"

namespace DkMathTest.Tromino.PortRotationSystemAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.RotationSystemAxiomAudit

def portTwoNetwork : PortNetwork where
  regionCount := 2
  arity := fun _ => 2

def portSwap2 (r : Fin 2) : Fin 2 := ⟨1 - r.val, by omega⟩

theorem portSwap2_involutive (r : Fin 2) : portSwap2 (portSwap2 r) = r := by
  apply Fin.ext
  dsimp [portSwap2]
  omega

theorem portSwap2_ne (r : Fin 2) : portSwap2 r ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [portSwap2] at hv
  omega

def portTwoCrossing : PortCrossing portTwoNetwork where
  cross := fun p => ⟨portSwap2 p.1, p.2⟩
  involutive := by
    intro p
    apply Sigma.ext
    · exact portSwap2_involutive p.1
    · exact heq_of_eq rfl
  changesRegion := by
    intro p
    exact portSwap2_ne p.1

def portRotate2 (i : Fin 2) : Fin 2 := ⟨1 - i.val, by omega⟩

theorem portRotate2_involutive (i : Fin 2) : portRotate2 (portRotate2 i) = i := by
  apply Fin.ext
  dsimp [portRotate2]
  omega

def portTwoRotateEquiv :
    PortNetworkPort portTwoNetwork ≃ PortNetworkPort portTwoNetwork where
  toFun := fun p => ⟨p.1, portRotate2 p.2⟩
  invFun := fun p => ⟨p.1, portRotate2 p.2⟩
  left_inv := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (portRotate2_involutive i)
  right_inv := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (portRotate2_involutive i)

def portTwoRotation : PortLocalRotation portTwoNetwork where
  rotate := portTwoRotateEquiv
  preservesRegion := by intro p; rfl

def portTwoRotationSystem : PortRotationSystem portTwoNetwork where
  toPortLocalRotation := portTwoRotation
  cyclic := by
    intro r i j
    fin_cases i <;> fin_cases j
    · exact ⟨0, rfl⟩
    · exact ⟨1, by
        rw [Function.iterate_succ_apply', Function.iterate_zero_apply]
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          rfl⟩
    · exact ⟨1, by
        rw [Function.iterate_succ_apply', Function.iterate_zero_apply]
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          rfl⟩
    · exact ⟨0, rfl⟩

def p22_00 : PortNetworkPort portTwoNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
def p22_01 : PortNetworkPort portTwoNetwork :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
def p22_10 : PortNetworkPort portTwoNetwork :=
  ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
def p22_11 : PortNetworkPort portTwoNetwork :=
  ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

theorem portFaceStep_22_00 :
    portFaceStep portTwoRotation portTwoCrossing p22_00 = p22_11 := by rfl
theorem portFaceStep_22_11 :
    portFaceStep portTwoRotation portTwoCrossing p22_11 = p22_00 := by rfl
theorem portFaceStep_22_01 :
    portFaceStep portTwoRotation portTwoCrossing p22_01 = p22_10 := by rfl
theorem portFaceStep_22_10 :
    portFaceStep portTwoRotation portTwoCrossing p22_10 = p22_01 := by rfl

theorem firstPortFaceReturn_22_00 :
    firstPortFaceReturn portTwoRotation portTwoCrossing p22_00 = 2 := by
  have hreturn :
      (portFaceStep portTwoRotation portTwoCrossing)^[2] p22_00 = p22_00 := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [portFaceStep_22_00, portFaceStep_22_11]
  have hle := firstPortFaceReturn_min portTwoRotation portTwoCrossing p22_00
    (m := 2) ⟨by decide, hreturn⟩
  have hnot :
      (portFaceStep portTwoRotation portTwoCrossing)^[1] p22_00 ≠ p22_00 := by
    rw [Function.iterate_succ_apply', Function.iterate_zero_apply,
      portFaceStep_22_00]
    decide
  have hge : 2 ≤ firstPortFaceReturn portTwoRotation portTwoCrossing p22_00 := by
    by_contra h
    have hlt : firstPortFaceReturn portTwoRotation portTwoCrossing p22_00 < 2 :=
      Nat.lt_of_not_ge h
    have hkpos := (firstPortFaceReturn_spec portTwoRotation
      portTwoCrossing p22_00).1
    have hkret := (firstPortFaceReturn_spec portTwoRotation
      portTwoCrossing p22_00).2
    have hkone : firstPortFaceReturn portTwoRotation portTwoCrossing p22_00 = 1 := by
      omega
    rw [hkone] at hkret
    exact hnot hkret
  exact Nat.le_antisymm hle hge

theorem firstPortFaceReturn_22_01 :
    firstPortFaceReturn portTwoRotation portTwoCrossing p22_01 = 2 := by
  have hreturn :
      (portFaceStep portTwoRotation portTwoCrossing)^[2] p22_01 = p22_01 := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [portFaceStep_22_01, portFaceStep_22_10]
  have hle := firstPortFaceReturn_min portTwoRotation portTwoCrossing p22_01
    (m := 2) ⟨by decide, hreturn⟩
  have hnot :
      (portFaceStep portTwoRotation portTwoCrossing)^[1] p22_01 ≠ p22_01 := by
    rw [Function.iterate_succ_apply', Function.iterate_zero_apply,
      portFaceStep_22_01]
    decide
  have hge : 2 ≤ firstPortFaceReturn portTwoRotation portTwoCrossing p22_01 := by
    by_contra h
    have hlt : firstPortFaceReturn portTwoRotation portTwoCrossing p22_01 < 2 :=
      Nat.lt_of_not_ge h
    have hkpos := (firstPortFaceReturn_spec portTwoRotation
      portTwoCrossing p22_01).1
    have hkret := (firstPortFaceReturn_spec portTwoRotation
      portTwoCrossing p22_01).2
    have hkone : firstPortFaceReturn portTwoRotation portTwoCrossing p22_01 = 1 := by
      omega
    rw [hkone] at hkret
    exact hnot hkret
  exact Nat.le_antisymm hle hge

example : portTwoNetwork.portCount = 4 := by decide
example (p : PortNetworkPort portTwoNetwork) :
    (portTwoRotation.rotate p).1 = p.1 :=
  portTwoRotation.preservesRegion p
example : PortRegionRotationCyclic portTwoRotation ⟨0, by decide⟩ :=
  portTwoRotationSystem.cyclic _
example (p : PortNetworkPort portTwoNetwork) :
    (portFaceEquiv portTwoRotation portTwoCrossing).symm
      (portFaceEquiv portTwoRotation portTwoCrossing p) = p := by
  exact (portFaceEquiv portTwoRotation portTwoCrossing).left_inv p
example (p : PortNetworkPort portTwoNetwork) :
    portEdgeSource portTwoCrossing (portFaceStep portTwoRotation portTwoCrossing p) =
      portEdgeTarget portTwoCrossing p :=
  portFaceStep_source portTwoRotation portTwoCrossing p

def portThreeNetwork : PortNetwork where
  regionCount := 2
  arity := fun _ => 3

def portRotate3 (i : Fin 3) : Fin 3 :=
  if i.val = 0 then ⟨1, by decide⟩
  else if i.val = 1 then ⟨2, by decide⟩
  else ⟨0, by omega⟩

def portRotate3Inv (i : Fin 3) : Fin 3 :=
  if i.val = 0 then ⟨2, by decide⟩
  else if i.val = 1 then ⟨0, by decide⟩
  else ⟨1, by omega⟩

theorem portRotate3Inv_rotate3 (i : Fin 3) : portRotate3Inv (portRotate3 i) = i := by
  fin_cases i <;> rfl

theorem portRotate3_rotate3Inv (i : Fin 3) : portRotate3 (portRotate3Inv i) = i := by
  fin_cases i <;> rfl

def portThreeRotateEquiv :
    PortNetworkPort portThreeNetwork ≃ PortNetworkPort portThreeNetwork where
  toFun := fun p => ⟨p.1, portRotate3 p.2⟩
  invFun := fun p => ⟨p.1, portRotate3Inv p.2⟩
  left_inv := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (portRotate3Inv_rotate3 i)
  right_inv := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (portRotate3_rotate3Inv i)

def portThreeRotation : PortLocalRotation portThreeNetwork where
  rotate := portThreeRotateEquiv
  preservesRegion := by intro p; rfl

theorem portRotate3_iterate (i j : Fin 3) :
    ∃ n : Nat, (portRotate3^[n]) i = j := by
  fin_cases i <;> fin_cases j
  · exact ⟨0, rfl⟩
  · exact ⟨1, by simp [portRotate3]⟩
  · exact ⟨2, by simp [portRotate3]⟩
  · exact ⟨2, by simp [portRotate3]⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, by simp [portRotate3]⟩
  · exact ⟨1, by simp [portRotate3]⟩
  · exact ⟨2, by simp [portRotate3]⟩
  · exact ⟨0, rfl⟩

theorem portThreeRotate_iterate (r : Fin 2) (i : Fin 3) (n : Nat) :
    (portThreeRotation.rotate^[n]) ⟨r, i⟩ =
      ⟨r, (portRotate3^[n]) i⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [Function.iterate_succ_apply']
    rfl

def portThreeRotationSystem : PortRotationSystem portThreeNetwork where
  toPortLocalRotation := portThreeRotation
  cyclic := by
    intro r i j
    obtain ⟨n, hn⟩ := portRotate3_iterate i j
    exact ⟨n, by
      calc
        (portThreeRotation.rotate^[n]) ⟨r, i⟩ =
            ⟨r, (portRotate3^[n]) i⟩ := portThreeRotate_iterate r i n
        _ = ⟨r, j⟩ := by rw [hn]⟩

def p30 : PortNetworkPort portThreeNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
def p31 : PortNetworkPort portThreeNetwork :=
  ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩
def p32 : PortNetworkPort portThreeNetwork :=
  ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩
def p33 : PortNetworkPort portThreeNetwork :=
  ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
def p34 : PortNetworkPort portThreeNetwork :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
def p35 : PortNetworkPort portThreeNetwork :=
  ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩

def portThreeCrossing : PortCrossing portThreeNetwork where
  cross := fun p => ⟨portSwap2 p.1, p.2⟩
  involutive := by
    intro p
    apply Sigma.ext
    · exact portSwap2_involutive p.1
    · exact heq_of_eq rfl
  changesRegion := by
    intro p
    exact portSwap2_ne p.1

theorem portFaceStep_30 :
    portFaceStep portThreeRotation portThreeCrossing p30 = p31 := by rfl
theorem portFaceStep_31 :
    portFaceStep portThreeRotation portThreeCrossing p31 = p32 := by rfl
theorem portFaceStep_32 :
    portFaceStep portThreeRotation portThreeCrossing p32 = p33 := by rfl
theorem portFaceStep_33 :
    portFaceStep portThreeRotation portThreeCrossing p33 = p34 := by rfl
theorem portFaceStep_34 :
    portFaceStep portThreeRotation portThreeCrossing p34 = p35 := by rfl
theorem portFaceStep_35 :
    portFaceStep portThreeRotation portThreeCrossing p35 = p30 := by rfl

theorem portFaceStep_iterate_30_1 :
    (portFaceStep portThreeRotation portThreeCrossing)^[1] p30 = p31 := by
  rw [Function.iterate_succ_apply', Function.iterate_zero_apply]
  exact portFaceStep_30
theorem portFaceStep_iterate_30_2 :
    (portFaceStep portThreeRotation portThreeCrossing)^[2] p30 = p32 := by
  rw [Function.iterate_succ_apply', portFaceStep_iterate_30_1]
  exact portFaceStep_31
theorem portFaceStep_iterate_30_3 :
    (portFaceStep portThreeRotation portThreeCrossing)^[3] p30 = p33 := by
  rw [Function.iterate_succ_apply', portFaceStep_iterate_30_2]
  exact portFaceStep_32
theorem portFaceStep_iterate_30_4 :
    (portFaceStep portThreeRotation portThreeCrossing)^[4] p30 = p34 := by
  rw [Function.iterate_succ_apply', portFaceStep_iterate_30_3]
  exact portFaceStep_33
theorem portFaceStep_iterate_30_5 :
    (portFaceStep portThreeRotation portThreeCrossing)^[5] p30 = p35 := by
  rw [Function.iterate_succ_apply', portFaceStep_iterate_30_4]
  exact portFaceStep_34
theorem portFaceStep_iterate_30_6 :
    (portFaceStep portThreeRotation portThreeCrossing)^[6] p30 = p30 := by
  rw [Function.iterate_succ_apply', portFaceStep_iterate_30_5]
  exact portFaceStep_35

theorem firstPortFaceReturn_30 :
    firstPortFaceReturn portThreeRotation portThreeCrossing p30 = 6 := by
  have hle := firstPortFaceReturn_min portThreeRotation portThreeCrossing p30
    (m := 6) ⟨by decide, portFaceStep_iterate_30_6⟩
  have hnot : ∀ n : Nat, 0 < n → n < 6 →
      (portFaceStep portThreeRotation portThreeCrossing)^[n] p30 ≠ p30 := by
    intro n hn hlt hneq
    have hc : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · rw [portFaceStep_iterate_30_1] at hneq
      exact (by decide : p31 ≠ p30) hneq
    · rw [portFaceStep_iterate_30_2] at hneq
      exact (by decide : p32 ≠ p30) hneq
    · rw [portFaceStep_iterate_30_3] at hneq
      exact (by decide : p33 ≠ p30) hneq
    · rw [portFaceStep_iterate_30_4] at hneq
      exact (by decide : p34 ≠ p30) hneq
    · rw [portFaceStep_iterate_30_5] at hneq
      exact (by decide : p35 ≠ p30) hneq
  have hge : 6 ≤ firstPortFaceReturn portThreeRotation portThreeCrossing p30 := by
    by_contra h
    exact hnot _ (firstPortFaceReturn_spec portThreeRotation
      portThreeCrossing p30).1 (Nat.lt_of_not_ge h)
      (firstPortFaceReturn_spec portThreeRotation portThreeCrossing p30).2
  exact Nat.le_antisymm hle hge

def portDeltaAAssignment : V4FlowAssignment portTwoCrossing where
  label := fun _ => deltaA
  nonzero := by intro; exact deltaA_ne_zero
  cross_sameLabel := by intro; rfl

def portDeltaBAssignment : V4FlowAssignment portTwoCrossing where
  label := fun _ => deltaB
  nonzero := by intro; exact deltaB_ne_zero
  cross_sameLabel := by intro; rfl

example (p : PortNetworkPort portTwoNetwork) :
    faceStep (portTwoRotation.toFlowLocalRotation portDeltaAAssignment)
      portDeltaAAssignment.toFlowCrossing p =
      portFaceStep portTwoRotation portTwoCrossing p :=
  portFaceStep_of_flow_lift portTwoRotation portDeltaAAssignment p

example (p : PortNetworkPort portTwoNetwork) :
    faceStep (portTwoRotation.toFlowLocalRotation portDeltaBAssignment)
      portDeltaBAssignment.toFlowCrossing p =
      portFaceStep portTwoRotation portTwoCrossing p :=
  portFaceStep_of_flow_lift portTwoRotation portDeltaBAssignment p

example (p : PortNetworkPort portTwoNetwork) :
    faceStep (portTwoRotation.toFlowLocalRotation portDeltaAAssignment)
      portDeltaAAssignment.toFlowCrossing p =
      faceStep (portTwoRotation.toFlowLocalRotation portDeltaBAssignment)
        portDeltaBAssignment.toFlowCrossing p :=
  portFaceStep_assignment_independent portTwoRotation
    portDeltaAAssignment portDeltaBAssignment p

example (p : PortNetworkPort twoThreeNetwork.toPortNetwork) :
    portFaceStep twoThreeRotation.toPortLocalRotation
      twoThreeCrossing.toPortCrossing p =
      faceStep twoThreeRotation twoThreeCrossing p :=
  portFaceStep_of_flow_erasure twoThreeRotation twoThreeCrossing p

example (p : PortNetworkPort twoThreeNetwork.toPortNetwork) :
    faceStep (twoThreeRotation.toPortLocalRotation.toFlowLocalRotation
      twoThreeCrossing.toV4FlowAssignment)
      twoThreeCrossing.toV4FlowAssignment.toFlowCrossing p =
      faceStep twoThreeRotation twoThreeCrossing p :=
  portFaceStep_round_trip twoThreeRotation twoThreeCrossing p

#print axioms DkMath.Tromino.PortLocalRotation.iterate_preservesRegion
#print axioms DkMath.Tromino.PortRotationSystem.rotation_reaches
#print axioms DkMath.Tromino.portFaceEquiv
#print axioms DkMath.Tromino.portFaceStep_periodic
#print axioms DkMath.Tromino.firstPortFaceReturn_spec
#print axioms DkMath.Tromino.FlowLocalRotation.toPortLocalRotation
#print axioms DkMath.Tromino.PortLocalRotation.toFlowLocalRotation
#print axioms DkMath.Tromino.portFaceStep_assignment_independent
#print axioms DkMath.Tromino.portFaceStep_round_trip

end DkMathTest.Tromino.PortRotationSystemAxiomAudit
