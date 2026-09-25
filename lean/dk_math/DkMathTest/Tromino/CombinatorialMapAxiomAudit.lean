/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.CombinatorialMap
import DkMathTest.Tromino.FaceOrbitAxiomAudit

#print "file: DkMathTest.Tromino.CombinatorialMapAxiomAudit"

namespace DkMathTest.Tromino.CombinatorialMapAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.FlowTransitionXorAxiomAudit
open DkMathTest.Tromino.RotationSystemAxiomAudit
open DkMathTest.Tromino.FaceOrbitAxiomAudit

def rotate2 (i : Fin 2) : Fin 2 :=
  ⟨1 - i.val, by omega⟩

theorem rotate2_involutive (i : Fin 2) : rotate2 (rotate2 i) = i := by
  apply Fin.ext
  dsimp [rotate2]
  omega

def twoTwoRotateEquiv :
    FlowNetworkPort twoRegionFlowNetwork ≃ FlowNetworkPort twoRegionFlowNetwork where
  toFun := fun p => ⟨p.1, rotate2 p.2⟩
  invFun := fun p => ⟨p.1, rotate2 p.2⟩
  left_inv := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (rotate2_involutive i)
  right_inv := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (rotate2_involutive i)

def twoTwoRotation : FlowLocalRotation twoRegionFlowNetwork where
  rotate := twoTwoRotateEquiv
  preservesRegion := by intro p; rfl

def twoTwoRotationSystem : FlowRotationSystem twoRegionFlowNetwork where
  toFlowLocalRotation := twoTwoRotation
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

def p22_00 : FlowNetworkPort twoRegionFlowNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

def p22_01 : FlowNetworkPort twoRegionFlowNetwork :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

def p22_10 : FlowNetworkPort twoRegionFlowNetwork :=
  ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

def p22_11 : FlowNetworkPort twoRegionFlowNetwork :=
  ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

theorem twoTwo_faceStep_00 :
    faceStep twoTwoRotation twoRegionFlowCrossing p22_00 = p22_11 := by
  rfl

theorem twoTwo_faceStep_11 :
    faceStep twoTwoRotation twoRegionFlowCrossing p22_11 = p22_00 := by
  rfl

theorem twoTwo_faceStep_01 :
    faceStep twoTwoRotation twoRegionFlowCrossing p22_01 = p22_10 := by
  rfl

theorem twoTwo_faceStep_10 :
    faceStep twoTwoRotation twoRegionFlowCrossing p22_10 = p22_01 := by
  rfl

theorem twoTwo_firstFaceReturn_00 :
    firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_00 = 2 := by
  have hreturn :
      (faceStep twoTwoRotation twoRegionFlowCrossing)^[2] p22_00 = p22_00 := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [twoTwo_faceStep_00, twoTwo_faceStep_11]
  have hle : firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_00 ≤ 2 :=
    firstFaceReturn_min twoTwoRotation twoRegionFlowCrossing p22_00
      ⟨by decide, hreturn⟩
  have hnot :
      (faceStep twoTwoRotation twoRegionFlowCrossing)^[1] p22_00 ≠ p22_00 := by
    rw [Function.iterate_succ_apply', Function.iterate_zero_apply,
      twoTwo_faceStep_00]
    decide
  have hge : 2 ≤ firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_00 := by
    by_contra h
    have hlt : firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_00 < 2 :=
      Nat.lt_of_not_ge h
    have hkpos := (firstFaceReturn_spec twoTwoRotation
      twoRegionFlowCrossing p22_00).1
    have hkret := (firstFaceReturn_spec twoTwoRotation
      twoRegionFlowCrossing p22_00).2
    have hkone : firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_00 = 1 := by
      omega
    rw [hkone] at hkret
    exact hnot hkret
  exact Nat.le_antisymm hle hge

theorem twoTwo_firstFaceReturn_01 :
    firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_01 = 2 := by
  have hreturn :
      (faceStep twoTwoRotation twoRegionFlowCrossing)^[2] p22_01 = p22_01 := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [twoTwo_faceStep_01, twoTwo_faceStep_10]
  have hle : firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_01 ≤ 2 :=
    firstFaceReturn_min twoTwoRotation twoRegionFlowCrossing p22_01
      ⟨by decide, hreturn⟩
  have hnot :
      (faceStep twoTwoRotation twoRegionFlowCrossing)^[1] p22_01 ≠ p22_01 := by
    rw [Function.iterate_succ_apply', Function.iterate_zero_apply,
      twoTwo_faceStep_01]
    decide
  have hge : 2 ≤ firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_01 := by
    by_contra h
    have hlt : firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_01 < 2 :=
      Nat.lt_of_not_ge h
    have hkpos := (firstFaceReturn_spec twoTwoRotation
      twoRegionFlowCrossing p22_01).1
    have hkret := (firstFaceReturn_spec twoTwoRotation
      twoRegionFlowCrossing p22_01).2
    have hkone : firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_01 = 1 := by
      omega
    rw [hkone] at hkret
    exact hnot hkret
  exact Nat.le_antisymm hle hge

theorem twoTwo_firstFaceReturn_10 :
    firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_10 = 2 := by
  calc
    firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_10 =
        firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_01 :=
      firstFaceReturn_eq_of_mem twoTwoRotation twoRegionFlowCrossing
        p22_01 p22_10
        ((faceOrbit_mem_iff_iterate twoTwoRotation twoRegionFlowCrossing
          p22_01 p22_10).2 ⟨1, twoTwo_faceStep_01⟩)
    _ = 2 := twoTwo_firstFaceReturn_01

theorem twoTwo_firstFaceReturn_11 :
    firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_11 = 2 := by
  calc
    firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_11 =
        firstFaceReturn twoTwoRotation twoRegionFlowCrossing p22_00 :=
      firstFaceReturn_eq_of_mem twoTwoRotation twoRegionFlowCrossing
        p22_00 p22_11
        ((faceOrbit_mem_iff_iterate twoTwoRotation twoRegionFlowCrossing
          p22_00 p22_11).2 ⟨1, twoTwo_faceStep_00⟩)
    _ = 2 := twoTwo_firstFaceReturn_00

theorem twoTwo_faceOrbit_card (p : FlowNetworkPort twoRegionFlowNetwork) :
    (faceOrbit twoTwoRotation twoRegionFlowCrossing p).card = 2 := by
  rw [faceOrbit_card]
  cases p with
  | mk r i =>
    fin_cases r <;> fin_cases i
    · exact twoTwo_firstFaceReturn_00
    · exact twoTwo_firstFaceReturn_01
    · exact twoTwo_firstFaceReturn_10
    · exact twoTwo_firstFaceReturn_11

theorem twoTwo_faceCount :
    faceCount twoTwoRotation twoRegionFlowCrossing = 2 := by
  have hcards : ∀ F ∈ faceOrbits twoTwoRotation twoRegionFlowCrossing,
      F.card = 2 := by
    intro F hF
    rcases (faceOrbits_mem_iff twoTwoRotation twoRegionFlowCrossing F).mp hF with
      ⟨p, rfl⟩
    exact twoTwo_faceOrbit_card p
  have hsum := faceSum_card twoTwoRotation twoRegionFlowCrossing
  have hcount :
      faceCount twoTwoRotation twoRegionFlowCrossing * 2 =
        totalPortCount twoRegionFlowNetwork := by
    calc
      faceCount twoTwoRotation twoRegionFlowCrossing * 2 =
          ∑ F ∈ faceOrbits twoTwoRotation twoRegionFlowCrossing, 2 := by
            simp [faceCount, Nat.mul_comm]
      _ = ∑ F ∈ faceOrbits twoTwoRotation twoRegionFlowCrossing, F.card := by
        apply Finset.sum_congr rfl
        intro F hF
        exact (hcards F hF).symm
      _ = totalPortCount twoRegionFlowNetwork := hsum
  have hports : totalPortCount twoRegionFlowNetwork = 4 := by decide
  omega

theorem twoRegion_connected (r s : Fin 2) :
    RegionReachable twoRegionFlowCrossing r s := by
  fin_cases r <;> fin_cases s
  · exact regionReachable_refl twoRegionFlowCrossing _
  · exact ⟨FlowRegionWalk.singleton twoRegionFlowCrossing p22_00⟩
  · exact ⟨FlowRegionWalk.singleton twoRegionFlowCrossing p22_10⟩
  · exact regionReachable_refl twoRegionFlowCrossing _

def twoTwoMap : FlowCombinatorialMap twoRegionFlowNetwork where
  crossing := twoRegionFlowCrossing
  rotation := twoTwoRotationSystem
  nonemptyRegions := by decide
  connected := twoRegion_connected

example : twoTwoMap.vertexCount = 2 := by decide
theorem twoTwo_edgeCount : twoTwoMap.edgeCount = 2 := by
  change crossingEdgeCount twoRegionFlowCrossing = 2
  have h := two_mul_crossingEdgeCount twoRegionFlowCrossing
  have hp : totalPortCount twoRegionFlowNetwork = 4 := by decide
  omega
example : twoTwoMap.faceCount = 2 := by exact twoTwo_faceCount
example : twoTwoMap.portCount = 4 := by decide
theorem twoTwo_eulerCharacteristic : twoTwoMap.eulerCharacteristic = 2 := by
  have he : crossingEdgeCount twoRegionFlowCrossing = 2 := by
    have h := two_mul_crossingEdgeCount twoRegionFlowCrossing
    have hp : totalPortCount twoRegionFlowNetwork = 4 := by decide
    omega
  change (regionVertexCount twoRegionFlowNetwork : Int)
    - (crossingEdgeCount twoRegionFlowCrossing : Int)
    + (faceCount twoTwoRotation twoRegionFlowCrossing : Int) = 2
  rw [twoTwo_faceCount, he]
  decide

example : HasSphereCharacteristic twoTwoMap := by
  change twoTwoMap.eulerCharacteristic = 2
  exact twoTwo_eulerCharacteristic

example : HasCombinatorialGenus twoTwoMap 0 := by
  rw [HasCombinatorialGenus]
  rw [twoTwo_eulerCharacteristic]
  norm_num

example (p q : FlowNetworkPort twoRegionFlowNetwork)
    (hregion : p.1 = q.1) :
    SameVertexRotationOrbit twoTwoMap p q :=
  twoTwoMap.sameVertexRotationOrbit_of_same_region p q hregion

theorem twoThree_connected (r s : Fin 2) :
    RegionReachable twoThreeCrossing r s := by
  fin_cases r <;> fin_cases s
  · exact regionReachable_refl twoThreeCrossing _
  · exact ⟨FlowRegionWalk.singleton twoThreeCrossing p23⟩
  · exact ⟨FlowRegionWalk.singleton twoThreeCrossing p23₃⟩
  · exact regionReachable_refl twoThreeCrossing _

theorem twoThree_firstFaceReturn_of_mem
    (p : FlowNetworkPort twoThreeNetwork) :
    firstFaceReturn twoThreeRotation twoThreeCrossing p = 6 := by
  cases p with
  | mk r i =>
    fin_cases r <;> fin_cases i
    · exact firstFaceReturn_p23
    · calc
        firstFaceReturn twoThreeRotation twoThreeCrossing p23₄ =
            firstFaceReturn twoThreeRotation twoThreeCrossing p23 :=
          firstFaceReturn_eq_of_mem twoThreeRotation twoThreeCrossing
            p23 p23₄
            ((faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
              p23 p23₄).2 ⟨4, faceStep_iterate_23_4⟩)
        _ = 6 := firstFaceReturn_p23
    · calc
        firstFaceReturn twoThreeRotation twoThreeCrossing p23₂ =
            firstFaceReturn twoThreeRotation twoThreeCrossing p23 :=
          firstFaceReturn_eq_of_mem twoThreeRotation twoThreeCrossing
            p23 p23₂
            ((faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
              p23 p23₂).2 ⟨2, faceStep_iterate_23_2⟩)
        _ = 6 := firstFaceReturn_p23
    · calc
        firstFaceReturn twoThreeRotation twoThreeCrossing p23₃ =
            firstFaceReturn twoThreeRotation twoThreeCrossing p23 :=
          firstFaceReturn_eq_of_mem twoThreeRotation twoThreeCrossing
            p23 p23₃
            ((faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
              p23 p23₃).2 ⟨3, faceStep_iterate_23_3⟩)
        _ = 6 := firstFaceReturn_p23
    · calc
        firstFaceReturn twoThreeRotation twoThreeCrossing p23₁ =
            firstFaceReturn twoThreeRotation twoThreeCrossing p23 :=
          firstFaceReturn_eq_of_mem twoThreeRotation twoThreeCrossing
            p23 p23₁
            ((faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
              p23 p23₁).2 ⟨1, faceStep_iterate_23_1⟩)
        _ = 6 := firstFaceReturn_p23
    · calc
        firstFaceReturn twoThreeRotation twoThreeCrossing p23₅ =
            firstFaceReturn twoThreeRotation twoThreeCrossing p23 :=
          firstFaceReturn_eq_of_mem twoThreeRotation twoThreeCrossing
            p23 p23₅
            ((faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
              p23 p23₅).2 ⟨5, faceStep_iterate_23_5⟩)
        _ = 6 := firstFaceReturn_p23

theorem twoThree_faceCount :
    faceCount twoThreeRotation twoThreeCrossing = 1 := by
  have hcards : ∀ F ∈ faceOrbits twoThreeRotation twoThreeCrossing,
      F.card = 6 := by
    intro F hF
    rcases (faceOrbits_mem_iff twoThreeRotation twoThreeCrossing F).mp hF with
      ⟨p, rfl⟩
    rw [faceOrbit_card]
    exact twoThree_firstFaceReturn_of_mem p
  have hsum := faceSum_card twoThreeRotation twoThreeCrossing
  have hcount :
      faceCount twoThreeRotation twoThreeCrossing * 6 =
        totalPortCount twoThreeNetwork := by
    calc
      faceCount twoThreeRotation twoThreeCrossing * 6 =
          ∑ F ∈ faceOrbits twoThreeRotation twoThreeCrossing, 6 := by
            simp [faceCount, Nat.mul_comm]
      _ = ∑ F ∈ faceOrbits twoThreeRotation twoThreeCrossing, F.card := by
        apply Finset.sum_congr rfl
        intro F hF
        exact (hcards F hF).symm
      _ = totalPortCount twoThreeNetwork := hsum
  have hports : totalPortCount twoThreeNetwork = 6 := by decide
  omega

def twoThreeMap : FlowCombinatorialMap twoThreeNetwork where
  crossing := twoThreeCrossing
  rotation := twoThreeRotationSystem
  nonemptyRegions := by decide
  connected := twoThree_connected

example : twoThreeMap.vertexCount = 2 := by decide
theorem twoThree_edgeCount : twoThreeMap.edgeCount = 3 := by
  change crossingEdgeCount twoThreeCrossing = 3
  have h := two_mul_crossingEdgeCount twoThreeCrossing
  have hp : totalPortCount twoThreeNetwork = 6 := by decide
  omega
example : twoThreeMap.faceCount = 1 := by exact twoThree_faceCount
example : twoThreeMap.portCount = 6 := by decide
theorem twoThree_eulerCharacteristic : twoThreeMap.eulerCharacteristic = 0 := by
  have he : crossingEdgeCount twoThreeCrossing = 3 := by
    have h := two_mul_crossingEdgeCount twoThreeCrossing
    have hp : totalPortCount twoThreeNetwork = 6 := by decide
    omega
  change (regionVertexCount twoThreeNetwork : Int)
    - (crossingEdgeCount twoThreeCrossing : Int)
    + (faceCount twoThreeRotation twoThreeCrossing : Int) = 0
  rw [twoThree_faceCount, he]
  decide

example : HasCombinatorialGenus twoThreeMap 1 := by
  rw [HasCombinatorialGenus]
  rw [twoThree_eulerCharacteristic]
  norm_num

theorem twoFour_identity_not_cyclic :
    ¬ RegionRotationCyclic twoFourIdentityRotation
      (⟨0, by decide⟩ : Fin twoFourNetwork.regionCount) := by
  intro h
  obtain ⟨n, hn⟩ := h ⟨0, by decide⟩ ⟨1, by decide⟩
  have hbad :
      (⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ :
        FlowNetworkPort twoFourNetwork) =
      ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ := by
    simp [twoFourIdentityRotation] at hn
  exact (by decide : ¬ ((⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ :
    FlowNetworkPort twoFourNetwork) =
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩)) hbad

#print axioms DkMath.Tromino.FlowCombinatorialMap
#print axioms DkMath.Tromino.FlowCombinatorialMap.rotation_reaches_same_region
#print axioms DkMath.Tromino.combinatorialGenus_unique
#print axioms DkMath.Tromino.combinatorialGenus_zero_iff
#print axioms DkMath.Tromino.combinatorialGenus_one_iff
#print axioms DkMath.Tromino.combinatorialGenus_characteristic_le_two
#print axioms DkMath.Tromino.combinatorialGenus_characteristic_even
#print axioms DkMath.Tromino.HasSphereCharacteristic
#print axioms DkMath.Tromino.hasSphereCharacteristic_iff_genus_zero

end DkMathTest.Tromino.CombinatorialMapAxiomAudit
