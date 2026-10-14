/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.EulerCount
import DkMathTest.Tromino.FaceOrbitAxiomAudit

#print "file: DkMathTest.Tromino.EulerCountAxiomAudit"

namespace DkMathTest.Tromino.EulerCountAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.FaceOrbitAxiomAudit
open DkMathTest.Tromino.RotationSystemAxiomAudit

example (p : FlowNetworkPort twoThreeNetwork) :
    (crossingEdgePair twoThreeCrossing p).card = 2 :=
  crossingEdgePair_card twoThreeCrossing p
example (p : FlowNetworkPort twoThreeNetwork) :
    crossingEdgePair twoThreeCrossing (twoThreeCrossing.cross p) =
      crossingEdgePair twoThreeCrossing p :=
  crossingEdgePair_cross_eq twoThreeCrossing p
example (p q : FlowNetworkPort twoThreeNetwork) :
    crossingEdgePair twoThreeCrossing p =
        crossingEdgePair twoThreeCrossing q ∨
      Disjoint (crossingEdgePair twoThreeCrossing p)
        (crossingEdgePair twoThreeCrossing q) :=
  crossingEdgePair_eq_or_disjoint twoThreeCrossing p q
example (p : FlowNetworkPort twoThreeNetwork) :
    ∃ E ∈ crossingEdgeOrbits twoThreeCrossing, p ∈ E :=
  crossingEdgeOrbits_coverage twoThreeCrossing p
example :
    (∑ E ∈ crossingEdgeOrbits twoThreeCrossing, E.card) =
      totalPortCount twoThreeNetwork :=
  crossingEdgeSum_card twoThreeCrossing
example : 2 * crossingEdgeCount twoThreeCrossing =
    totalPortCount twoThreeNetwork :=
  two_mul_crossingEdgeCount twoThreeCrossing

theorem twoThree_faceOrbit_cover (p : FlowNetworkPort twoThreeNetwork) :
    p ∈ faceOrbit twoThreeRotation twoThreeCrossing p23 := by
  rcases p with ⟨r, i⟩
  fin_cases r <;> fin_cases i
  · exact faceOrbit_contains twoThreeRotation twoThreeCrossing p23
  · exact (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
      p23 p23₄).2 ⟨4, faceStep_iterate_23_4⟩
  · exact (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
      p23 p23₂).2 ⟨2, faceStep_iterate_23_2⟩
  · exact (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
      p23 p23₃).2 ⟨3, faceStep_iterate_23_3⟩
  · exact (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
      p23 p23₁).2 ⟨1, faceStep_iterate_23_1⟩
  · exact (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
      p23 p23₅).2 ⟨5, faceStep_iterate_23_5⟩

theorem twoThree_faceOrbits_eq_singleton :
    faceOrbits twoThreeRotation twoThreeCrossing =
      {faceOrbit twoThreeRotation twoThreeCrossing p23} := by
  ext F
  constructor
  · intro hF
    rcases (faceOrbits_mem_iff twoThreeRotation twoThreeCrossing F).mp hF
      with ⟨p, rfl⟩
    have hp := twoThree_faceOrbit_cover p
    rw [faceOrbit_eq_of_mem twoThreeRotation twoThreeCrossing p23 p hp]
    simp
  · intro hF
    simp only [Finset.mem_singleton] at hF
    subst F
    exact faceOrbit_mem_orbits twoThreeRotation twoThreeCrossing p23

example :
    ∃ F ∈ faceOrbits twoThreeRotation twoThreeCrossing, p23 ∈ F :=
  faceOrbits_coverage twoThreeRotation twoThreeCrossing p23
example :
    ((faceOrbits twoThreeRotation twoThreeCrossing : Finset
      (Finset (FlowNetworkPort twoThreeNetwork))) : Set
      (Finset (FlowNetworkPort twoThreeNetwork))).Pairwise Disjoint :=
  faceOrbits_pairwise_disjoint twoThreeRotation twoThreeCrossing
example :
    (∑ F ∈ faceOrbits twoThreeRotation twoThreeCrossing, F.card) =
      totalPortCount twoThreeNetwork :=
  faceSum_card twoThreeRotation twoThreeCrossing

theorem twoThree_crossingEdgeCount :
    crossingEdgeCount twoThreeCrossing = 3 := by
  have hD : totalPortCount twoThreeNetwork = 6 := by decide
  have h := two_mul_crossingEdgeCount twoThreeCrossing
  rw [hD] at h
  omega
theorem twoThree_faceCount : faceCount twoThreeRotation twoThreeCrossing = 1 := by
  change (faceOrbits twoThreeRotation twoThreeCrossing).card = 1
  rw [twoThree_faceOrbits_eq_singleton]
  simp
example : regionVertexCount twoThreeNetwork = 2 := by decide
example : crossingEdgeCount twoThreeCrossing = 3 := twoThree_crossingEdgeCount
example : faceCount twoThreeRotation twoThreeCrossing = 1 := twoThree_faceCount
example :
    combinatorialEulerCharacteristic twoThreeRotation twoThreeCrossing = 0 := by
  norm_num [combinatorialEulerCharacteristic, regionVertexCount,
    twoThreeNetwork, twoThree_crossingEdgeCount, twoThree_faceCount]
example :
    (∑ F ∈ faceOrbits twoThreeRotation twoThreeCrossing, F.card) = 6 := by
  rw [faceSum_card]
  decide

theorem twoFour_firstFaceReturn (p : FlowNetworkPort twoFourNetwork) :
    firstFaceReturn twoFourIdentityRotation twoFourCrossing p = 2 := by
  have hreturn :
      (faceStep twoFourIdentityRotation twoFourCrossing)^[2] p = p := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_zero_apply]
    change twoFourCrossing.cross (twoFourCrossing.cross p) = p
    exact twoFourCrossing.involutive p
  have hle : firstFaceReturn twoFourIdentityRotation twoFourCrossing p ≤ 2 :=
    firstFaceReturn_min twoFourIdentityRotation twoFourCrossing p
      ⟨by decide, hreturn⟩
  have hnot :
      (faceStep twoFourIdentityRotation twoFourCrossing)^[1] p ≠ p := by
    rw [Function.iterate_succ_apply', Function.iterate_zero_apply]
    change twoFourCrossing.cross p ≠ p
    intro h
    apply twoFourCrossing.changesRegion p
    exact congrArg Sigma.fst h
  have hge : 2 ≤ firstFaceReturn twoFourIdentityRotation twoFourCrossing p := by
    by_contra h
    have hlt : firstFaceReturn twoFourIdentityRotation twoFourCrossing p < 2 :=
      Nat.lt_of_not_ge h
    have hkpos := (firstFaceReturn_spec twoFourIdentityRotation
      twoFourCrossing p).1
    have hkret := (firstFaceReturn_spec twoFourIdentityRotation
      twoFourCrossing p).2
    have hkone : firstFaceReturn twoFourIdentityRotation twoFourCrossing p = 1 := by
      omega
    rw [hkone] at hkret
    exact hnot hkret
  exact Nat.le_antisymm hle hge

theorem twoFour_faceOrbit_eq_edgePair (p : FlowNetworkPort twoFourNetwork) :
    faceOrbit twoFourIdentityRotation twoFourCrossing p =
      crossingEdgePair twoFourCrossing p := by
  unfold faceOrbit
  rw [twoFour_firstFaceReturn p]
  ext q
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, hqn⟩
    have hnlt : n < 2 := Finset.mem_range.mp hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · have hqeq : p = q := by
        simpa [Function.iterate_zero_apply] using hqn
      rw [← hqeq]
      exact crossingEdgePair_mem twoFourCrossing p
    · have hqeq : twoFourCrossing.cross p = q := by
        simpa [faceStep, twoFourIdentityRotation,
          Function.iterate_succ_apply', Function.iterate_zero_apply] using hqn
      rw [← hqeq]
      exact crossingEdgePair_cross_mem twoFourCrossing p
  · intro hq
    simp only [crossingEdgePair, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Finset.mem_image.mpr
        ⟨0, by simp, by simp⟩
    · exact Finset.mem_image.mpr
        ⟨1, by simp [faceStep, twoFourIdentityRotation]⟩

theorem twoFour_faceOrbits_eq_edgeOrbits :
    faceOrbits twoFourIdentityRotation twoFourCrossing =
      crossingEdgeOrbits twoFourCrossing := by
  ext F
  constructor
  · intro hF
    rcases (faceOrbits_mem_iff twoFourIdentityRotation twoFourCrossing F).mp hF
      with ⟨p, rfl⟩
    rw [twoFour_faceOrbit_eq_edgePair]
    exact crossingEdgePair_mem_orbits twoFourCrossing p
  · intro hE
    rcases (crossingEdgeOrbits_mem_iff twoFourCrossing F).mp hE
      with ⟨p, rfl⟩
    rw [← twoFour_faceOrbit_eq_edgePair]
    exact faceOrbit_mem_orbits twoFourIdentityRotation twoFourCrossing p

theorem twoFour_crossingEdgeCount :
    crossingEdgeCount twoFourCrossing = 4 := by
  have hD : totalPortCount twoFourNetwork = 8 := by decide
  have h := two_mul_crossingEdgeCount twoFourCrossing
  rw [hD] at h
  omega
theorem twoFour_faceCount : faceCount twoFourIdentityRotation twoFourCrossing = 4 := by
  change (faceOrbits twoFourIdentityRotation twoFourCrossing).card = 4
  rw [twoFour_faceOrbits_eq_edgeOrbits]
  exact twoFour_crossingEdgeCount
example : regionVertexCount twoFourNetwork = 2 := by decide
example : crossingEdgeCount twoFourCrossing = 4 := twoFour_crossingEdgeCount
example : faceCount twoFourIdentityRotation twoFourCrossing = 4 := twoFour_faceCount
example :
    combinatorialEulerCharacteristic twoFourIdentityRotation twoFourCrossing = 2 := by
  norm_num [combinatorialEulerCharacteristic, regionVertexCount,
    twoFourNetwork, twoFour_crossingEdgeCount, twoFour_faceCount]
example :
    combinatorialEulerCharacteristic twoThreeRotation twoThreeCrossing ≠
      combinatorialEulerCharacteristic twoFourIdentityRotation twoFourCrossing := by
  norm_num [combinatorialEulerCharacteristic, regionVertexCount,
    twoThreeNetwork, twoThree_crossingEdgeCount, twoThree_faceCount,
    twoFourNetwork, twoFour_crossingEdgeCount, twoFour_faceCount]
example :
    (∑ F ∈ faceOrbits twoFourIdentityRotation twoFourCrossing, F.card) =
      totalPortCount twoFourNetwork :=
  faceSum_card twoFourIdentityRotation twoFourCrossing

#print axioms DkMath.Tromino.crossingEdgePair_card
#print axioms DkMath.Tromino.crossingEdgeOrbits_pairwise_disjoint
#print axioms DkMath.Tromino.crossingEdgeCount_mul_two
#print axioms DkMath.Tromino.faceOrbits_pairwise_disjoint
#print axioms DkMath.Tromino.faceSum_card
#print axioms DkMath.Tromino.combinatorialEulerCharacteristic

end DkMathTest.Tromino.EulerCountAxiomAudit
