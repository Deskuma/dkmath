/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FaceOrbit
import DkMathTest.Tromino.RotationSystemAxiomAudit

#print "file: DkMathTest.Tromino.FaceOrbitAxiomAudit"

namespace DkMathTest.Tromino.FaceOrbitAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.FlowTransitionXorAxiomAudit
open DkMathTest.Tromino.RotationSystemAxiomAudit

def p23₁ : FlowNetworkPort twoThreeNetwork := ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩
def p23₂ : FlowNetworkPort twoThreeNetwork := ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩
def p23₃ : FlowNetworkPort twoThreeNetwork := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
def p23₄ : FlowNetworkPort twoThreeNetwork := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
def p23₅ : FlowNetworkPort twoThreeNetwork := ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩

theorem faceStep_23_1 : faceStep twoThreeRotation twoThreeCrossing p23₁ = p23₂ := by rfl
theorem faceStep_23_2 : faceStep twoThreeRotation twoThreeCrossing p23₂ = p23₃ := by rfl
theorem faceStep_23_3 : faceStep twoThreeRotation twoThreeCrossing p23₃ = p23₄ := by rfl
theorem faceStep_23_4 : faceStep twoThreeRotation twoThreeCrossing p23₄ = p23₅ := by rfl
theorem faceStep_23_5 : faceStep twoThreeRotation twoThreeCrossing p23₅ = p23 := by rfl

theorem faceStep_iterate_23_1 :
    (faceStep twoThreeRotation twoThreeCrossing)^[1] p23 = p23₁ := by
  rw [Function.iterate_succ_apply']
  exact faceStep_23_0
theorem faceStep_iterate_23_2 :
    (faceStep twoThreeRotation twoThreeCrossing)^[2] p23 = p23₂ := by
  rw [Function.iterate_succ_apply', faceStep_iterate_23_1]
  exact faceStep_23_1
theorem faceStep_iterate_23_3 :
    (faceStep twoThreeRotation twoThreeCrossing)^[3] p23 = p23₃ := by
  rw [Function.iterate_succ_apply', faceStep_iterate_23_2]
  exact faceStep_23_2
theorem faceStep_iterate_23_4 :
    (faceStep twoThreeRotation twoThreeCrossing)^[4] p23 = p23₄ := by
  rw [Function.iterate_succ_apply', faceStep_iterate_23_3]
  exact faceStep_23_3
theorem faceStep_iterate_23_5 :
    (faceStep twoThreeRotation twoThreeCrossing)^[5] p23 = p23₅ := by
  rw [Function.iterate_succ_apply', faceStep_iterate_23_4]
  exact faceStep_23_4
theorem faceStep_iterate_23_6 :
    (faceStep twoThreeRotation twoThreeCrossing)^[6] p23 = p23 := by
  rw [Function.iterate_succ_apply', faceStep_iterate_23_5]
  exact faceStep_23_5

theorem faceStep_not_return_23_1 :
    (faceStep twoThreeRotation twoThreeCrossing)^[1] p23 ≠ p23 := by
  rw [faceStep_iterate_23_1]
  decide
theorem faceStep_not_return_23_2 :
    (faceStep twoThreeRotation twoThreeCrossing)^[2] p23 ≠ p23 := by
  rw [faceStep_iterate_23_2]
  decide
theorem faceStep_not_return_23_3 :
    (faceStep twoThreeRotation twoThreeCrossing)^[3] p23 ≠ p23 := by
  rw [faceStep_iterate_23_3]
  decide
theorem faceStep_not_return_23_4 :
    (faceStep twoThreeRotation twoThreeCrossing)^[4] p23 ≠ p23 := by
  rw [faceStep_iterate_23_4]
  decide
theorem faceStep_not_return_23_5 :
    (faceStep twoThreeRotation twoThreeCrossing)^[5] p23 ≠ p23 := by
  rw [faceStep_iterate_23_5]
  decide

theorem firstFaceReturn_p23 :
    firstFaceReturn twoThreeRotation twoThreeCrossing p23 = 6 := by
  have hle : firstFaceReturn twoThreeRotation twoThreeCrossing p23 ≤ 6 :=
    firstFaceReturn_min twoThreeRotation twoThreeCrossing p23
      ⟨by decide, faceStep_iterate_23_6⟩
  have hnot :
      ∀ n : Nat, 0 < n → n < 6 →
        (faceStep twoThreeRotation twoThreeCrossing)^[n] p23 ≠ p23 := by
    intro n hn hlt hreturn
    have hc : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact faceStep_not_return_23_1 hreturn
    · exact faceStep_not_return_23_2 hreturn
    · exact faceStep_not_return_23_3 hreturn
    · exact faceStep_not_return_23_4 hreturn
    · exact faceStep_not_return_23_5 hreturn
  have hge : 6 ≤ firstFaceReturn twoThreeRotation twoThreeCrossing p23 := by
    by_contra h
    have hlt : firstFaceReturn twoThreeRotation twoThreeCrossing p23 < 6 :=
      Nat.lt_of_not_ge h
    exact hnot _ (firstFaceReturn_spec twoThreeRotation
      twoThreeCrossing p23).1 hlt
      (firstFaceReturn_spec twoThreeRotation twoThreeCrossing p23).2
  exact Nat.le_antisymm hle hge

example : totalPortCount twoThreeNetwork = 6 := by decide
example : p23 ∈ faceOrbit twoThreeRotation twoThreeCrossing p23 :=
  faceOrbit_contains twoThreeRotation twoThreeCrossing p23
example :
    (faceStep twoThreeRotation twoThreeCrossing)^[17] p23 ∈
      faceOrbit twoThreeRotation twoThreeCrossing p23 :=
  faceOrbit_mem_iterate twoThreeRotation twoThreeCrossing p23 17
example : (faceOrbit twoThreeRotation twoThreeCrossing p23).card = 6 := by
  rw [faceOrbit_card, firstFaceReturn_p23]
example : p23₁ ∈ faceOrbit twoThreeRotation twoThreeCrossing p23 :=
  (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing p23 p23₁).2
    ⟨1, faceStep_iterate_23_1⟩
example : p23₂ ∈ faceOrbit twoThreeRotation twoThreeCrossing p23 :=
  (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing p23 p23₂).2
    ⟨2, faceStep_iterate_23_2⟩
example : p23₃ ∈ faceOrbit twoThreeRotation twoThreeCrossing p23 :=
  (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing p23 p23₃).2
    ⟨3, faceStep_iterate_23_3⟩
example : p23₄ ∈ faceOrbit twoThreeRotation twoThreeCrossing p23 :=
  (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing p23 p23₄).2
    ⟨4, faceStep_iterate_23_4⟩
example : p23₅ ∈ faceOrbit twoThreeRotation twoThreeCrossing p23 :=
  (faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing p23 p23₅).2
    ⟨5, faceStep_iterate_23_5⟩
example : faceOrbit twoThreeRotation twoThreeCrossing p23₁ =
    faceOrbit twoThreeRotation twoThreeCrossing p23 :=
  faceOrbit_eq_of_mem twoThreeRotation twoThreeCrossing p23 p23₁
    ((faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
      p23 p23₁).2 ⟨1, faceStep_iterate_23_1⟩)
example :
    ∀ n : Nat, 0 < n → n < 6 →
      (faceStep twoThreeRotation twoThreeCrossing)^[n] p23 ≠ p23 := by
  intro n hn hlt hreturn
  have hc : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact faceStep_not_return_23_1 hreturn
  · exact faceStep_not_return_23_2 hreturn
  · exact faceStep_not_return_23_3 hreturn
  · exact faceStep_not_return_23_4 hreturn
  · exact faceStep_not_return_23_5 hreturn
example :
    firstFaceReturn twoThreeRotation twoThreeCrossing p23₅ =
      firstFaceReturn twoThreeRotation twoThreeCrossing p23 := by
  exact firstFaceReturn_eq_of_mem twoThreeRotation twoThreeCrossing p23 p23₅
    ((faceOrbit_mem_iff_iterate twoThreeRotation twoThreeCrossing
      p23 p23₅).2 ⟨5, faceStep_iterate_23_5⟩)

def bbbbFlow : FlowSignature where
  arity := 4
  label := ![deltaA, deltaA, deltaA, deltaA]
  nonzero := by
    intro i
    fin_cases i <;> exact deltaA_ne_zero
def twoFourNetwork : FlowNetwork where
  regionCount := 2
  signature := fun _ => bbbbFlow
def twoFourCrossing : FlowCrossing twoFourNetwork where
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
def twoFourIdentityRotation : FlowLocalRotation twoFourNetwork where
  rotate := Equiv.refl _
  preservesRegion := by intro p; rfl
def p40 : FlowNetworkPort twoFourNetwork := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
def p40' : FlowNetworkPort twoFourNetwork := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
def p41 : FlowNetworkPort twoFourNetwork := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
def p41' : FlowNetworkPort twoFourNetwork := ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩
theorem faceStep_40 :
    faceStep twoFourIdentityRotation twoFourCrossing p40 = p40' := by rfl
theorem faceStep_41 :
    faceStep twoFourIdentityRotation twoFourCrossing p41 = p41' := by rfl

theorem firstFaceReturn_p41 :
    firstFaceReturn twoFourIdentityRotation twoFourCrossing p41 = 2 := by
  have hreturn :
      (faceStep twoFourIdentityRotation twoFourCrossing)^[2] p41 = p41 := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rfl
  have hle : firstFaceReturn twoFourIdentityRotation twoFourCrossing p41 ≤ 2 :=
    firstFaceReturn_min twoFourIdentityRotation twoFourCrossing p41
      ⟨by decide, hreturn⟩
  have hnot :
      (faceStep twoFourIdentityRotation twoFourCrossing)^[1] p41 ≠ p41 := by
    rw [Function.iterate_succ_apply', Function.iterate_zero_apply, faceStep_41]
    decide
  have hge : 2 ≤ firstFaceReturn twoFourIdentityRotation twoFourCrossing p41 := by
    by_contra h
    have hlt : firstFaceReturn twoFourIdentityRotation twoFourCrossing p41 < 2 :=
      Nat.lt_of_not_ge h
    have hkpos := (firstFaceReturn_spec twoFourIdentityRotation
      twoFourCrossing p41).1
    have hkret := (firstFaceReturn_spec twoFourIdentityRotation
      twoFourCrossing p41).2
    have hkone : firstFaceReturn twoFourIdentityRotation twoFourCrossing p41 = 1 := by
      omega
    rw [hkone] at hkret
    exact hnot hkret
  exact Nat.le_antisymm hle hge

theorem faceOrbit_40_ne_41 :
    faceOrbit twoFourIdentityRotation twoFourCrossing p40 ≠
      faceOrbit twoFourIdentityRotation twoFourCrossing p41 := by
  intro heq
  have hmem : p40 ∈ faceOrbit twoFourIdentityRotation twoFourCrossing p41 := by
    rw [← heq]
    exact faceOrbit_contains twoFourIdentityRotation twoFourCrossing p40
  rcases (faceOrbit_mem_iff_iterate twoFourIdentityRotation twoFourCrossing
    p41 p40).mp hmem with ⟨n, hn⟩
  have hperiod : Function.IsPeriodicPt
      (faceStep twoFourIdentityRotation twoFourCrossing) 2 p41 := by
    change (faceStep twoFourIdentityRotation twoFourCrossing)^[2] p41 = p41
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rfl
  have hmod := hperiod.iterate_mod_apply n
  have hn' := hmod.trans hn
  have hne0 : p41 ≠ p40 := by decide
  have hne1 : p41' ≠ p40 := by decide
  rcases Nat.mod_two_eq_zero_or_one n with hzero | hone
  · apply hne0
    simpa [hzero] using hn'
  · apply hne1
    have hstep : (faceStep twoFourIdentityRotation twoFourCrossing) p41 = p40 := by
      simpa [hone, Function.iterate_succ_apply'] using hn'
    exact faceStep_41.symm.trans hstep

example : Disjoint
    (faceOrbit twoFourIdentityRotation twoFourCrossing p40)
    (faceOrbit twoFourIdentityRotation twoFourCrossing p41) :=
  (faceOrbit_eq_or_disjoint twoFourIdentityRotation twoFourCrossing
    p40 p41).resolve_left faceOrbit_40_ne_41
example :
    faceOrbit twoFourIdentityRotation twoFourCrossing p40 =
      faceOrbit twoFourIdentityRotation twoFourCrossing
        (faceStep twoFourIdentityRotation twoFourCrossing p40) :=
  (faceOrbit_eq_of_mem twoFourIdentityRotation twoFourCrossing p40
    (faceStep twoFourIdentityRotation twoFourCrossing p40)
    (faceOrbit_mem_iterate twoFourIdentityRotation twoFourCrossing p40 1)).symm

#print axioms DkMath.Tromino.faceOrbit_contains
#print axioms DkMath.Tromino.faceOrbit_mem_iterate
#print axioms DkMath.Tromino.faceOrbit_iterate_distinct
#print axioms DkMath.Tromino.faceOrbit_card
#print axioms DkMath.Tromino.faceOrbit_mem_iff_iterate
#print axioms DkMath.Tromino.faceOrbit_eq_of_mem
#print axioms DkMath.Tromino.faceOrbit_eq_or_disjoint
#print axioms DkMath.Tromino.firstFaceReturn_eq_of_mem

end DkMathTest.Tromino.FaceOrbitAxiomAudit
