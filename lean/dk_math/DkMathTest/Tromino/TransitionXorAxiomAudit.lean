/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.TransitionXor

#print "file: DkMathTest.Tromino.TransitionXorAxiomAudit"

namespace DkMathTest.Tromino.TransitionXorAxiomAudit

open DkMath.Tromino

def contactA : BoundaryContact := { inside := 0, outside := deltaA }

def aaSignature : BoundarySignature where
  arity := 2
  contact := ![contactA, contactA]
  proper := by intro i; fin_cases i <;> decide

def aaSwap (i : Fin 2) : Fin 2 := ⟨1 - i.val, by omega⟩

def canonicalAAPairing : BoundaryPairing aaSignature where
  mate := aaSwap
  involutive := by
    intro i
    apply Fin.ext
    dsimp [aaSwap]
    omega
  sameLabel := by
    intro i
    fin_cases i <;> rfl

theorem canonicalAAPairing_perfect : residualPorts canonicalAAPairing = ∅ := by
  ext i
  fin_cases i <;> simp only [residualPorts, canonicalAAPairing, aaSwap, Finset.notMem_empty,
    iff_false] <;> decide

def twoRegionNetwork : BoundaryNetwork where
  regionCount := 2
  signature := fun _ => aaSignature

def swapRegion (r : Fin 2) : Fin 2 := ⟨1 - r.val, by omega⟩

def twoRegionCrossing : BoundaryCrossing twoRegionNetwork where
  cross := fun p =>
    ⟨swapRegion ⟨p.1.val, by simpa [twoRegionNetwork] using p.1.isLt⟩, p.2⟩
  cross_involutive := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · apply Fin.ext
        dsimp [swapRegion]
        have hr : r.val < 2 := by simpa [twoRegionNetwork] using r.isLt
        omega
      · exact heq_of_eq rfl
  cross_changes_region := by
    intro p h
    have hp : p.1.val < 2 := by simpa [twoRegionNetwork] using p.1.isLt
    have hv := congrArg Fin.val h
    dsimp [swapRegion] at hv
    omega
  cross_sameLabel := by intro p; rfl

def twoRegionClosed : ClosedBoundaryNetwork where
  toBoundaryNetwork := twoRegionNetwork
  crossing := twoRegionCrossing
  pairing := fun _ => canonicalAAPairing
  perfect := by intro r; exact canonicalAAPairing_perfect

def p2 : NetworkPort twoRegionClosed.toBoundaryNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

def p2₁ : NetworkPort twoRegionClosed.toBoundaryNetwork :=
  ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

theorem transitionStep_two_p2 : transitionStep twoRegionClosed p2 = p2₁ := by
  apply Sigma.ext
  · apply Fin.ext
    simp [p2, p2₁, transitionStep, localMatePort, crossPort, twoRegionClosed,
      twoRegionCrossing, twoRegionNetwork, swapRegion, canonicalAAPairing, aaSwap]
  · apply heq_of_eq
    apply Fin.ext
    simp [p2, p2₁, transitionStep, localMatePort, crossPort, twoRegionClosed,
      twoRegionCrossing, twoRegionNetwork, swapRegion, canonicalAAPairing, aaSwap]

theorem transitionStep_two_p2₁ : transitionStep twoRegionClosed p2₁ = p2 := by
  apply Sigma.ext
  · apply Fin.ext
    simp [p2, p2₁, transitionStep, localMatePort, crossPort, twoRegionClosed,
      twoRegionCrossing, twoRegionNetwork, swapRegion, canonicalAAPairing, aaSwap]
  · apply heq_of_eq
    apply Fin.ext
    simp [p2, p2₁, transitionStep, localMatePort, crossPort, twoRegionClosed,
      twoRegionCrossing, twoRegionNetwork, swapRegion, canonicalAAPairing, aaSwap]

theorem transitionStep_two_p2_sq : (transitionStep twoRegionClosed)^[2] p2 = p2 := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [transitionStep_two_p2, transitionStep_two_p2₁]

def threeRegionNetwork : BoundaryNetwork where
  regionCount := 3
  signature := fun _ => aaSignature

def mk3 (r : Nat) (hr : r < 3) (i : Nat) (hi : i < 2) : NetworkPort threeRegionNetwork :=
  ⟨⟨r, by simpa [threeRegionNetwork] using hr⟩,
    ⟨i, by simpa [threeRegionNetwork, aaSignature] using hi⟩⟩

def crossThree (p : NetworkPort threeRegionNetwork) : NetworkPort threeRegionNetwork :=
  if p.1.val = 0 then
    if p.2.val = 0 then mk3 2 (by decide) 1 (by decide) else mk3 1 (by decide) 0 (by decide)
  else if p.1.val = 1 then
    if p.2.val = 0 then mk3 0 (by decide) 1 (by decide) else mk3 2 (by decide) 0 (by decide)
  else
    if p.2.val = 0 then mk3 1 (by decide) 1 (by decide) else mk3 0 (by decide) 0 (by decide)

def threeRegionCrossing : BoundaryCrossing threeRegionNetwork where
  cross := crossThree
  cross_involutive := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;> simp [crossThree, mk3]
  cross_changes_region := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;> simp [crossThree, mk3, Fin.ext_iff]
  cross_sameLabel := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;> rfl

def threeRegionClosed : ClosedBoundaryNetwork where
  toBoundaryNetwork := threeRegionNetwork
  crossing := threeRegionCrossing
  pairing := fun _ => canonicalAAPairing
  perfect := by intro r; exact canonicalAAPairing_perfect

def p3 : NetworkPort threeRegionClosed.toBoundaryNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

def p3₁ : NetworkPort threeRegionClosed.toBoundaryNetwork :=
  ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩

def p3₂ : NetworkPort threeRegionClosed.toBoundaryNetwork :=
  ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

theorem transitionStep_three_p3 : transitionStep threeRegionClosed p3 = p3₁ := by
  apply Sigma.ext
  · apply Fin.ext
    simp [p3, p3₁, transitionStep, localMatePort, crossPort, threeRegionClosed,
      threeRegionCrossing, threeRegionNetwork, crossThree, mk3, canonicalAAPairing, aaSwap]
  · apply heq_of_eq
    apply Fin.ext
    simp [p3, p3₁, transitionStep, localMatePort, crossPort, threeRegionClosed,
      threeRegionCrossing, threeRegionNetwork, crossThree, mk3, canonicalAAPairing, aaSwap]

theorem transitionStep_three_p3₁ : transitionStep threeRegionClosed p3₁ = p3₂ := by
  apply Sigma.ext
  · apply Fin.ext
    simp [    p3₁, p3₂, transitionStep, localMatePort, crossPort, threeRegionClosed,
      threeRegionCrossing, threeRegionNetwork, crossThree, mk3, canonicalAAPairing, aaSwap]
  · apply heq_of_eq
    apply Fin.ext
    simp [    p3₁, p3₂, transitionStep, localMatePort, crossPort, threeRegionClosed,
      threeRegionCrossing, threeRegionNetwork, crossThree, mk3, canonicalAAPairing, aaSwap]

theorem transitionStep_three_p3₂ : transitionStep threeRegionClosed p3₂ = p3 := by
  apply Sigma.ext
  · apply Fin.ext
    simp [p3, p3₂, transitionStep, localMatePort, crossPort, threeRegionClosed,
      threeRegionCrossing, threeRegionNetwork, crossThree, mk3, canonicalAAPairing, aaSwap]
  · apply heq_of_eq
    apply Fin.ext
    simp [p3, p3₂, transitionStep, localMatePort, crossPort, threeRegionClosed,
      threeRegionCrossing, threeRegionNetwork, crossThree, mk3,
      canonicalAAPairing, aaSwap]

theorem transitionStep_three_p3_sq : (transitionStep threeRegionClosed)^[2] p3 = p3₂ := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [transitionStep_three_p3, transitionStep_three_p3₁]

theorem transitionStep_three_p3_cube : (transitionStep threeRegionClosed)^[3] p3 = p3 := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [transitionStep_three_p3, transitionStep_three_p3₁, transitionStep_three_p3₂]

theorem transitionStep_two_p2_ne : transitionStep twoRegionClosed p2 ≠ p2 := by
  rw [transitionStep_two_p2]
  intro h
  have hv' := congrArg Fin.val (congrArg Sigma.fst h)
  norm_num [p2, p2₁] at hv'

theorem transitionStep_three_p3_ne : transitionStep threeRegionClosed p3 ≠ p3 := by
  rw [transitionStep_three_p3]
  intro h
  have hv' := congrArg Fin.val (congrArg Sigma.fst h)
  norm_num [p3, p3₁] at hv'

theorem transitionStep_three_p3_sq_ne : (transitionStep threeRegionClosed)^[2] p3 ≠ p3 := by
  rw [transitionStep_three_p3_sq]
  intro h
  have hv' := congrArg Fin.val (congrArg Sigma.fst h)
  norm_num [p3, p3₂] at hv'

theorem primitive_two : PrimitiveTransitionReturn twoRegionClosed p2 2 := by
  refine ⟨⟨by decide, transitionStep_two_p2_sq⟩, ?_⟩
  intro m hm hmlt hreturn
  have hmone : m = 1 := by omega
  subst m
  exact transitionStep_two_p2_ne hreturn

theorem primitive_three : PrimitiveTransitionReturn threeRegionClosed p3 3 := by
  refine ⟨⟨by decide, transitionStep_three_p3_cube⟩, ?_⟩
  intro m hm hmlt hreturn
  have hm_cases : m = 1 ∨ m = 2 := by omega
  rcases hm_cases with rfl | rfl
  · exact transitionStep_three_p3_ne hreturn
  · exact transitionStep_three_p3_sq_ne hreturn

theorem label_two : boundaryDelta (twoRegionClosed.toBoundaryNetwork.signature p2.1) p2.2 = deltaA := rfl
theorem label_three : boundaryDelta (threeRegionClosed.toBoundaryNetwork.signature p3.1) p3.2 = deltaA := rfl

example : Fintype.card (NetworkPort twoRegionClosed.toBoundaryNetwork) = 4 := by decide
example : Fintype.card (NetworkPort threeRegionClosed.toBoundaryNetwork) = 6 := by decide

example : transitionXor twoRegionClosed p2 2 = 0 := by
  rw [transitionXor_eq_nsmul, label_two, nsmul_state_eq_mod_two]
  decide

example : transitionXor threeRegionClosed p3 3 = deltaA := by
  rw [transitionXor_eq_nsmul, label_three, nsmul_state_eq_mod_two]
  decide

example : transitionXor threeRegionClosed p3 3 ≠ 0 := by
  rw [show transitionXor threeRegionClosed p3 3 = deltaA by
    rw [transitionXor_eq_nsmul, label_three, nsmul_state_eq_mod_two]
    decide]
  exact deltaA_ne_zero

example (base : TrominoState) : transportState base twoRegionClosed p2 2 = base := by
  rw [transportState_return_iff base twoRegionClosed p2 2 primitive_two.1]
  rw [transitionXor_eq_nsmul, label_two, nsmul_state_eq_mod_two]
  decide

example (base : TrominoState) : transportState base threeRegionClosed p3 3 ≠ base := by
  intro h
  have hxor := (transportState_return_iff base threeRegionClosed p3 3 primitive_three.1).mp h
  rw [transitionXor_eq_nsmul, label_three, nsmul_state_eq_mod_two] at hxor
  exact deltaA_ne_zero hxor

example : PrimitiveCycleCompatible twoRegionClosed p2 2 := by
  exact (primitiveCycleCompatible_iff_even twoRegionClosed p2 2 primitive_two).mpr (by decide)

example : ¬ PrimitiveCycleCompatible threeRegionClosed p3 3 := by
  intro h
  have heven := (primitiveCycleCompatible_iff_even threeRegionClosed p3 3 primitive_three).mp h
  omega

#print axioms DkMath.Tromino.transitionXor_eq_nsmul
#print axioms DkMath.Tromino.nsmul_state_eq_zero_iff
#print axioms DkMath.Tromino.firstTransitionReturn_primitive
#print axioms DkMath.Tromino.primitiveCycleXor_iff_even
#print axioms DkMath.Tromino.transportState_add

end DkMathTest.Tromino.TransitionXorAxiomAudit
