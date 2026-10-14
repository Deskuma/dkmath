/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FlowTransitionXor

#print "file: DkMathTest.Tromino.FlowTransitionXorAxiomAudit"

namespace DkMathTest.Tromino.FlowTransitionXorAxiomAudit

open DkMath.Tromino

def aaFlow : FlowSignature where
  arity := 2
  label := ![deltaA, deltaA]
  nonzero := by
    intro i
    fin_cases i <;> exact deltaA_ne_zero

theorem aaMate_zero : canonicalFlowMate aaFlow ⟨0, by decide⟩ = ⟨1, by decide⟩ := by
  have hempty : flowResidualPorts (canonicalFlowPairing aaFlow) = ∅ := by
    apply canonicalFlowPairing_even_perfect
    all_goals decide
  have hready := canonicalFlowPairing_transition_ready aaFlow
    ⟨0, by decide⟩ (by rw [hempty]; simp)
  apply Fin.ext
  change (canonicalFlowMate aaFlow ⟨0, by decide⟩).val = 1
  have hne : canonicalFlowMate aaFlow ⟨0, by decide⟩ ≠
      (⟨0, by decide⟩ : Fin aaFlow.arity) := hready.1
  have hneval : (canonicalFlowMate aaFlow ⟨0, by decide⟩).val ≠ 0 := by
    intro h
    apply hne
    apply Fin.ext
    exact h
  have hlt : (canonicalFlowMate aaFlow ⟨0, by decide⟩).val < 2 := by
    simpa [aaFlow] using (canonicalFlowMate aaFlow ⟨0, by decide⟩).isLt
  omega

theorem aaMate_one : canonicalFlowMate aaFlow ⟨1, by decide⟩ = ⟨0, by decide⟩ := by
  have h := canonicalFlowMate_involutive aaFlow ⟨0, by decide⟩
  rw [aaMate_zero] at h
  exact h

def twoRegionFlowNetwork : FlowNetwork where
  regionCount := 2
  signature := fun _ => aaFlow

def swapRegion (r : Fin 2) : Fin 2 := ⟨1 - r.val, by omega⟩

theorem swapRegion_involutive (r : Fin 2) :
    swapRegion (swapRegion r) = r := by
  apply Fin.ext
  dsimp [swapRegion]
  omega

theorem swapRegion_ne (r : Fin 2) : swapRegion r ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [swapRegion] at hv
  omega

def twoRegionFlowCrossing : FlowCrossing twoRegionFlowNetwork where
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

def twoRegionFlowClosed : ClosedFlowNetwork where
  toFlowNetwork := twoRegionFlowNetwork
  crossing := twoRegionFlowCrossing
  pairing := fun _ => canonicalFlowPairing aaFlow
  perfect := by
    intro r
    change flowResidualPorts (canonicalFlowPairing aaFlow) = ∅
    apply canonicalFlowPairing_even_perfect
    all_goals decide

def p2 : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

def p2₁ : FlowNetworkPort twoRegionFlowClosed.toFlowNetwork :=
  ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

theorem flowTransitionStep_two_p2 :
    flowTransitionStep twoRegionFlowClosed p2 = p2₁ := by
  apply Sigma.ext
  · apply Fin.ext
    simp [p2, p2₁, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      twoRegionFlowClosed, twoRegionFlowCrossing, twoRegionFlowNetwork,
      swapRegion, canonicalFlowPairing_mate, aaMate_zero]
  · apply heq_of_eq
    apply Fin.ext
    simp [p2, p2₁, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      twoRegionFlowClosed, twoRegionFlowCrossing, twoRegionFlowNetwork,
      swapRegion, canonicalFlowPairing_mate, aaMate_zero]

theorem flowTransitionStep_two_p2₁ :
    flowTransitionStep twoRegionFlowClosed p2₁ = p2 := by
  apply Sigma.ext
  · apply Fin.ext
    simp [p2, p2₁, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      twoRegionFlowClosed, twoRegionFlowCrossing, twoRegionFlowNetwork,
      swapRegion, canonicalFlowPairing_mate, aaMate_one]
  · apply heq_of_eq
    apply Fin.ext
    simp [p2, p2₁, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      twoRegionFlowClosed, twoRegionFlowCrossing, twoRegionFlowNetwork,
      swapRegion, canonicalFlowPairing_mate, aaMate_one]

theorem flowTransitionStep_two_p2_sq :
    (flowTransitionStep twoRegionFlowClosed)^[2] p2 = p2 := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [flowTransitionStep_two_p2, flowTransitionStep_two_p2₁]

theorem flowTransitionStep_two_p2_ne :
    flowTransitionStep twoRegionFlowClosed p2 ≠ p2 := by
  rw [flowTransitionStep_two_p2]
  intro h
  have hv := congrArg Fin.val (congrArg Sigma.fst h)
  norm_num [p2, p2₁] at hv

theorem flowPrimitive_two :
    FlowPrimitiveTransitionReturn twoRegionFlowClosed p2 2 := by
  refine ⟨⟨by decide, flowTransitionStep_two_p2_sq⟩, ?_⟩
  intro m hm hmlt hreturn
  have hmone : m = 1 := by omega
  subst m
  exact flowTransitionStep_two_p2_ne hreturn

example : firstFlowTransitionReturn twoRegionFlowClosed p2 = 2 := by
  have hmin := firstFlowTransitionReturn_min twoRegionFlowClosed p2
    flowPrimitive_two.1
  have hspec := firstFlowTransitionReturn_spec twoRegionFlowClosed p2
  have hpos := hspec.1
  have hne : firstFlowTransitionReturn twoRegionFlowClosed p2 ≠ 1 := by
    intro h
    have hreturn := hspec.2
    rw [h] at hreturn
    exact flowTransitionStep_two_p2_ne hreturn
  omega

example (N : ClosedFlowNetwork) (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) :
    flowTransitionXor N p n =
      n • (N.toFlowNetwork.signature p.1).label p.2 :=
  flowTransitionXor_eq_nsmul N p n

example (N : ClosedFlowNetwork) (p : FlowNetworkPort N.toFlowNetwork) (n : Nat) :
    flowTransitionXor N p n = 0 ↔ n % 2 = 0 :=
  flowTransitionXor_nonzero_iff_even N p n

example : flowTransitionXor twoRegionFlowClosed p2 2 = 0 := by
  rw [flowTransitionXor_eq_nsmul]
  change 2 • deltaA = 0
  rw [nsmul_state_eq_mod_two]
  decide

example (base : TrominoState) :
    flowTransportState base twoRegionFlowClosed p2 2 = base := by
  rw [flowTransportState_return_iff base twoRegionFlowClosed p2 2 flowPrimitive_two.1]
  exact (flowTransitionXor_nonzero_iff_even twoRegionFlowClosed p2 2).mpr (by decide)

example : FlowPrimitiveCycleCompatible twoRegionFlowClosed p2 2 := by
  exact (flowPrimitiveCycleCompatible_iff_even twoRegionFlowClosed p2 2
    flowPrimitive_two).mpr (by decide)

def threeRegionFlowNetwork : FlowNetwork where
  regionCount := 3
  signature := fun _ => aaFlow

def mk3 (r : Nat) (hr : r < 3) (i : Nat) (hi : i < 2) :
    FlowNetworkPort threeRegionFlowNetwork :=
  ⟨⟨r, by simpa [threeRegionFlowNetwork] using hr⟩,
    ⟨i, by simpa [threeRegionFlowNetwork, aaFlow] using hi⟩⟩

def crossThree (p : FlowNetworkPort threeRegionFlowNetwork) :
    FlowNetworkPort threeRegionFlowNetwork :=
  if p.1.val = 0 then
    if p.2.val = 0 then mk3 2 (by decide) 1 (by decide)
    else mk3 1 (by decide) 0 (by decide)
  else if p.1.val = 1 then
    if p.2.val = 0 then mk3 0 (by decide) 1 (by decide)
    else mk3 2 (by decide) 0 (by decide)
  else
    if p.2.val = 0 then mk3 1 (by decide) 1 (by decide)
    else mk3 0 (by decide) 0 (by decide)

def threeRegionFlowCrossing : FlowCrossing threeRegionFlowNetwork where
  cross := crossThree
  involutive := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;> simp [crossThree, mk3]
  changesRegion := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;> simp [crossThree, mk3, Fin.ext_iff]
  sameLabel := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;> rfl

def threeRegionFlowClosed : ClosedFlowNetwork where
  toFlowNetwork := threeRegionFlowNetwork
  crossing := threeRegionFlowCrossing
  pairing := fun _ => canonicalFlowPairing aaFlow
  perfect := by
    intro r
    change flowResidualPorts (canonicalFlowPairing aaFlow) = ∅
    apply canonicalFlowPairing_even_perfect
    all_goals decide

def p3 : FlowNetworkPort threeRegionFlowClosed.toFlowNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

def p3₁ : FlowNetworkPort threeRegionFlowClosed.toFlowNetwork :=
  ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩

def p3₂ : FlowNetworkPort threeRegionFlowClosed.toFlowNetwork :=
  ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

theorem flowTransitionStep_three_p3 :
    flowTransitionStep threeRegionFlowClosed p3 = p3₁ := by
  apply Sigma.ext
  · apply Fin.ext
    simp [p3, p3₁, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      threeRegionFlowClosed, threeRegionFlowCrossing, threeRegionFlowNetwork,
      crossThree, mk3, canonicalFlowPairing_mate, aaMate_one]
  · apply heq_of_eq
    apply Fin.ext
    simp [p3, p3₁, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      threeRegionFlowClosed, threeRegionFlowCrossing, threeRegionFlowNetwork,
      crossThree, mk3, canonicalFlowPairing_mate, aaMate_one]

theorem flowTransitionStep_three_p3₁ :
    flowTransitionStep threeRegionFlowClosed p3₁ = p3₂ := by
  apply Sigma.ext
  · apply Fin.ext
    simp [p3₁, p3₂, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      threeRegionFlowClosed, threeRegionFlowCrossing, threeRegionFlowNetwork,
      crossThree, mk3, canonicalFlowPairing_mate, aaMate_one]
  · apply heq_of_eq
    apply Fin.ext
    simp [p3₁, p3₂, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      threeRegionFlowClosed, threeRegionFlowCrossing, threeRegionFlowNetwork,
      crossThree, mk3, canonicalFlowPairing_mate, aaMate_one]

theorem flowTransitionStep_three_p3₂ :
    flowTransitionStep threeRegionFlowClosed p3₂ = p3 := by
  apply Sigma.ext
  · apply Fin.ext
    simp [p3, p3₂, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      threeRegionFlowClosed, threeRegionFlowCrossing, threeRegionFlowNetwork,
      crossThree, mk3, canonicalFlowPairing_mate, aaMate_one]
  · apply heq_of_eq
    apply Fin.ext
    simp [p3, p3₂, flowTransitionStep, flowLocalMatePort, flowCrossPort,
      threeRegionFlowClosed, threeRegionFlowCrossing, threeRegionFlowNetwork,
      crossThree, mk3, canonicalFlowPairing_mate, aaMate_one]

theorem flowTransitionStep_three_p3_sq :
    (flowTransitionStep threeRegionFlowClosed)^[2] p3 = p3₂ := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [flowTransitionStep_three_p3, flowTransitionStep_three_p3₁]

theorem flowTransitionStep_three_p3_cube :
    (flowTransitionStep threeRegionFlowClosed)^[3] p3 = p3 := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [flowTransitionStep_three_p3, flowTransitionStep_three_p3₁,
    flowTransitionStep_three_p3₂]

theorem flowTransitionStep_three_p3_ne :
    flowTransitionStep threeRegionFlowClosed p3 ≠ p3 := by
  rw [flowTransitionStep_three_p3]
  intro h
  have hv := congrArg Fin.val (congrArg Sigma.fst h)
  norm_num [p3, p3₁] at hv

theorem flowTransitionStep_three_p3_sq_ne :
    (flowTransitionStep threeRegionFlowClosed)^[2] p3 ≠ p3 := by
  rw [flowTransitionStep_three_p3_sq]
  intro h
  have hv := congrArg Fin.val (congrArg Sigma.fst h)
  norm_num [p3, p3₂] at hv

theorem flowPrimitive_three :
    FlowPrimitiveTransitionReturn threeRegionFlowClosed p3 3 := by
  refine ⟨⟨by decide, flowTransitionStep_three_p3_cube⟩, ?_⟩
  intro m hm hmlt hreturn
  have hm_cases : m = 1 ∨ m = 2 := by omega
  rcases hm_cases with rfl | rfl
  · exact flowTransitionStep_three_p3_ne hreturn
  · exact flowTransitionStep_three_p3_sq_ne hreturn

example : firstFlowTransitionReturn threeRegionFlowClosed p3 = 3 := by
  have hmin := firstFlowTransitionReturn_min threeRegionFlowClosed p3
    flowPrimitive_three.1
  have hspec := firstFlowTransitionReturn_spec threeRegionFlowClosed p3
  have hpos := hspec.1
  have hne1 : firstFlowTransitionReturn threeRegionFlowClosed p3 ≠ 1 := by
    intro h
    have hreturn := hspec.2
    rw [h] at hreturn
    exact flowTransitionStep_three_p3_ne hreturn
  have hne2 : firstFlowTransitionReturn threeRegionFlowClosed p3 ≠ 2 := by
    intro h
    have hreturn := hspec.2
    rw [h] at hreturn
    exact flowTransitionStep_three_p3_sq_ne hreturn
  omega

example : flowTransitionXor threeRegionFlowClosed p3 3 = deltaA := by
  rw [flowTransitionXor_eq_nsmul]
  change 3 • deltaA = deltaA
  rw [nsmul_state_eq_mod_two]
  decide

example : flowTransitionXor threeRegionFlowClosed p3 3 ≠ 0 := by
  rw [show flowTransitionXor threeRegionFlowClosed p3 3 = deltaA by
    rw [flowTransitionXor_eq_nsmul]
    change 3 • deltaA = deltaA
    rw [nsmul_state_eq_mod_two]
    decide]
  exact deltaA_ne_zero

example (base : TrominoState) :
    flowTransportState base threeRegionFlowClosed p3 3 ≠ base := by
  intro h
  have hxor := (flowTransportState_return_iff base threeRegionFlowClosed p3 3
    flowPrimitive_three.1).mp h
  have hparity := (flowTransitionXor_nonzero_iff_even
    threeRegionFlowClosed p3 3).mp hxor
  norm_num at hparity

example : FlowPrimitiveCycleCompatible threeRegionFlowClosed p3 3 ↔
    3 % 2 = 0 :=
  flowPrimitiveCycleCompatible_iff_even threeRegionFlowClosed p3 3 flowPrimitive_three

def contactA : BoundaryContact := { inside := 0, outside := deltaA }

def aaSignature : BoundarySignature where
  arity := 2
  contact := ![contactA, contactA]
  proper := by intro i; fin_cases i <;> decide

def twoRegionNetwork : BoundaryNetwork where
  regionCount := 2
  signature := fun _ => aaSignature

def twoRegionCrossing : BoundaryCrossing twoRegionNetwork where
  cross := fun p => ⟨swapRegion p.1, p.2⟩
  cross_involutive := by
    intro p
    apply Sigma.ext
    · exact swapRegion_involutive p.1
    · exact heq_of_eq rfl
  cross_changes_region := by
    intro p
    exact swapRegion_ne p.1
  cross_sameLabel := by
    intro p
    rfl

def twoRegionClosed : ClosedBoundaryNetwork where
  toBoundaryNetwork := twoRegionNetwork
  crossing := twoRegionCrossing
  pairing := fun _ => canonicalBoundaryPairing aaSignature
  perfect := by
    intro r
    change residualPorts (canonicalBoundaryPairing aaSignature) = ∅
    apply canonicalBoundaryPairing_even_perfect
    all_goals decide

def bp2 : NetworkPort twoRegionClosed.toBoundaryNetwork :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

example (n : Nat) :
    flowTransitionXor twoRegionClosed.toClosedFlowNetwork bp2 n =
      transitionXor twoRegionClosed bp2 n :=
  flowTransitionXor_toClosedFlowNetwork twoRegionClosed bp2 n

example (base : TrominoState) (n : Nat) :
    flowTransportState base twoRegionClosed.toClosedFlowNetwork bp2 n =
      transportState base twoRegionClosed bp2 n :=
  flowTransportState_toClosedFlowNetwork base twoRegionClosed bp2 n

example (n : Nat) :
    FlowTransitionReturn twoRegionClosed.toClosedFlowNetwork bp2 n ↔
      TransitionReturn twoRegionClosed bp2 n :=
  flowTransitionReturn_toClosedFlowNetwork twoRegionClosed bp2 n

example (n : Nat) :
    FlowPrimitiveTransitionReturn twoRegionClosed.toClosedFlowNetwork bp2 n ↔
      PrimitiveTransitionReturn twoRegionClosed bp2 n :=
  flowPrimitiveTransitionReturn_toClosedFlowNetwork twoRegionClosed bp2 n

example (n : Nat) :
    FlowPrimitiveCycleCompatible twoRegionClosed.toClosedFlowNetwork bp2 n ↔
      PrimitiveCycleCompatible twoRegionClosed bp2 n :=
  flowPrimitiveCycleCompatible_toClosedFlowNetwork twoRegionClosed bp2 n

example :
    firstFlowTransitionReturn twoRegionClosed.toClosedFlowNetwork bp2 =
      firstTransitionReturn twoRegionClosed bp2 :=
  firstFlowTransitionReturn_toClosedFlowNetwork twoRegionClosed bp2

#print axioms DkMath.Tromino.flowTransitionXor_eq_nsmul
#print axioms DkMath.Tromino.flowTransitionXor_nonzero_iff_even
#print axioms DkMath.Tromino.flowTransitionXor_add
#print axioms DkMath.Tromino.firstFlowTransitionReturn_primitive
#print axioms DkMath.Tromino.flowPrimitiveCycleCompatible_iff_even
#print axioms DkMath.Tromino.flowTransportState_add
#print axioms DkMath.Tromino.flowTransitionXor_toClosedFlowNetwork
#print axioms DkMath.Tromino.flowTransportState_toClosedFlowNetwork

end DkMathTest.Tromino.FlowTransitionXorAxiomAudit
