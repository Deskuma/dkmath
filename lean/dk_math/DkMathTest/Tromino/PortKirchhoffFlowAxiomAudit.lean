/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortKirchhoffFlow
import DkMathTest.Tromino.PortTensionColoringAxiomAudit

#print "file: DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit"

namespace DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortTensionColoringAxiomAudit
open DkMathTest.Tromino.PortCombinatorialMapAxiomAudit
open DkMathTest.Tromino.PortRegionWalkAxiomAudit
open DkMathTest.Tromino.PortRotationSystemAxiomAudit
open DkMathTest.Tromino.RotationSystemAxiomAudit

example {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r =
      ∑ i : Fin (P.arity r), A.label ⟨r, i⟩ :=
  vertexKirchhoffSum_formula A r

example {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r = flowSum (assignmentFlowSignature A r) :=
  vertexKirchhoffSum_eq_flowSum A r

example {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (r : Fin P.regionCount) :
    vertexKirchhoffSum A r = 0 ↔
      flowLabelCount (assignmentFlowSignature A r) deltaA % 2 =
          flowLabelCount (assignmentFlowSignature A r) deltaC % 2 ∧
        flowLabelCount (assignmentFlowSignature A r) deltaB % 2 =
          flowLabelCount (assignmentFlowSignature A r) deltaC % 2 :=
  vertexKirchhoffSum_iff_parity A r

example {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔
      ∀ r, FlowConserved (assignmentFlowSignature A r) :=
  isKirchhoffV4Flow_iff_flowConserved A

example {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsKirchhoffV4Flow A ↔ IsKirchhoffV4Flow A :=
  isKirchhoffV4Flow_ignores_rotation A

def trianglePortNetwork : PortNetwork where
  regionCount := 3
  arity := fun _ => 2

def trianglePort (r i : Nat) (hr : r < 3) (hi : i < 2) :
    PortNetworkPort trianglePortNetwork :=
  ⟨⟨r, by simpa [trianglePortNetwork] using hr⟩,
    ⟨i, by simpa [trianglePortNetwork] using hi⟩⟩

def triangleCross (p : PortNetworkPort trianglePortNetwork) :
    PortNetworkPort trianglePortNetwork :=
  if p.1.val = 0 then
    if p.2.val = 0 then trianglePort 2 1 (by decide) (by decide)
    else trianglePort 1 0 (by decide) (by decide)
  else if p.1.val = 1 then
    if p.2.val = 0 then trianglePort 0 1 (by decide) (by decide)
    else trianglePort 2 0 (by decide) (by decide)
  else
    if p.2.val = 0 then trianglePort 1 1 (by decide) (by decide)
    else trianglePort 0 0 (by decide) (by decide)

def trianglePortCrossing : PortCrossing trianglePortNetwork where
  cross := triangleCross
  involutive := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;>
        simp [triangleCross, trianglePort]
  changesRegion := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;>
        simp [triangleCross, trianglePort, Fin.ext_iff]

def triangleRotate2 (i : Fin 2) : Fin 2 := ⟨1 - i.val, by omega⟩

theorem triangleRotate2_involutive (i : Fin 2) :
    triangleRotate2 (triangleRotate2 i) = i := by
  apply Fin.ext
  dsimp [triangleRotate2]
  omega

def trianglePortRotation : PortLocalRotation trianglePortNetwork where
  rotate :=
    { toFun := fun p => ⟨p.1, triangleRotate2 p.2⟩
      invFun := fun p => ⟨p.1, triangleRotate2 p.2⟩
      left_inv := by
        intro p
        cases p with
        | mk r i =>
          apply Sigma.ext
          · rfl
          · exact heq_of_eq (triangleRotate2_involutive i)
      right_inv := by
        intro p
        cases p with
        | mk r i =>
          apply Sigma.ext
          · rfl
          · exact heq_of_eq (triangleRotate2_involutive i) }
  preservesRegion := by intro p; rfl

def trianglePortRotationSystem : PortRotationSystem trianglePortNetwork where
  toPortLocalRotation := trianglePortRotation
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

def t00 : PortNetworkPort trianglePortNetwork := trianglePort 0 0 (by decide) (by decide)
def t01 : PortNetworkPort trianglePortNetwork := trianglePort 0 1 (by decide) (by decide)
def t10 : PortNetworkPort trianglePortNetwork := trianglePort 1 0 (by decide) (by decide)
def t11 : PortNetworkPort trianglePortNetwork := trianglePort 1 1 (by decide) (by decide)
def t20 : PortNetworkPort trianglePortNetwork := trianglePort 2 0 (by decide) (by decide)
def t21 : PortNetworkPort trianglePortNetwork := trianglePort 2 1 (by decide) (by decide)

theorem triangle_face_t00 : trianglePortCrossing.cross t00 = t21 := by rfl
theorem triangle_face_t01 : trianglePortCrossing.cross t01 = t10 := by rfl
theorem triangle_face_t10 : trianglePortCrossing.cross t10 = t01 := by rfl
theorem triangle_face_t11 : trianglePortCrossing.cross t11 = t20 := by rfl
theorem triangle_face_t20 : trianglePortCrossing.cross t20 = t11 := by rfl
theorem triangle_face_t21 : trianglePortCrossing.cross t21 = t00 := by rfl

theorem triangle_step_t00 :
    portFaceStep trianglePortRotation trianglePortCrossing t00 = t20 := by rfl
theorem triangle_step_t20 :
    portFaceStep trianglePortRotation trianglePortCrossing t20 = t10 := by rfl
theorem triangle_step_t10 :
    portFaceStep trianglePortRotation trianglePortCrossing t10 = t00 := by rfl
theorem triangle_step_t01 :
    portFaceStep trianglePortRotation trianglePortCrossing t01 = t11 := by rfl
theorem triangle_step_t11 :
    portFaceStep trianglePortRotation trianglePortCrossing t11 = t21 := by rfl
theorem triangle_step_t21 :
    portFaceStep trianglePortRotation trianglePortCrossing t21 = t01 := by rfl

example : (portFaceStep trianglePortRotation trianglePortCrossing)^[3] t00 = t00 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [triangle_step_t00, triangle_step_t20, triangle_step_t10]

example : (portFaceStep trianglePortRotation trianglePortCrossing)^[3] t01 = t01 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [triangle_step_t01, triangle_step_t11, triangle_step_t21]

theorem triangle_firstPortFaceReturn_t00 : firstPortFaceReturn trianglePortRotation trianglePortCrossing t00 = 3 := by
  have hreturn : (portFaceStep trianglePortRotation trianglePortCrossing)^[3] t00 = t00 := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [triangle_step_t00, triangle_step_t20, triangle_step_t10]
  have hle := firstPortFaceReturn_min trianglePortRotation trianglePortCrossing t00
    (m := 3) ⟨by decide, hreturn⟩
  have hne1 : (portFaceStep trianglePortRotation trianglePortCrossing)^[1] t00 ≠ t00 := by
    rw [Function.iterate_succ_apply', Function.iterate_zero_apply, triangle_step_t00]
    decide
  have hne2 : (portFaceStep trianglePortRotation trianglePortCrossing)^[2] t00 ≠ t00 := by
    rw [show (portFaceStep trianglePortRotation trianglePortCrossing)^[2] t00 = t10 by
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [triangle_step_t00, triangle_step_t20]]
    decide
  have hge : 3 ≤ firstPortFaceReturn trianglePortRotation trianglePortCrossing t00 := by
    by_contra h
    have hlt : firstPortFaceReturn trianglePortRotation trianglePortCrossing t00 < 3 := Nat.lt_of_not_ge h
    have hpos := (firstPortFaceReturn_spec trianglePortRotation trianglePortCrossing t00).1
    have hret := (firstPortFaceReturn_spec trianglePortRotation trianglePortCrossing t00).2
    have hc : firstPortFaceReturn trianglePortRotation trianglePortCrossing t00 = 1 ∨
        firstPortFaceReturn trianglePortRotation trianglePortCrossing t00 = 2 := by omega
    rcases hc with h1 | h2
    · rw [h1] at hret
      exact hne1 hret
    · rw [h2] at hret
      exact hne2 hret
  exact Nat.le_antisymm hle hge

theorem triangle_firstPortFaceReturn_t01 : firstPortFaceReturn trianglePortRotation trianglePortCrossing t01 = 3 := by
  have hreturn : (portFaceStep trianglePortRotation trianglePortCrossing)^[3] t01 = t01 := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [triangle_step_t01, triangle_step_t11, triangle_step_t21]
  have hle := firstPortFaceReturn_min trianglePortRotation trianglePortCrossing t01 (m := 3) ⟨by decide, hreturn⟩
  have hne1 : (portFaceStep trianglePortRotation trianglePortCrossing)^[1] t01 ≠ t01 := by
    rw [Function.iterate_succ_apply', Function.iterate_zero_apply, triangle_step_t01]
    decide
  have hne2 : (portFaceStep trianglePortRotation trianglePortCrossing)^[2] t01 ≠ t01 := by
    rw [show (portFaceStep trianglePortRotation trianglePortCrossing)^[2] t01 = t21 by
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [triangle_step_t01, triangle_step_t11]]
    intro h
    have hv := congrArg Sigma.fst h
    norm_num [t21, t01, trianglePort] at hv
  have hge : 3 ≤ firstPortFaceReturn trianglePortRotation trianglePortCrossing t01 := by
    by_contra h
    have hlt : firstPortFaceReturn trianglePortRotation trianglePortCrossing t01 < 3 := Nat.lt_of_not_ge h
    have hpos := (firstPortFaceReturn_spec trianglePortRotation trianglePortCrossing t01).1
    have hret := (firstPortFaceReturn_spec trianglePortRotation trianglePortCrossing t01).2
    have hc : firstPortFaceReturn trianglePortRotation trianglePortCrossing t01 = 1 ∨
        firstPortFaceReturn trianglePortRotation trianglePortCrossing t01 = 2 := by omega
    rcases hc with h1 | h2
    · rw [h1] at hret
      exact hne1 hret
    · rw [h2] at hret
      exact hne2 hret
  exact Nat.le_antisymm hle hge

theorem triangle_faceCount : portFaceCount trianglePortRotation trianglePortCrossing = 2 := by
  have h20 : portFaceOrbit trianglePortRotation trianglePortCrossing t20 =
      portFaceOrbit trianglePortRotation trianglePortCrossing t00 := by
    apply portFaceOrbit_eq_of_mem
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨1, triangle_step_t00⟩
  have h10 : portFaceOrbit trianglePortRotation trianglePortCrossing t10 =
      portFaceOrbit trianglePortRotation trianglePortCrossing t00 := by
    apply portFaceOrbit_eq_of_mem
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨2, by simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]; rw [triangle_step_t00, triangle_step_t20]⟩
  have h11 : portFaceOrbit trianglePortRotation trianglePortCrossing t11 =
      portFaceOrbit trianglePortRotation trianglePortCrossing t01 := by
    apply portFaceOrbit_eq_of_mem
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨1, triangle_step_t01⟩
  have h21 : portFaceOrbit trianglePortRotation trianglePortCrossing t21 =
      portFaceOrbit trianglePortRotation trianglePortCrossing t01 := by
    apply portFaceOrbit_eq_of_mem
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨2, by simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]; rw [triangle_step_t01, triangle_step_t11]⟩
  have hfamily : portFaceOrbits trianglePortRotation trianglePortCrossing =
      {portFaceOrbit trianglePortRotation trianglePortCrossing t00,
       portFaceOrbit trianglePortRotation trianglePortCrossing t01} := by
    ext F
    constructor
    · intro h
      rcases (portFaceOrbits_mem_iff trianglePortRotation trianglePortCrossing F).mp h with ⟨p, rfl⟩
      rcases p with ⟨r, i⟩
      fin_cases r <;> fin_cases i
      · exact Finset.mem_insert.mpr (Or.inl rfl)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      · change portFaceOrbit trianglePortRotation trianglePortCrossing t10 ∈ _
        rw [h10]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · change portFaceOrbit trianglePortRotation trianglePortCrossing t11 ∈ _
        rw [h11]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      · change portFaceOrbit trianglePortRotation trianglePortCrossing t20 ∈ _
        rw [h20]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · change portFaceOrbit trianglePortRotation trianglePortCrossing t21 ∈ _
        rw [h21]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact portFaceOrbit_mem_orbits trianglePortRotation trianglePortCrossing t00
      · exact portFaceOrbit_mem_orbits trianglePortRotation trianglePortCrossing t01
  have hne : portFaceOrbit trianglePortRotation trianglePortCrossing t00 ≠
      portFaceOrbit trianglePortRotation trianglePortCrossing t01 := by
    intro h
    have h00 : portFaceOrbit trianglePortRotation trianglePortCrossing t00 = {t00, t20, t10} := by
      rw [portFaceOrbit, triangle_firstPortFaceReturn_t00]
      decide
    have h01 : portFaceOrbit trianglePortRotation trianglePortCrossing t01 = {t01, t11, t21} := by
      rw [portFaceOrbit, triangle_firstPortFaceReturn_t01]
      decide
    rw [h00, h01] at h
    exact (by decide : ({t00, t20, t10} : Finset _) ≠ {t01, t11, t21}) h
  unfold portFaceCount
  rw [hfamily]
  simp [hne]
def trianglePortMap : PortCombinatorialMap trianglePortNetwork where
  crossing := trianglePortCrossing
  rotation := trianglePortRotationSystem
  nonemptyRegions := by decide
  connected := by
    intro r s
    fin_cases r <;> fin_cases s
    · exact ⟨PortRegionWalk.nil trianglePortCrossing _⟩
    · exact ⟨PortRegionWalk.singleton trianglePortCrossing t01⟩
    · exact ⟨PortRegionWalk.singleton trianglePortCrossing t00⟩
    · exact ⟨PortRegionWalk.singleton trianglePortCrossing t10⟩
    · exact ⟨PortRegionWalk.nil trianglePortCrossing _⟩
    · exact ⟨PortRegionWalk.singleton trianglePortCrossing t11⟩
    · exact ⟨PortRegionWalk.singleton trianglePortCrossing t21⟩
    · exact ⟨PortRegionWalk.singleton trianglePortCrossing t20⟩
    · exact ⟨PortRegionWalk.nil trianglePortCrossing _⟩
example : trianglePortMap.vertexCount = 3 := by decide
example : trianglePortMap.edgeCount = 3 := by decide
example : trianglePortMap.portCount = 6 := by decide
example : trianglePortMap.faceCount = 2 := by
  change portFaceCount trianglePortRotation trianglePortCrossing = 2
  exact triangle_faceCount

theorem triangle_eulerCharacteristic : trianglePortMap.eulerCharacteristic = 2 := by
  change portCombinatorialEulerCharacteristic trianglePortRotation trianglePortCrossing = 2
  unfold portCombinatorialEulerCharacteristic
  have he : portCrossingEdgeCount trianglePortCrossing = 3 := by decide
  rw [he, triangle_faceCount]
  norm_num [portRegionVertexCount, trianglePortNetwork]

example : PortHasCombinatorialGenus trianglePortMap 0 := by
  rw [portCombinatorialGenus_zero_iff]
  exact triangle_eulerCharacteristic
example : PortHasSphereCharacteristic trianglePortMap := by
  rw [PortHasSphereCharacteristic]
  exact triangle_eulerCharacteristic

def triangleGenusZero : PortGenusZeroCombinatorialMap trianglePortNetwork where
  map := trianglePortMap
  genusZero := by
    rw [portCombinatorialGenus_zero_iff]
    exact triangle_eulerCharacteristic

def triangleAllDeltaA : V4FlowAssignment trianglePortCrossing where
  label := fun _ => deltaA
  nonzero := by intro; exact deltaA_ne_zero
  cross_sameLabel := by intro; rfl

example : IsKirchhoffV4Flow triangleAllDeltaA := by
  intro r
  fin_cases r <;> decide

def triangleCycle : ClosedRegionWalk triangleAllDeltaA.toFlowCrossing
    ⟨0, by decide⟩ :=
  FlowRegionWalk.append
    (FlowRegionWalk.singleton triangleAllDeltaA.toFlowCrossing
      (t00 : FlowNetworkPort triangleAllDeltaA.toFlowNetwork))
    (FlowRegionWalk.append
      (FlowRegionWalk.singleton triangleAllDeltaA.toFlowCrossing
        (t20 : FlowNetworkPort triangleAllDeltaA.toFlowNetwork))
      (FlowRegionWalk.singleton triangleAllDeltaA.toFlowCrossing
        (t10 : FlowNetworkPort triangleAllDeltaA.toFlowNetwork)))

theorem triangleCycle_xor : regionWalkXor triangleCycle = deltaA := by
  change deltaA + (deltaA + deltaA) = deltaA
  rw [state_add_self, add_zero]

theorem triangleAllDeltaA_not_tension :
    ¬ IsZeroHolonomyV4Tension triangleAllDeltaA := by
  intro hzero
  have h := hzero ⟨0, by decide⟩ triangleCycle
  rw [triangleCycle_xor] at h
  exact deltaA_ne_zero h

theorem triangle_kirchhoff_not_tension :
    IsKirchhoffV4Flow triangleAllDeltaA ∧
      ¬ IsZeroHolonomyV4Tension triangleAllDeltaA := by
  refine ⟨?_, triangleAllDeltaA_not_tension⟩
  intro r
  fin_cases r <;> decide

def portThreeDeltaAAssignment : V4FlowAssignment portThreeCrossing where
  label := fun _ => deltaA
  nonzero := by intro; exact deltaA_ne_zero
  cross_sameLabel := by intro; rfl

theorem portThreeDeltaAAssignment_eq_coloring_assignment :
    portThreeDeltaAAssignment = coloringToV4Assignment portThreeColoring := by
  apply v4Assignment_ext
  intro p
  cases p with
  | mk r i => fin_cases r <;> fin_cases i <;> rfl

theorem portThreeDeltaAAssignment_zeroHolonomy :
    IsZeroHolonomyV4Tension portThreeDeltaAAssignment := by
  rw [portThreeDeltaAAssignment_eq_coloring_assignment]
  exact coloringToV4Assignment_isZeroHolonomy portThreeColoring

theorem portThreeDeltaAAssignment_not_kirchhoff :
    ¬ IsKirchhoffV4Flow portThreeDeltaAAssignment := by
  intro h
  have h0 := h ⟨0, by decide⟩
  have h0' : deltaA = 0 := by
    norm_num [vertexKirchhoffSum, portThreeDeltaAAssignment,
      portThreeNetwork, aaaFlow, state_add_self] at h0 ⊢
    exact h0
  exact deltaA_ne_zero h0'

theorem portThree_tension_not_kirchhoff :
    IsZeroHolonomyV4Tension portThreeDeltaAAssignment ∧
      ¬ IsKirchhoffV4Flow portThreeDeltaAAssignment :=
  ⟨portThreeDeltaAAssignment_zeroHolonomy, portThreeDeltaAAssignment_not_kirchhoff⟩

def balancedThreeLabelAssignment : V4FlowAssignment portThreeCrossing where
  label := fun p => if p.2.val = 0 then deltaA else
    if p.2.val = 1 then deltaB else deltaC
  nonzero := by
    intro p
    cases p with
    | mk r i => fin_cases i <;>
      simp [deltaA_ne_zero, deltaB_ne_zero, deltaC_ne_zero]
  cross_sameLabel := by intro; rfl

theorem balancedThreeLabelAssignment_kirchhoff :
    IsKirchhoffV4Flow balancedThreeLabelAssignment := by
  intro r
  fin_cases r <;> decide

def triangleColoring :
    (portRegionSimpleGraph trianglePortCrossing).Coloring TrominoState :=
  SimpleGraph.Coloring.mk
    (fun r : Fin 3 => if r.val = 0 then 0 else
      if r.val = 1 then deltaA else deltaB) (by
      intro r s h
      fin_cases r <;> fin_cases s <;>
        simp_all [portRegionSimpleGraph_adj_iff, trianglePortCrossing,
          triangleCross, trianglePort, deltaA_ne_zero, deltaB_ne_zero,
          Ne.symm deltaA_ne_zero, Ne.symm deltaB_ne_zero,
          deltaA_ne_deltaB, Ne.symm deltaA_ne_deltaB])

theorem triangleColoring_edge_labels :
    (coloringToV4Assignment triangleColoring).label t01 = deltaA ∧
    (coloringToV4Assignment triangleColoring).label t11 = deltaC ∧
    (coloringToV4Assignment triangleColoring).label t21 = deltaB := by
  constructor
  · change 0 + deltaA = deltaA
    simp
  · constructor
    · change deltaA + deltaB = deltaC
      exact deltaA_add_deltaB
    · change deltaB + 0 = deltaB
      simp

#print axioms DkMath.Tromino.vertexKirchhoffSum_eq_flowSum
#print axioms DkMath.Tromino.IsKirchhoffV4Flow
#print axioms DkMath.Tromino.HasKirchhoffV4Flow
#print axioms DkMath.Tromino.assignmentFlowSignature
#print axioms DkMath.Tromino.vertexKirchhoffSum_iff_parity
#print axioms DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit.triangle_kirchhoff_not_tension

end DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
