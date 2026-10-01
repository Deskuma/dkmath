/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortDualityKernel
import DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
import DkMathTest.Tromino.PortCombinatorialMapAxiomAudit

#print "file: DkMathTest.Tromino.PortDualityKernelAxiomAudit"

namespace DkMathTest.Tromino.PortDualityKernelAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
open DkMathTest.Tromino.PortCombinatorialMapAxiomAudit
open DkMathTest.Tromino.PortEulerCountAxiomAudit
open DkMathTest.Tromino.PortRotationSystemAxiomAudit

example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (p : PortNetworkPort P) : dualRotationEquiv R C p = portFaceStep R C p := rfl
example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (p : PortNetworkPort P) : dualFaceStepRaw R C p = R.rotate p :=
  dualFaceStepRaw_eq_rotation R C p
example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (p : PortNetworkPort P) (n : Nat) :
    (dualFaceStepRaw R C)^[n] p = (R.rotate^[n]) p :=
  dualFaceStepRaw_iterate R C n p
example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (p q : PortNetworkPort P) :
    SameDualVertex R C p q ↔ ∃ n, (dualRotationStep R C)^[n] p = q :=
  sameDualVertex_iff_dualRotation_iterate R C p q
example {P : PortNetwork} (R : PortRotationSystem P) (C : PortCrossing P)
    (p q : PortNetworkPort P) :
    SameDualFace R C p q ↔
      ∃ n, (dualFaceStepRaw R.toPortLocalRotation C)^[n] p = q :=
  sameDualFace_iff_dualFace_iterate R C p q
example {P : PortNetwork} (M : PortCombinatorialMap P) :
    dualVertexCount M = M.faceCount ∧ dualEdgeCount M = M.edgeCount ∧
      dualFaceCount M = M.vertexCount ∧ dualPortCount M = M.portCount :=
  ⟨rfl, rfl, rfl, rfl⟩
example {P : PortNetwork} (M : PortCombinatorialMap P) :
    dualEulerCharacteristic M = M.eulerCharacteristic := dualEulerCharacteristic_eq M
example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (p : PortNetworkPort P) :
    (portFaceBoundaryWalk R C p).length = firstPortFaceReturn R C p :=
  portFaceBoundaryWalk_length R C p
example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (p : PortNetworkPort P) :
    (portFaceBoundaryWalk R C p).edges.toFinset = portFaceOrbit R C p :=
  portFaceBoundaryWalk_edges_toFinset R C p
example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (p q : PortNetworkPort P) (hq : q ∈ (portFaceBoundaryWalk R C p).edges) :
    q ∈ portFaceOrbit R C p := portFaceBoundaryWalk_mem_faceOrbit R C p q hq
example {P : PortNetwork} {C : PortCrossing P} (A : V4FlowAssignment C)
    (R : PortLocalRotation P) (p : PortNetworkPort P)
    (h : IsZeroHolonomyV4Tension A) : faceBoundaryLabelSum A R p = 0 := by
  exact tension_implies_dualFaceKirchhoff A R h p
example {P : PortNetwork} {C : PortCrossing P} (R : PortLocalRotation P)
    (p : PortNetworkPort P) :
    IsDualLoopPort R C p ↔ IsDualLoopPort R C (C.cross p) :=
  isDualLoopPort_cross_iff R C p


def triangleFaceOrbitA : Finset (PortNetworkPort trianglePortNetwork) := {t00, t20, t10}
def triangleFaceOrbitB : Finset (PortNetworkPort trianglePortNetwork) := {t01, t11, t21}

theorem triangle_faceOrbit_t00 :
    portFaceOrbit trianglePortRotation trianglePortCrossing t00 = triangleFaceOrbitA := by
  rw [triangleFaceOrbitA, portFaceOrbit, triangle_firstPortFaceReturn_t00]
  decide
theorem triangle_faceOrbit_t01 :
    portFaceOrbit trianglePortRotation trianglePortCrossing t01 = triangleFaceOrbitB := by
  rw [triangleFaceOrbitB, portFaceOrbit, triangle_firstPortFaceReturn_t01]
  decide
theorem triangle_faceOrbit_t20 :
    portFaceOrbit trianglePortRotation trianglePortCrossing t20 = triangleFaceOrbitA := by
  have h : portFaceOrbit trianglePortRotation trianglePortCrossing t20 =
      portFaceOrbit trianglePortRotation trianglePortCrossing t00 := by
    apply portFaceOrbit_eq_of_mem trianglePortRotation trianglePortCrossing t00 t20
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨1, triangle_step_t00⟩
  rw [h]
  simpa [triangleFaceOrbitA] using triangle_faceOrbit_t00
theorem triangle_faceOrbit_t10 :
    portFaceOrbit trianglePortRotation trianglePortCrossing t10 = triangleFaceOrbitA := by
  have h : portFaceOrbit trianglePortRotation trianglePortCrossing t10 =
      portFaceOrbit trianglePortRotation trianglePortCrossing t00 := by
    apply portFaceOrbit_eq_of_mem trianglePortRotation trianglePortCrossing t00 t10
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨2, by
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [triangle_step_t00, triangle_step_t20]
    ⟩
  rw [h]
  simpa [triangleFaceOrbitA] using triangle_faceOrbit_t00
theorem triangle_faceOrbit_t11 :
    portFaceOrbit trianglePortRotation trianglePortCrossing t11 = triangleFaceOrbitB := by
  have h : portFaceOrbit trianglePortRotation trianglePortCrossing t11 =
      portFaceOrbit trianglePortRotation trianglePortCrossing t01 := by
    apply portFaceOrbit_eq_of_mem trianglePortRotation trianglePortCrossing t01 t11
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨1, triangle_step_t01⟩
  rw [h]
  simpa [triangleFaceOrbitB] using triangle_faceOrbit_t01
theorem triangle_faceOrbit_t21 :
    portFaceOrbit trianglePortRotation trianglePortCrossing t21 = triangleFaceOrbitB := by
  have h : portFaceOrbit trianglePortRotation trianglePortCrossing t21 =
      portFaceOrbit trianglePortRotation trianglePortCrossing t01 := by
    apply portFaceOrbit_eq_of_mem trianglePortRotation trianglePortCrossing t01 t21
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨2, by
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [triangle_step_t01, triangle_step_t11]
    ⟩
  rw [h]
  simpa [triangleFaceOrbitB] using triangle_faceOrbit_t01

theorem triangle_dualLoopFree :
    DualLoopFree trianglePortRotation trianglePortCrossing := by
  intro p
  rcases p with ⟨r, i⟩
  fin_cases r <;> fin_cases i
  · intro h
    change SamePortFaceOrbit trianglePortRotation trianglePortCrossing t00 t21 at h
    unfold SamePortFaceOrbit at h
    rw [triangle_faceOrbit_t00] at h
    exact (by decide : ¬ (t21 ∈ triangleFaceOrbitA)) h
  · intro h
    change SamePortFaceOrbit trianglePortRotation trianglePortCrossing t01 t10 at h
    unfold SamePortFaceOrbit at h
    rw [triangle_faceOrbit_t01] at h
    exact (by decide : ¬ (t10 ∈ triangleFaceOrbitB)) h
  · intro h
    change SamePortFaceOrbit trianglePortRotation trianglePortCrossing t10 t01 at h
    unfold SamePortFaceOrbit at h
    rw [triangle_faceOrbit_t10] at h
    exact (by decide : ¬ (t01 ∈ triangleFaceOrbitA)) h
  · intro h
    change SamePortFaceOrbit trianglePortRotation trianglePortCrossing t11 t20 at h
    unfold SamePortFaceOrbit at h
    rw [triangle_faceOrbit_t11] at h
    exact (by decide : ¬ (t20 ∈ triangleFaceOrbitB)) h
  · intro h
    change SamePortFaceOrbit trianglePortRotation trianglePortCrossing t20 t11 at h
    unfold SamePortFaceOrbit at h
    rw [triangle_faceOrbit_t20] at h
    exact (by decide : ¬ (t11 ∈ triangleFaceOrbitA)) h
  · intro h
    change SamePortFaceOrbit trianglePortRotation trianglePortCrossing t21 t00 at h
    unfold SamePortFaceOrbit at h
    rw [triangle_faceOrbit_t21] at h
    exact (by decide : ¬ (t00 ∈ triangleFaceOrbitB)) h

def triangleDualNetwork : PortNetwork where
  regionCount := 2
  arity := fun _ => 3

def triangleDualFlip3 (i : Fin 3) : Fin 3 :=
  if i.val = 0 then ⟨2, by decide⟩ else
    if i.val = 1 then ⟨1, by decide⟩ else ⟨0, by omega⟩
theorem triangleDualFlip3_involutive (i : Fin 3) :
    triangleDualFlip3 (triangleDualFlip3 i) = i := by fin_cases i <;> rfl

def triangleDualCross : PortNetworkPort triangleDualNetwork →
    PortNetworkPort triangleDualNetwork := fun p =>
  ⟨portSwap2 p.1, triangleDualFlip3 p.2⟩
def triangleDualCrossing : PortCrossing triangleDualNetwork where
  cross := triangleDualCross
  involutive := by
    intro p
    cases p with
    | mk r i =>
      apply Sigma.ext
      · exact portSwap2_involutive r
      · exact heq_of_eq (triangleDualFlip3_involutive i)
  changesRegion := by intro p; exact portSwap2_ne p.1

def triangleDualRotateEquiv :
    PortNetworkPort triangleDualNetwork ≃ PortNetworkPort triangleDualNetwork where
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

def triangleDualRotation : PortLocalRotation triangleDualNetwork where
  rotate := triangleDualRotateEquiv
  preservesRegion := by intro p; rfl
theorem triangleDualRotation_iterate (r : Fin 2) (i : Fin 3) (n : Nat) :
    (triangleDualRotation.rotate^[n]) ⟨r, i⟩ = ⟨r, (portRotate3^[n]) i⟩ := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (triangleDualRotation.rotate^[n]) ⟨r, portRotate3 i⟩ =
        ⟨r, (portRotate3^[n]) (portRotate3 i)⟩
      exact ih (portRotate3 i)

def triangleDualRotationSystem : PortRotationSystem triangleDualNetwork where
  toPortLocalRotation := triangleDualRotation
  cyclic := by
    intro r i j
    -- change ∃ n : Nat, (triangleDualRotation.rotate^[n]) ⟨r, i⟩ = ⟨r, j⟩
    obtain ⟨n, hn⟩ := portRotate3_iterate i j
    refine ⟨n, ?_⟩
    have hiter := triangleDualRotation_iterate r i n
    simpa [hn] using hiter

def d00 : PortNetworkPort triangleDualNetwork := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

def d01 : PortNetworkPort triangleDualNetwork := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
def d02 : PortNetworkPort triangleDualNetwork := ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩
def d10 : PortNetworkPort triangleDualNetwork := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
def d11 : PortNetworkPort triangleDualNetwork := ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩
def d12 : PortNetworkPort triangleDualNetwork := ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩

theorem triangleDual_step_d00 : portFaceStep triangleDualRotation triangleDualCrossing d00 = d10 := by
  change (⟨(1 : Fin 2), portRotate3 (triangleDualFlip3 (0 : Fin 3))⟩ : PortNetworkPort triangleDualNetwork) = d10
  decide
theorem triangleDual_step_d10 : portFaceStep triangleDualRotation triangleDualCrossing d10 = d00 := by
  change (⟨(0 : Fin 2), portRotate3 (triangleDualFlip3 (0 : Fin 3))⟩ : PortNetworkPort triangleDualNetwork) = d00
  decide
theorem triangleDual_step_d01 : portFaceStep triangleDualRotation triangleDualCrossing d01 = d12 := by
  change (⟨(1 : Fin 2), portRotate3 (triangleDualFlip3 (1 : Fin 3))⟩ : PortNetworkPort triangleDualNetwork) = d12
  decide
theorem triangleDual_step_d12 : portFaceStep triangleDualRotation triangleDualCrossing d12 = d01 := by
  change (⟨(0 : Fin 2), portRotate3 (triangleDualFlip3 (2 : Fin 3))⟩ : PortNetworkPort triangleDualNetwork) = d01
  decide
theorem triangleDual_step_d02 : portFaceStep triangleDualRotation triangleDualCrossing d02 = d11 := by
  unfold portFaceStep triangleDualRotation triangleDualRotateEquiv triangleDualCrossing triangleDualCross d02 d11
  decide
theorem triangleDual_step_d11 : portFaceStep triangleDualRotation triangleDualCrossing d11 = d02 := by
  unfold portFaceStep triangleDualRotation triangleDualRotateEquiv triangleDualCrossing triangleDualCross d11 d02
  decide

theorem triangleDual_firstReturn (d e _f : PortNetworkPort triangleDualNetwork)
    (hde : portFaceStep triangleDualRotation triangleDualCrossing d = e)
    (hef : portFaceStep triangleDualRotation triangleDualCrossing e = d)
    (hneq : e ≠ d) :
    firstPortFaceReturn triangleDualRotation triangleDualCrossing d = 2 := by
  have hle := firstPortFaceReturn_min triangleDualRotation triangleDualCrossing d
    (m := 2) ⟨by decide, by
      change (portFaceStep triangleDualRotation triangleDualCrossing)^[2] d = d
      simp [Function.iterate_succ_apply', hde, hef]
    ⟩
  have hge : 2 ≤ firstPortFaceReturn triangleDualRotation triangleDualCrossing d := by
    by_contra h
    have hp := (firstPortFaceReturn_spec triangleDualRotation triangleDualCrossing d).1
    have hr := (firstPortFaceReturn_spec triangleDualRotation triangleDualCrossing d).2
    have heq : firstPortFaceReturn triangleDualRotation triangleDualCrossing d = 1 := by omega
    rw [heq] at hr
    change (portFaceStep triangleDualRotation triangleDualCrossing)^[1] d = d at hr
    have hed : e = d := by
      simpa [Function.iterate_succ_apply', hde] using hr
    exact hneq hed
  exact Nat.le_antisymm hle hge

theorem triangleDual_firstReturn_d00 : firstPortFaceReturn triangleDualRotation triangleDualCrossing d00 = 2 :=
  triangleDual_firstReturn d00 d10 d00 triangleDual_step_d00 triangleDual_step_d10 (by decide)
theorem triangleDual_firstReturn_d01 : firstPortFaceReturn triangleDualRotation triangleDualCrossing d01 = 2 :=
  triangleDual_firstReturn d01 d12 d01 triangleDual_step_d01 triangleDual_step_d12 (by decide)
theorem triangleDual_firstReturn_d02 : firstPortFaceReturn triangleDualRotation triangleDualCrossing d02 = 2 :=
  triangleDual_firstReturn d02 d11 d02 triangleDual_step_d02 triangleDual_step_d11 (by decide)

def triangleDualMap : PortCombinatorialMap triangleDualNetwork where
  crossing := triangleDualCrossing
  rotation := triangleDualRotationSystem
  nonemptyRegions := by decide
  connected := by
    intro r s
    fin_cases r <;> fin_cases s
    · exact ⟨PortRegionWalk.nil triangleDualCrossing _⟩
    · exact ⟨PortRegionWalk.singleton triangleDualCrossing d00⟩
    · exact ⟨PortRegionWalk.singleton triangleDualCrossing d10⟩
    · exact ⟨PortRegionWalk.nil triangleDualCrossing _⟩

theorem triangleDual_faceCount : triangleDualMap.faceCount = 3 := by
  change portFaceCount triangleDualRotation triangleDualCrossing = 3
  have h0 : portFaceOrbit triangleDualRotation triangleDualCrossing d00 = {d00, d10} := by
    rw [portFaceOrbit, triangleDual_firstReturn_d00]
    decide
  have h1 : portFaceOrbit triangleDualRotation triangleDualCrossing d01 = {d01, d12} := by
    rw [portFaceOrbit, triangleDual_firstReturn_d01]
    decide
  have h2 : portFaceOrbit triangleDualRotation triangleDualCrossing d02 = {d02, d11} := by
    rw [portFaceOrbit, triangleDual_firstReturn_d02]
    decide
  have h10 : portFaceOrbit triangleDualRotation triangleDualCrossing d10 =
      portFaceOrbit triangleDualRotation triangleDualCrossing d00 := by
    apply portFaceOrbit_eq_of_mem triangleDualRotation triangleDualCrossing d00 d10
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨1, triangleDual_step_d00⟩
  have h11 : portFaceOrbit triangleDualRotation triangleDualCrossing d11 =
      portFaceOrbit triangleDualRotation triangleDualCrossing d02 := by
    apply portFaceOrbit_eq_of_mem triangleDualRotation triangleDualCrossing d02 d11
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨1, triangleDual_step_d02⟩
  have h12 : portFaceOrbit triangleDualRotation triangleDualCrossing d12 =
      portFaceOrbit triangleDualRotation triangleDualCrossing d01 := by
    apply portFaceOrbit_eq_of_mem triangleDualRotation triangleDualCrossing d01 d12
    rw [portFaceOrbit_mem_iff_iterate]
    exact ⟨1, triangleDual_step_d01⟩
  have hfam : portFaceOrbits triangleDualRotation triangleDualCrossing =
      {portFaceOrbit triangleDualRotation triangleDualCrossing d00,
       portFaceOrbit triangleDualRotation triangleDualCrossing d01,
       portFaceOrbit triangleDualRotation triangleDualCrossing d02} := by
    ext F
    constructor
    · intro h
      rcases (portFaceOrbits_mem_iff triangleDualRotation triangleDualCrossing F).mp h with ⟨p, rfl⟩
      rcases p with ⟨r, i⟩
      fin_cases r <;> fin_cases i
      · change portFaceOrbit triangleDualRotation triangleDualCrossing d00 ∈ _
        simp
      · change portFaceOrbit triangleDualRotation triangleDualCrossing d01 ∈ _
        simp
      · change portFaceOrbit triangleDualRotation triangleDualCrossing d02 ∈ _
        simp
      · change portFaceOrbit triangleDualRotation triangleDualCrossing d10 ∈ _
        rw [h10]
        simp
      · change portFaceOrbit triangleDualRotation triangleDualCrossing d11 ∈ _
        rw [h11]
        simp
      · change portFaceOrbit triangleDualRotation triangleDualCrossing d12 ∈ _
        rw [h12]
        simp
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact portFaceOrbit_mem_orbits triangleDualRotation triangleDualCrossing d00
      · exact portFaceOrbit_mem_orbits triangleDualRotation triangleDualCrossing d01
      · exact portFaceOrbit_mem_orbits triangleDualRotation triangleDualCrossing d02
  unfold portFaceCount
  rw [hfam, h0, h1, h2]
  decide

theorem triangleDual_eulerCharacteristic : triangleDualMap.eulerCharacteristic = 2 := by
  change portCombinatorialEulerCharacteristic triangleDualRotation triangleDualCrossing = 2
  have he : portCrossingEdgeCount triangleDualCrossing = 3 := by decide
  unfold portCombinatorialEulerCharacteristic
  have hf : portFaceCount triangleDualRotation triangleDualCrossing = 3 := triangleDual_faceCount
  rw [he, hf]
  norm_num [portRegionVertexCount, triangleDualNetwork]

example : triangleDualMap.vertexCount = 2 := by decide
example : triangleDualMap.edgeCount = 3 := by decide
example : triangleDualMap.faceCount = 3 := triangleDual_faceCount
example : triangleDualMap.portCount = 6 := by decide
example : triangleDualMap.eulerCharacteristic = 2 := triangleDual_eulerCharacteristic
example : portThreeMap.faceCount = 1 := by
  change portFaceCount portThreeRotation portThreeCrossing = 1
  exact portFaceCount_23
example : portThreeMap.eulerCharacteristic = 0 := portThreeMap_eulerCharacteristic

def triangleDualAssignment : V4FlowAssignment triangleDualCrossing where
  label := fun p => if p.1.val = 0 then
    if p.2.val = 0 then deltaB else if p.2.val = 1 then deltaC else deltaA
  else
    if p.2.val = 0 then deltaA else if p.2.val = 1 then deltaC else deltaB
  nonzero := by
    intro p
    cases p with
    | mk r i => fin_cases r <;> fin_cases i <;> simp [deltaA_ne_zero, deltaB_ne_zero, deltaC_ne_zero]
  cross_sameLabel := by
    intro p
    cases p with
    | mk r i =>
      fin_cases r <;> fin_cases i <;> simp [triangleDualCrossing, triangleDualCross, triangleDualFlip3, portSwap2]

theorem triangleDualAssignment_kirchhoff :
    IsKirchhoffV4Flow triangleDualAssignment := by
  intro r
  fin_cases r <;> decide

theorem triangleColoring_to_dual_labels :
    triangleDualAssignment.label d00 = deltaB ∧
      triangleDualAssignment.label d01 = deltaC ∧
      triangleDualAssignment.label d02 = deltaA := by decide

theorem triangleColoring_transport :
    triangleDualAssignment.label d00 = (coloringToV4Assignment triangleColoring).label t21 ∧
      triangleDualAssignment.label d01 = (coloringToV4Assignment triangleColoring).label t11 ∧
      triangleDualAssignment.label d02 = (coloringToV4Assignment triangleColoring).label t01 := by
  rcases triangleColoring_edge_labels with ⟨hA, hC, hB⟩
  constructor
  · simpa [triangleDualAssignment, d00] using hB.symm
  · constructor
    · simpa [triangleDualAssignment, d01] using hC.symm
    · simpa [triangleDualAssignment, d02] using hA.symm

theorem triangleColoring_to_dual_balanced :
    IsKirchhoffV4Flow triangleDualAssignment ∧
      deltaA + deltaC + deltaB = 0 := by
  constructor
  · exact triangleDualAssignment_kirchhoff
  · calc
      deltaA + deltaC + deltaB = deltaA + deltaB + deltaC := by ac_rfl
      _ = deltaC + deltaC := by rw [deltaA_add_deltaB]
      _ = 0 := state_add_self deltaC

theorem triangle_doubleDual_restores_rotation (p : PortNetworkPort trianglePortNetwork) :
    dualFaceStepRaw trianglePortRotation trianglePortCrossing p =
      trianglePortRotation.rotate p :=
  dualFaceStepRaw_doubleDual_eq_rotation trianglePortRotation trianglePortCrossing p

-- The converse dual-face-conservation -> primal-tension theorem is absent by design.
#print axioms DkMath.Tromino.dualFaceStepRaw_eq_rotation
#print axioms DkMath.Tromino.portFaceBoundaryWalk
#print axioms DkMath.Tromino.faceBoundaryWalk_xor_eq_labelSum
#print axioms DkMath.Tromino.tension_implies_dualFaceKirchhoff
#print axioms DkMath.Tromino.DualLoopFree
#print axioms DkMathTest.Tromino.PortDualityKernelAxiomAudit.triangleDual_faceCount

end DkMathTest.Tromino.PortDualityKernelAxiomAudit
