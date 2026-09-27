/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortKirchhoffFlow
import DkMath.Tromino.PortFaceOrbit
import DkMath.Tromino.PortEulerCount
import DkMath.Tromino.PortRegionWalk

#print "file: DkMath.Tromino.PortDualityKernel"

namespace DkMath.Tromino

open scoped BigOperators

def dualRotationEquiv {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortNetworkPort P ≃ PortNetworkPort P :=
  portFaceEquiv R C

def dualRotationStep {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortNetworkPort P → PortNetworkPort P :=
  dualRotationEquiv R C

theorem dualRotationStep_eq_portFaceStep {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    dualRotationStep R C p = portFaceStep R C p := rfl

def dualFaceStepRaw {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortNetworkPort P → PortNetworkPort P :=
  fun p => dualRotationEquiv R C (C.cross p)

theorem dualFaceStepRaw_eq_rotation {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    dualFaceStepRaw R C p = R.rotate p := by
  change R.rotate (C.cross (C.cross p)) = R.rotate p
  rw [C.involutive]

theorem dualFaceStepRaw_iterate {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (n : Nat) (p : PortNetworkPort P) :
    (dualFaceStepRaw R C)^[n] p = (R.rotate^[n]) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact dualFaceStepRaw_eq_rotation R C _

def SameDualVertex {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p q : PortNetworkPort P) : Prop :=
  SamePortFaceOrbit R C p q

theorem dualRotation_preserves_dualVertex {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    SameDualVertex R C p (dualRotationEquiv R C p) := by
  change portFaceStep R C p ∈ portFaceOrbit R C p
  exact portFaceOrbit_mem_iterate R C p 1

theorem sameDualVertex_iff_dualRotation_iterate {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) :
    SameDualVertex R C p q ↔
      ∃ n : Nat, (dualRotationStep R C)^[n] p = q := by
  change q ∈ portFaceOrbit R C p ↔
    ∃ n : Nat, (portFaceStep R C)^[n] p = q
  exact portFaceOrbit_mem_iff_iterate R C p q

theorem dualVertexClass_card {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    (portFaceOrbit R C p).card = firstPortFaceReturn R C p :=
  portFaceOrbit_card R C p

def SameDualFace {P : PortNetwork} (_R : PortRotationSystem P)
    (_C : PortCrossing P) (p q : PortNetworkPort P) : Prop :=
  p.1 = q.1

theorem sameDualFace_iff_dualFace_iterate {P : PortNetwork}
    (R : PortRotationSystem P) (C : PortCrossing P)
    (p q : PortNetworkPort P) :
    SameDualFace R C p q ↔
      ∃ n : Nat, (dualFaceStepRaw R.toPortLocalRotation C)^[n] p = q := by
  constructor
  · intro h
    rcases p with ⟨r, i⟩
    rcases q with ⟨s, j⟩
    dsimp [SameDualFace] at h
    subst s
    obtain ⟨n, hn⟩ := R.rotation_reaches r i j
    exact ⟨n, by rw [dualFaceStepRaw_iterate]; exact hn⟩
  · rintro ⟨n, hn⟩
    rw [dualFaceStepRaw_iterate] at hn
    exact (R.toPortLocalRotation.iterate_preservesRegion n p).symm.trans
      (congrArg Sigma.fst hn)

def dualVertexCount {P : PortNetwork} (M : PortCombinatorialMap P) : Nat := M.faceCount
def dualEdgeCount {P : PortNetwork} (M : PortCombinatorialMap P) : Nat := M.edgeCount
def dualFaceCount {P : PortNetwork} (M : PortCombinatorialMap P) : Nat := M.vertexCount
def dualPortCount {P : PortNetwork} (M : PortCombinatorialMap P) : Nat := M.portCount

def dualEulerCharacteristic {P : PortNetwork}
    (M : PortCombinatorialMap P) : Int :=
  (dualVertexCount M : Int) - (dualEdgeCount M : Int) + (dualFaceCount M : Int)

theorem dualEulerCharacteristic_eq {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    dualEulerCharacteristic M = M.eulerCharacteristic := by
  change (M.faceCount : Int) - (M.edgeCount : Int) + (M.vertexCount : Int) =
    (M.vertexCount : Int) - (M.edgeCount : Int) + (M.faceCount : Int)
  ring

def portFaceBoundaryEdges {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : List (PortNetworkPort P) :=
  List.ofFn (fun i : Fin (firstPortFaceReturn R C p) =>
    (portFaceStep R C)^[i.val] p)

theorem portFaceBoundaryEdges_length {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceBoundaryEdges R C p).length = firstPortFaceReturn R C p := by
  simp [portFaceBoundaryEdges]

theorem portFaceBoundary_prefix_valid {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) (n : Nat) :
    PortRegionWalk.Valid C p.1 (C.cross ((portFaceStep R C)^[n] p)).1
      (List.ofFn (fun i : Fin (n + 1) => (portFaceStep R C)^[i.val] p)) := by
  induction n generalizing p with
  | zero => simp [List.ofFn_succ, PortRegionWalk.Valid]
  | succ n ih =>
    rw [List.ofFn_succ]
    constructor
    · rfl
    · have h := ih (portFaceStep R C p)
      convert h using 1
      · exact (portFaceStep_source R C p).symm
      · rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      · apply congrArg List.ofFn
        funext i
        change (portFaceStep R C)^[i.val + 1] p =
          (portFaceStep R C)^[i.val] (portFaceStep R C p)
        exact Function.iterate_succ_apply (portFaceStep R C) i.val p

theorem portFaceBoundaryWalk_valid {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    PortRegionWalk.Valid C p.1 p.1 (portFaceBoundaryEdges R C p) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (firstPortFaceReturn_spec R C p).1)
  change PortRegionWalk.Valid C p.1 p.1
    (List.ofFn (fun i : Fin (firstPortFaceReturn R C p) =>
      (portFaceStep R C)^[i.val] p))
  rw [hn]
  have h := portFaceBoundary_prefix_valid R C p n
  have hreturn := (firstPortFaceReturn_spec R C p).2
  rw [hn] at hreturn
  have hend : (C.cross ((portFaceStep R C)^[n] p)).1 = p.1 := by
    calc
      (C.cross ((portFaceStep R C)^[n] p)).1 =
          (portFaceStep R C ((portFaceStep R C)^[n] p)).1 := by
            exact (portFaceStep_source R C _).symm
      _ = p.1 := by
        simpa [Function.iterate_succ_apply'] using congrArg Sigma.fst hreturn
  rw [hend] at h
  exact h

def portFaceBoundaryWalk {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : PortRegionWalk C p.1 p.1 :=
  ⟨portFaceBoundaryEdges R C p, portFaceBoundaryWalk_valid R C p⟩

theorem portFaceBoundaryWalk_length {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceBoundaryWalk R C p).length = firstPortFaceReturn R C p :=
  portFaceBoundaryEdges_length R C p

theorem portFaceBoundaryWalk_mem_faceOrbit {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) (hq : q ∈ (portFaceBoundaryWalk R C p).edges) :
    q ∈ portFaceOrbit R C p := by
  rcases (List.mem_ofFn.mp hq) with ⟨i, rfl⟩
  exact portFaceOrbit_mem_iterate R C p i.val

theorem portFaceBoundaryWalk_edges_toFinset {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceBoundaryWalk R C p).edges.toFinset = portFaceOrbit R C p := by
  ext q
  constructor
  · intro hq
    change q ∈ (portFaceBoundaryEdges R C p).toFinset at hq
    exact portFaceBoundaryWalk_mem_faceOrbit R C p q (List.mem_toFinset.mp hq)
  · intro hq
    rcases (portFaceOrbit_mem_iff_iterate R C p q).mp hq with ⟨n, hn⟩
    change q ∈ (portFaceBoundaryEdges R C p).toFinset
    rw [portFaceBoundaryEdges, List.mem_toFinset]
    rcases Nat.mod_lt n (firstPortFaceReturn_spec R C p).1 with hmod
    refine List.mem_ofFn.mpr ⟨⟨n % firstPortFaceReturn R C p, hmod⟩, ?_⟩
    have hperiod : Function.IsPeriodicPt (portFaceStep R C)
        (firstPortFaceReturn R C p) p := (firstPortFaceReturn_spec R C p).2
    exact (hperiod.iterate_mod_apply n).trans hn

def faceBoundaryLabelSum {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (R : PortLocalRotation P)
    (p : PortNetworkPort P) : TrominoState :=
  ∑ q ∈ portFaceOrbit R C p, A.label q

theorem portFaceBoundaryWalk_edges_nodup {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceBoundaryWalk R C p).edges.Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  apply Fin.ext
  exact portFaceOrbit_iterate_distinct R C p i.isLt j.isLt hij

theorem faceBoundaryWalk_xor_eq_labelSum {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (R : PortLocalRotation P) (p : PortNetworkPort P) :
    regionWalkXor ((portFaceBoundaryWalk R C p).toFlowRegionWalk A) =
      faceBoundaryLabelSum A R p := by
  have hnodup := portFaceBoundaryWalk_edges_nodup R C p
  have hset := portFaceBoundaryWalk_edges_toFinset R C p
  change (List.map (fun q => A.label q) (portFaceBoundaryWalk R C p).edges).sum = _
  rw [← List.sum_toFinset (fun q => A.label q) hnodup]
  rw [hset]
  rfl

def IsDualFaceKirchhoff {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (R : PortLocalRotation P) : Prop :=
  ∀ p, faceBoundaryLabelSum A R p = 0

theorem tension_implies_dualFaceKirchhoff {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (R : PortLocalRotation P) (hzero : IsZeroHolonomyV4Tension A) :
    IsDualFaceKirchhoff A R := by
  intro p
  let W : ClosedRegionWalk A.toFlowCrossing p.1 :=
    PortRegionWalk.toFlowRegionWalk A (portFaceBoundaryWalk R C p)
  have h := hzero p.1 W
  rw [faceBoundaryWalk_xor_eq_labelSum A R p] at h
  exact h

def IsDualLoopPort {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : Prop :=
  SamePortFaceOrbit R C p (C.cross p)

def DualLoopFree {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : Prop := ∀ p, ¬ IsDualLoopPort R C p

theorem isDualLoopPort_cross_iff {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    IsDualLoopPort R C p ↔ IsDualLoopPort R C (C.cross p) := by
  constructor
  · intro h
    change SamePortFaceOrbit R C p (C.cross p) at h
    change SamePortFaceOrbit R C (C.cross p) (C.cross (C.cross p))
    rw [C.involutive]
    exact samePortFaceOrbit_symm R C h
  · intro h
    change SamePortFaceOrbit R C (C.cross p) (C.cross (C.cross p)) at h
    rw [C.involutive] at h
    change SamePortFaceOrbit R C p (C.cross p)
    exact samePortFaceOrbit_symm R C h

theorem isDualLoopPort_edgePair {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) (hq : q ∈ portCrossingEdgePair C p)
    (hloop : IsDualLoopPort R C p) : SamePortFaceOrbit R C p q := by
  simp only [portCrossingEdgePair, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with hq | hq
  · subst q
    exact samePortFaceOrbit_refl R C p
  · subst q
    exact hloop

theorem dualLoop_edgePair_labelSum_zero {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : PortNetworkPort P) (_hloop : ∃ R, IsDualLoopPort R C p) :
    (∑ q ∈ portCrossingEdgePair C p, A.label q) = 0 := by
  have hne : p ≠ C.cross p := (C.cross_ne p).symm
  simp [portCrossingEdgePair, hne, A.cross_sameLabel, state_add_self]

theorem dualFaceStepRaw_doubleDual_eq_rotation {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    dualFaceStepRaw R C p = R.rotate p := dualFaceStepRaw_eq_rotation R C p

end DkMath.Tromino
