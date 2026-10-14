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

/-!
# The dual face-step kernel

The dual rotation is the port face-step permutation, and the raw dual face
step is rotation after the crossing involution.  This presents the same
finite dart permutation from the dual viewpoint: primal faces become dual
vertices, primal regions become dual faces, and crossing edges remain
edges.  The boundary-walk and label-sum lemmas turn dual face conservation
into a local algebraic condition, while explicitly retaining the possible
dual-loop obstruction.
-/

namespace DkMath.Tromino

open scoped BigOperators

/-- The dual rotation is the permutation obtained from the face step.

The dual vertex motion is therefore exactly the primal face permutation;
duality is implemented by reusing the same finite dart equivalence. -/
def dualRotationEquiv {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortNetworkPort P ≃ PortNetworkPort P :=
  portFaceEquiv R C

/-- The corresponding dual rotation function. -/
def dualRotationStep {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortNetworkPort P → PortNetworkPort P :=
  dualRotationEquiv R C

/-- Dual rotation and primal face step are definitionally the same map. -/
theorem dualRotationStep_eq_portFaceStep {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    dualRotationStep R C p = portFaceStep R C p := rfl

/-- Raw dual face motion rotates after crossing the current dart.

This is the complementary composition to the dual rotation: crossing moves
to the other edge incidence, then the dual rotation advances around the
corresponding dual vertex. -/
def dualFaceStepRaw {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortNetworkPort P → PortNetworkPort P :=
  fun p => dualRotationEquiv R C (C.cross p)

/-- Crossing twice cancels, so raw dual face motion is local rotation.

The apparent dual two-step reduces definitionally to the original local
rotation because the crossing is an involution. -/
theorem dualFaceStepRaw_eq_rotation {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    dualFaceStepRaw R C p = R.rotate p := by
  change R.rotate (C.cross (C.cross p)) = R.rotate p
  rw [C.involutive]

/-- Iterated raw dual face motion is iterated local rotation. -/
theorem dualFaceStepRaw_iterate {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (n : Nat) (p : PortNetworkPort P) :
    (dualFaceStepRaw R C)^[n] p = (R.rotate^[n]) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact dualFaceStepRaw_eq_rotation R C _

/-- Equivalence relation identifying darts in one dual-vertex orbit.

Dual vertices are represented by primal face orbits, so this relation is
the same finite orbit relation already established for the primal face
permutation. -/
def SameDualVertex {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p q : PortNetworkPort P) : Prop :=
  SamePortFaceOrbit R C p q

/-- A dual rotation step remains in the same dual vertex. -/
theorem dualRotation_preserves_dualVertex {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    SameDualVertex R C p (dualRotationEquiv R C p) := by
  change portFaceStep R C p ∈ portFaceOrbit R C p
  exact portFaceOrbit_mem_iterate R C p 1

/-- Dual-vertex equivalence is exactly reachability by dual rotation. -/
theorem sameDualVertex_iff_dualRotation_iterate {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) :
    SameDualVertex R C p q ↔
      ∃ n : Nat, (dualRotationStep R C)^[n] p = q := by
  change q ∈ portFaceOrbit R C p ↔
    ∃ n : Nat, (portFaceStep R C)^[n] p = q
  exact portFaceOrbit_mem_iff_iterate R C p q

/-- Dual vertex classes have the cardinality of their rotation orbits. -/
theorem dualVertexClass_card {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    (portFaceOrbit R C p).card = firstPortFaceReturn R C p :=
  portFaceOrbit_card R C p

/-- Equivalence relation identifying darts in one dual-face orbit. -/
def SameDualFace {P : PortNetwork} (_R : PortRotationSystem P)
    (_C : PortCrossing P) (p q : PortNetworkPort P) : Prop :=
  p.1 = q.1

/-- Dual-face equivalence is characterized by iterated dual face motion. -/
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

/-- Dual vertices are primal faces.

The count is exchanged by definition: each primal face orbit becomes one
dual vertex cell. -/
def dualVertexCount {P : PortNetwork} (M : PortCombinatorialMap P) : Nat := M.faceCount
/-- Dual edges are primal edges.

Crossing orbits are unchanged by the dual viewpoint, so the edge count is
the same finite two-dart partition. -/
def dualEdgeCount {P : PortNetwork} (M : PortCombinatorialMap P) : Nat := M.edgeCount
/-- Dual faces are primal regions.

The region carrier becomes the dual face carrier, exchanging the vertex and
face counts in the Euler formula. -/
def dualFaceCount {P : PortNetwork} (M : PortCombinatorialMap P) : Nat := M.vertexCount
/-- The dual construction preserves the dart carrier size. -/
def dualPortCount {P : PortNetwork} (M : PortCombinatorialMap P) : Nat := M.portCount

/-- The dual Euler characteristic computed from exchanged counts.

This definition performs the formal exchange `V ↔ F` while leaving `E`
fixed.  The next theorem shows algebraically that `V - E + F` is invariant
under this exchange. -/
def dualEulerCharacteristic {P : PortNetwork}
    (M : PortCombinatorialMap P) : Int :=
  (dualVertexCount M : Int) - (dualEdgeCount M : Int) + (dualFaceCount M : Int)

/-- Duality preserves the combinatorial Euler characteristic. -/
theorem dualEulerCharacteristic_eq {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    dualEulerCharacteristic M = M.eulerCharacteristic := by
  change (M.faceCount : Int) - (M.edgeCount : Int) + (M.vertexCount : Int) =
    (M.vertexCount : Int) - (M.edgeCount : Int) + (M.faceCount : Int)
  ring

/-- List the successive darts along the face boundary of a port.

The list records the canonical iterates indexed by the first-return
interval; it is the ordered boundary counterpart of the unordered face
orbit finset. -/
def portFaceBoundaryEdges {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : List (PortNetworkPort P) :=
  List.ofFn (fun i : Fin (firstPortFaceReturn R C p) =>
    (portFaceStep R C)^[i.val] p)

/-- The boundary list has the first-return length. -/
theorem portFaceBoundaryEdges_length {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceBoundaryEdges R C p).length = firstPortFaceReturn R C p := by
  simp [portFaceBoundaryEdges]

/-- Every prefix of a face boundary is a valid region walk. -/
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

/-- The full face boundary is a closed valid region walk.

The face-step source equation supplies each successive region transition,
and the first-return equation closes the final endpoint.  Thus every
combinatorial face has a certified finite boundary walk. -/
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

/-- Package a face boundary as a region walk. -/
def portFaceBoundaryWalk {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : PortRegionWalk C p.1 p.1 :=
  ⟨portFaceBoundaryEdges R C p, portFaceBoundaryWalk_valid R C p⟩

/-- The packaged face boundary has the orbit length. -/
theorem portFaceBoundaryWalk_length {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceBoundaryWalk R C p).length = firstPortFaceReturn R C p :=
  portFaceBoundaryEdges_length R C p

/-- Every boundary dart belongs to the same face orbit as the start. -/
theorem portFaceBoundaryWalk_mem_faceOrbit {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) (hq : q ∈ (portFaceBoundaryWalk R C p).edges) :
    q ∈ portFaceOrbit R C p := by
  rcases (List.mem_ofFn.mp hq) with ⟨i, rfl⟩
  exact portFaceOrbit_mem_iterate R C p i.val

/-- The boundary walk's edge list has the expected finite support. -/
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

/-- XOR of the labels encountered on one face boundary. -/
def faceBoundaryLabelSum {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (R : PortLocalRotation P)
    (p : PortNetworkPort P) : TrominoState :=
  ∑ q ∈ portFaceOrbit R C p, A.label q

/-- A primitive face boundary has no repeated darts. -/
theorem portFaceBoundaryWalk_edges_nodup {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    (portFaceBoundaryWalk R C p).edges.Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  apply Fin.ext
  exact portFaceOrbit_iterate_distinct R C p i.isLt j.isLt hij

/-- The walk XOR equals the face-boundary label sum. -/
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

/-- Every dual face boundary has zero V4 label sum. -/
def IsDualFaceKirchhoff {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (R : PortLocalRotation P) : Prop :=
  ∀ p, faceBoundaryLabelSum A R p = 0

/-- A tension assignment has zero sum around every dual face. -/
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

/-- Predicate that a dart lies on a degenerate dual loop. -/
def IsDualLoopPort {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : Prop :=
  SamePortFaceOrbit R C p (C.cross p)

/-- No port is allowed to lie on a dual loop. -/
def DualLoopFree {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : Prop := ∀ p, ¬ IsDualLoopPort R C p

/-- Crossing preserves the dual-loop condition. -/
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

/-- A dual loop is detected by its crossing edge pair. -/
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

/-- A dual-loop edge pair has zero total V4 label. -/
theorem dualLoop_edgePair_labelSum_zero {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : PortNetworkPort P) (_hloop : ∃ R, IsDualLoopPort R C p) :
    (∑ q ∈ portCrossingEdgePair C p, A.label q) = 0 := by
  have hne : p ≠ C.cross p := (C.cross_ne p).symm
  simp [portCrossingEdgePair, hne, A.cross_sameLabel, state_add_self]

/-- Applying the raw dual construction twice returns the primal rotation. -/
theorem dualFaceStepRaw_doubleDual_eq_rotation {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (p : PortNetworkPort P) :
    dualFaceStepRaw R C p = R.rotate p := dualFaceStepRaw_eq_rotation R C p

end DkMath.Tromino
