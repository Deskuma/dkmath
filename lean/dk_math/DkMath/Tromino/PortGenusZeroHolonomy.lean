/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortF2Exactness
import DkMath.Tromino.PortDualityKernel
import DkMath.Tromino.PortTensionColoring
import DkMath.Tromino.PortV4Chains

#print "file: DkMath.Tromino.PortGenusZeroHolonomy"

/-!
# Genus-zero face conservation and zero holonomy

This module closes the converse direction between face-boundary V4
conservation and zero holonomy for a fixed assignment on a connected
genus-zero Port combinatorial map.  It does not construct a universal
face-conservative assignment, a general dual PortNetwork, a topological
realization, or a Four Color theorem endpoint.

The tetrahedral rolling interpretation is that a face boundary records the
V4 delta accumulated by a rolling route.  TRM-037 and this module show that,
on a genus-zero combinatorial certificate, face-conservative assignments have
zero closed-route color holonomy.  Full tetrahedron orientation holonomy is
stronger and is not represented here.
-/

namespace DkMath.Tromino

open scoped BigOperators

/-! ## Canonical edge labels and scalar evaluation -/

/-- Sum the label of an edge cell once, using a canonical endpoint order. -/
def assignmentEdgeLabel {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (E : PortEdgeCell C) : TrominoState :=
  Finset.sum E.val (fun p => if p.1 < (C.cross p).1 then A.label p else 0)

/-- The canonical edge-cell label is the label of either endpoint. -/
theorem assignmentEdgeLabel_edgeCellOfPort {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    assignmentEdgeLabel A (edgeCellOfPort C p) = A.label p := by
  classical
  change Finset.sum {p, C.cross p}
    (fun q => if q.1 < (C.cross q).1 then A.label q else 0) = A.label p
  have hne : p.1 ≠ (C.cross p).1 := (C.changesRegion p).symm
  by_cases hlt : p.1 < (C.cross p).1
  · have hgt : ¬ (C.cross p).1 < p.1 := by
      exact not_lt_of_ge (le_of_lt hlt)
    rw [Finset.sum_insert (by simpa using (C.cross_ne p).symm)]
    rw [Finset.sum_singleton, C.involutive]
    simp [hlt, hgt]
  · have hgt : (C.cross p).1 < p.1 := by
      exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    rw [Finset.sum_insert (by simpa using (C.cross_ne p).symm)]
    rw [Finset.sum_singleton, C.involutive]
    simp [hlt, hgt, A.cross_sameLabel]

/-- Crossing to the other endpoint leaves the edge-cell label unchanged. -/
theorem assignmentEdgeLabel_edgeCellOfPort_cross {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    assignmentEdgeLabel A (edgeCellOfPort C (C.cross p)) = A.label p := by
  rw [edgeCellOfPort_cross]
  exact assignmentEdgeLabel_edgeCellOfPort A p

/-- Evaluate an F₂ edge chain by summing its V4 edge labels. -/
def portEdgeLabelEval {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    PortEdgeChain C →ₗ[PortF2] TrominoState :=
  { toFun := fun x => ∑ E : PortEdgeCell C, x E • assignmentEdgeLabel A E
    map_add' := by
      intro x y
      simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      simp [smul_smul, Finset.smul_sum] }

/-- Unfolding the evaluator exposes its finite linear combination. -/
@[simp] theorem portEdgeLabelEval_apply {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (x : PortEdgeChain C) :
    portEdgeLabelEval A x =
      ∑ E : PortEdgeCell C, x E • assignmentEdgeLabel A E := rfl

/-- A basis chain supported on one edge evaluates to that edge label. -/
theorem portEdgeLabelEval_edgeBasis {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    portEdgeLabelEval A
        (fun E => if edgeCellOfPort C p = E then 1 else 0) =
      A.label p := by
  classical
  rw [portEdgeLabelEval_apply]
  simp only [eq_comm, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact assignmentEdgeLabel_edgeCellOfPort A p

/-- A one-edge walk evaluates to the label of its crossing port. -/
theorem portEdgeLabelEval_singleton {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (p : PortNetworkPort P) :
    portEdgeLabelEval A (portWalkEdgeChain (PortRegionWalk.singleton C p)) =
      A.label p := by
  rw [portWalkEdgeChain_singleton]
  exact portEdgeLabelEval_edgeBasis A p

/-! ## Evaluation of structural walks -/

/-- Evaluation of a walk's incidence chain is the XOR of its labels. -/
theorem portEdgeLabelEval_walkEdgeCoeff {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (xs : List (PortNetworkPort P)) :
    portEdgeLabelEval A (fun E => walkEdgeCoeff C E xs) =
      (xs.map A.label).sum := by
  induction xs with
  | nil =>
      simp [walkEdgeCoeff]
  | cons p xs ih =>
      have hdecomp :
          (fun E : PortEdgeCell C => walkEdgeCoeff C E (p :: xs)) =
            (fun E => if edgeCellOfPort C p = E then 1 else 0) +
              (fun E => walkEdgeCoeff C E xs) := by
        funext E
        by_cases h : p ∈ E.val
        · have he : edgeCellOfPort C p = E :=
            (edgeCellOfPort_eq_iff C p E).2 h
          simp [walkEdgeCoeff, h, he]
        · have he : edgeCellOfPort C p ≠ E := fun heq =>
            h ((edgeCellOfPort_eq_iff C p E).1 heq)
          simp [walkEdgeCoeff, h, he]
      rw [hdecomp, map_add, portEdgeLabelEval_edgeBasis, ih]
      rfl

/-- The evaluator agrees with the flow-language walk XOR. -/
theorem portEdgeLabelEval_portWalkEdgeChain {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    {r s : Fin P.regionCount} (W : PortRegionWalk C r s) :
    portEdgeLabelEval A (portWalkEdgeChain W) =
      regionWalkXor (W.toFlowRegionWalk A) := by
  exact portEdgeLabelEval_walkEdgeCoeff A W.edges

/-- The same evaluation identity holds for a flow-language walk. -/
theorem portEdgeLabelEval_flowWalk {P : PortNetwork}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    {r s : Fin P.regionCount} (W : FlowRegionWalk A.toFlowCrossing r s) :
    portEdgeLabelEval A
        (portWalkEdgeChain W.toPortRegionWalk) = regionWalkXor W := by
  exact portEdgeLabelEval_walkEdgeCoeff A W.edges

/-! ## Face-cell conservation -/

/-- Sum the V4 labels around one face cell. -/
def faceCellLabelSum {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (R : PortLocalRotation P)
    (F : PortFaceCell R C) : TrominoState :=
  portEdgeLabelEval A (faceBoundaryEdgeChain F)

/-- The face-cell sum is the boundary-walk label sum at any representative. -/
theorem faceCellLabelSum_faceCellOfPort {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (p : PortNetworkPort P) :
    faceCellLabelSum A R (faceCellOfPort R C p) = faceBoundaryLabelSum A R p := by
  rw [faceCellLabelSum, faceBoundaryEdgeChain_eq_walk,
    portEdgeLabelEval_portWalkEdgeChain,
    faceBoundaryWalk_xor_eq_labelSum]

/-- Face-cell label sums do not depend on the chosen representative port. -/
theorem faceCellLabelSum_representative_invariant {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) {p q : PortNetworkPort P}
    (h : faceCellOfPort R C p = faceCellOfPort R C q) :
    faceBoundaryLabelSum A R p = faceBoundaryLabelSum A R q := by
  rw [← faceCellLabelSum_faceCellOfPort A p, ←
    faceCellLabelSum_faceCellOfPort A q, h]

/-- Every face cell has zero total V4 boundary label. -/
def IsFaceCellKirchhoff {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (R : PortLocalRotation P) : Prop :=
  ∀ F : PortFaceCell R C, faceCellLabelSum A R F = 0

/-- Representative-free face conservation equals dual face conservation. -/
theorem isFaceCellKirchhoff_iff_dualFaceKirchhoff {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) :
    IsFaceCellKirchhoff A R ↔ IsDualFaceKirchhoff A R := by
  constructor
  · intro h p
    rw [← faceCellLabelSum_faceCellOfPort A p]
    exact h _
  · intro h F
    rcases (portFaceOrbits_mem_iff R C F.val).mp F.property with ⟨p, hp⟩
    have hF : faceCellOfPort R C p = F := Subtype.ext hp.symm
    rw [← hF, faceCellLabelSum_faceCellOfPort]
    exact h p

/-! ## Boundary-two/evaluation adjunction -/

/-- Evaluation turns a face boundary chain into the sum of face labels. -/
theorem portEdgeLabelEval_boundary2 {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (y : PortFaceChain R C) :
    portEdgeLabelEval A (portBoundary2 R C y) =
      ∑ F : PortFaceCell R C, y F • faceCellLabelSum A R F := by
  rw [portBoundary2_as_sum_basis]
  simp only [map_sum, map_smul]
  rfl

/-- Face conservation annihilates every F₂ face boundary. -/
theorem portEdgeLabelEval_boundary2_eq_zero_of_faceKirchhoff
    {P : PortNetwork} {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (hface : IsFaceCellKirchhoff A R)
    (y : PortFaceChain R C) :
    portEdgeLabelEval A (portBoundary2 R C y) = 0 := by
  rw [portEdgeLabelEval_boundary2]
  apply Finset.sum_eq_zero
  intro F hF
  rw [hface F, smul_zero]

/-- Dual face conservation also annihilates every face boundary. -/
theorem portEdgeLabelEval_boundary2_eq_zero_of_dualFaceKirchhoff
    {P : PortNetwork} {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (hdual : IsDualFaceKirchhoff A R)
    (y : PortFaceChain R C) :
    portEdgeLabelEval A (portBoundary2 R C y) = 0 := by
  exact portEdgeLabelEval_boundary2_eq_zero_of_faceKirchhoff (R := R) A
    ((isFaceCellKirchhoff_iff_dualFaceKirchhoff (R := R) A).mpr hdual) y

/-! ## Genus-zero closure -/

/-- On genus zero, a closed walk has zero V4 holonomy under face conservation. -/
theorem portGenusZero_closedWalk_xor_eq_zero_of_dualFaceKirchhoff
    {P : PortNetwork} (G : PortGenusZeroCombinatorialMap P)
    (A : V4FlowAssignment G.map.crossing)
    (hface : IsDualFaceKirchhoff A G.map.localRotation)
    {r : Fin P.regionCount} (W : PortRegionWalk G.map.crossing r r) :
    regionWalkXor (W.toFlowRegionWalk A) = 0 := by
  rcases portGenusZero_closed_portWalkEdgeChain_mem_faceBoundarySpace G W with
    ⟨y, hy⟩
  calc
    regionWalkXor (W.toFlowRegionWalk A) = portEdgeLabelEval A
        (portWalkEdgeChain W) :=
      (portEdgeLabelEval_portWalkEdgeChain A W).symm
    _ = portEdgeLabelEval A (portBoundary2 G.map.localRotation G.map.crossing y) := by
      rw [hy]
    _ = 0 := portEdgeLabelEval_boundary2_eq_zero_of_dualFaceKirchhoff A hface y

/-- Dual face conservation implies the zero-holonomy tension condition. -/
theorem portGenusZero_zeroHolonomy_of_dualFaceKirchhoff
    {P : PortNetwork} (G : PortGenusZeroCombinatorialMap P)
    (A : V4FlowAssignment G.map.crossing)
    (hface : IsDualFaceKirchhoff A G.map.localRotation) :
    IsZeroHolonomyV4Tension A := by
  intro r W
  have h := portGenusZero_closedWalk_xor_eq_zero_of_dualFaceKirchhoff
    G A hface W.toPortRegionWalk
  rw [← FlowRegionWalk.toPortRegionWalk_toFlowRegionWalk W]
  exact h

/-- On a genus-zero map, dual face conservation and zero holonomy coincide. -/
theorem portGenusZero_dualFaceKirchhoff_iff_zeroHolonomy
    {P : PortNetwork} (G : PortGenusZeroCombinatorialMap P)
    (A : V4FlowAssignment G.map.crossing) :
    IsDualFaceKirchhoff A G.map.localRotation ↔
      IsZeroHolonomyV4Tension A := by
  constructor
  · exact portGenusZero_zeroHolonomy_of_dualFaceKirchhoff G A
  · exact tension_implies_dualFaceKirchhoff A G.map.localRotation

/-- A genus-zero dual-conservative assignment induces a region coloring. -/
theorem exists_portColoring_of_dualFaceKirchhoff
    {P : PortNetwork} (G : PortGenusZeroCombinatorialMap P)
    (A : V4FlowAssignment G.map.crossing)
    (hface : IsDualFaceKirchhoff A G.map.localRotation) :
    ∃ K : (portRegionSimpleGraph G.map.crossing).Coloring TrominoState,
      ∀ p, (coloringToV4Assignment K).label p = A.label p := by
  exact exists_portColoring_of_zeroHolonomyV4Tension G.map A
    (portGenusZero_zeroHolonomy_of_dualFaceKirchhoff G A hface)

/-- The preceding coloring existence can be exposed without its label equation. -/
theorem exists_portColoring_of_dualFaceKirchhoff_only
    {P : PortNetwork} (G : PortGenusZeroCombinatorialMap P)
    (A : V4FlowAssignment G.map.crossing)
    (hface : IsDualFaceKirchhoff A G.map.localRotation) :
    ∃ _K : (portRegionSimpleGraph G.map.crossing).Coloring TrominoState, True := by
  obtain ⟨K, _⟩ := exists_portColoring_of_dualFaceKirchhoff G A hface
  exact ⟨K, trivial⟩

/-- Existence of a dual-face-conservative V4 assignment. -/
def HasDualFaceKirchhoffV4Assignment {P : PortNetwork}
    (M : PortCombinatorialMap P) : Prop :=
  ∃ A : V4FlowAssignment M.crossing,
    IsDualFaceKirchhoff A M.localRotation

/-- On genus zero, dual conservation is equivalent to four-state colorability. -/
theorem PortGenusZeroCombinatorialMap.dualFaceKirchhoff_iff_colorable
    {P : PortNetwork} (G : PortGenusZeroCombinatorialMap P) :
    HasDualFaceKirchhoffV4Assignment G.map ↔
      PortFourStateColorable G.map.crossing := by
  constructor
  · rintro ⟨A, hface⟩
    exact ⟨(exists_portColoring_of_dualFaceKirchhoff G A hface).choose⟩
  · rintro ⟨K⟩
    refine ⟨coloringToV4Assignment K, ?_⟩
    exact tension_implies_dualFaceKirchhoff
      (coloringToV4Assignment K) G.map.localRotation
      (coloringToV4Assignment_isZeroHolonomy K)

/-- Universal target asserting a conservative assignment on every genus-zero map. -/
def PortGenusZeroDualFaceKirchhoffTarget : Prop :=
  ∀ (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
    HasDualFaceKirchhoffV4Assignment G.map

/-- The conservative-assignment target is exactly the four-color target. -/
theorem portGenusZeroDualFaceKirchhoffTarget_iff_fourColorTarget :
    PortGenusZeroDualFaceKirchhoffTarget ↔
      PortGenusZeroFourColorTarget := by
  constructor
  · intro h P G
    exact (G.dualFaceKirchhoff_iff_colorable).mp (h P G)
  · intro h P G
    exact (G.dualFaceKirchhoff_iff_colorable).mpr (h P G)

end DkMath.Tromino
