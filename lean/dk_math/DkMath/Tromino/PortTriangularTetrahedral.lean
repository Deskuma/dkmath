/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.TetrahedralClosure
import DkMath.Tromino.PortGenusZeroHolonomy

#print "file: DkMath.Tromino.PortTriangularTetrahedral"

namespace DkMath.Tromino

open scoped BigOperators

def IsTriangularPortFace {P : PortNetwork} {R : PortLocalRotation P}
    {C : PortCrossing P} (F : PortFaceCell R C) : Prop :=
  F.val.card = 3

def PortAllFacesTriangular {P : PortNetwork}
    (M : PortCombinatorialMap P) : Prop :=
  ∀ F : PortFaceCell M.localRotation M.crossing,
    IsTriangularPortFace F

def facePortLabelSet {P : PortNetwork} {R : PortLocalRotation P}
    {C : PortCrossing P} (A : V4FlowAssignment C)
    (F : PortFaceCell R C) : Finset TrominoState :=
  F.val.image A.label

theorem facePortLabelSet_subset_deltaSet {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (F : PortFaceCell R C) :
    facePortLabelSet A F ⊆ ({deltaA, deltaB, deltaC} : Finset TrominoState) := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC _ (A.nonzero p) with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

theorem faceCellLabelSum_eq_facePortLabelSum {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (F : PortFaceCell R C) :
    faceCellLabelSum A R F = ∑ p ∈ F.val, A.label p := by
  rcases (portFaceOrbits_mem_iff R C F.val).mp F.property with ⟨p, hp⟩
  have hF : faceCellOfPort R C p = F := Subtype.ext hp.symm
  rw [← hF, faceCellLabelSum_faceCellOfPort]
  rfl

theorem triangular_faceLabelSet_iff_faceCellLabelSum_zero
    {P : PortNetwork} {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (F : PortFaceCell R C)
    (htri : IsTriangularPortFace F) :
    faceCellLabelSum A R F = 0 ↔
      facePortLabelSet A F = ({deltaA, deltaB, deltaC} : Finset TrominoState) := by
  rcases Finset.card_eq_three.mp htri with ⟨p, q, r, hpq, hpr, hqr, hF⟩
  have hsum_eq : faceCellLabelSum A R F =
      A.label p + A.label q + A.label r := by
    rw [faceCellLabelSum_eq_facePortLabelSum, hF]
    simp [hpq, hpr, hqr, add_assoc]
  have hset_eq : facePortLabelSet A F =
      ({A.label p, A.label q, A.label r} : Finset TrominoState) := by
    rw [facePortLabelSet, hF]
    simp
  rw [hsum_eq, hset_eq]
  exact three_nonzero_sum_zero_iff_delta_finset
    (A.nonzero p) (A.nonzero q) (A.nonzero r)

theorem conserved_triangular_face_label_injective
    {P : PortNetwork} {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (F : PortFaceCell R C)
    (htri : IsTriangularPortFace F) (hsum : faceCellLabelSum A R F = 0) :
    Set.InjOn A.label F.val := by
  have hset := (triangular_faceLabelSet_iff_faceCellLabelSum_zero A F htri).mp hsum
  have hcard : (facePortLabelSet A F).card = F.val.card := by
    rw [hset, htri]
    decide
  exact (Finset.card_image_iff.mp hcard)

theorem conserved_triangular_face_no_crossing_pair
    {P : PortNetwork} {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (F : PortFaceCell R C)
    (htri : IsTriangularPortFace F) (hsum : faceCellLabelSum A R F = 0) :
    ∀ p, p ∈ F.val → C.cross p ∉ F.val := by
  intro p hp hcross
  have hinj := conserved_triangular_face_label_injective A F htri hsum
  have heq : A.label p = A.label (C.cross p) := (A.cross_sameLabel p).symm
  have hpc : p = C.cross p := hinj hp hcross heq
  exact C.cross_ne p hpc.symm

def IsTetrahedralFacePattern {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (A : V4FlowAssignment C) (F : PortFaceCell R C) : Prop :=
  IsTriangularPortFace F ∧
    facePortLabelSet A F = ({deltaA, deltaB, deltaC} : Finset TrominoState)

theorem isDualFaceKirchhoff_iff_tetrahedralFacePattern
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (htri : PortAllFacesTriangular M) (A : V4FlowAssignment M.crossing) :
    IsDualFaceKirchhoff A M.localRotation ↔
      ∀ F : PortFaceCell M.localRotation M.crossing,
        IsTetrahedralFacePattern A F := by
  constructor
  · intro h F
    refine ⟨htri F, ?_⟩
    exact (triangular_faceLabelSet_iff_faceCellLabelSum_zero A F (htri F)).mp
      ((isFaceCellKirchhoff_iff_dualFaceKirchhoff (R := M.localRotation) A).mpr h F)
  · intro h
    apply (isFaceCellKirchhoff_iff_dualFaceKirchhoff (R := M.localRotation) A).mp
    intro F
    exact (triangular_faceLabelSet_iff_faceCellLabelSum_zero A F (h F).1).mpr
      (h F).2

def HasTetrahedralFaceAssignment {P : PortNetwork}
    (M : PortCombinatorialMap P) : Prop :=
  ∃ A : V4FlowAssignment M.crossing,
    ∀ F : PortFaceCell M.localRotation M.crossing,
      IsTetrahedralFacePattern A F

theorem hasTetrahedralFaceAssignment_iff_dualFaceKirchhoff
    {P : PortNetwork} (G : PortGenusZeroCombinatorialMap P)
    (htri : PortAllFacesTriangular G.map) :
    HasTetrahedralFaceAssignment G.map ↔
      HasDualFaceKirchhoffV4Assignment G.map := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, ?_⟩
    exact (isDualFaceKirchhoff_iff_tetrahedralFacePattern G.map htri A).mpr hA
  · rintro ⟨A, hA⟩
    refine ⟨A, ?_⟩
    exact (isDualFaceKirchhoff_iff_tetrahedralFacePattern G.map htri A).mp hA

theorem hasTetrahedralFaceAssignment_iff_fourStateColorable
    {P : PortNetwork} (G : PortGenusZeroCombinatorialMap P)
    (htri : PortAllFacesTriangular G.map) :
    HasTetrahedralFaceAssignment G.map ↔
      PortFourStateColorable G.map.crossing := by
  rw [hasTetrahedralFaceAssignment_iff_dualFaceKirchhoff G htri]
  exact G.dualFaceKirchhoff_iff_colorable

theorem allTriangular_dualFaceKirchhoff_dualLoopFree
    {P : PortNetwork} (M : PortCombinatorialMap P)
    (htri : PortAllFacesTriangular M)
    (A : V4FlowAssignment M.crossing)
    (hdual : IsDualFaceKirchhoff A M.localRotation) :
    DualLoopFree M.localRotation M.crossing := by
  intro p hloop
  let F := faceCellOfPort M.localRotation M.crossing p
  have hp : p ∈ F.val := faceCellOfPort_mem M.localRotation M.crossing p
  have hsum : faceCellLabelSum A M.localRotation F = 0 :=
    ((isFaceCellKirchhoff_iff_dualFaceKirchhoff (R := M.localRotation) A).mpr hdual F)
  apply conserved_triangular_face_no_crossing_pair A F (htri F) hsum p hp
  exact hloop

def tetraStampColor {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (c : TrominoState) {r s : Fin P.regionCount}
    (W : FlowRegionWalk A.toFlowCrossing r s) : TrominoState :=
  c + regionWalkXor W

theorem tetraStampColor_append {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (c : TrominoState)
    {r s t : Fin P.regionCount}
    (W₁ : FlowRegionWalk A.toFlowCrossing r s)
    (W₂ : FlowRegionWalk A.toFlowCrossing s t) :
    tetraStampColor A c (FlowRegionWalk.append W₁ W₂) =
      tetraStampColor A (tetraStampColor A c W₁) W₂ := by
  simp only [tetraStampColor]
  rw [regionWalkXor_append W₁ W₂]
  ac_rfl

theorem tetraStampColor_closed_of_zeroHolonomy
    {P : PortNetwork} {C : PortCrossing P}
    (A : V4FlowAssignment C) (c : TrominoState)
    {r : Fin P.regionCount} (W : ClosedRegionWalk A.toFlowCrossing r)
    (hzero : IsZeroHolonomyV4Tension A) :
    tetraStampColor A c W = c := by
  simp [tetraStampColor, hzero r W]

end DkMath.Tromino
