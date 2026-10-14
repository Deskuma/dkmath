/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortTriangularTetrahedral
import DkMathTest.Tromino.PortGenusZeroHolonomyAxiomAudit

#print "file: DkMathTest.Tromino.PortTriangularTetrahedralAxiomAudit"

namespace DkMathTest.Tromino.PortTriangularTetrahedralAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortGenusZeroHolonomyAxiomAudit
open DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
open DkMathTest.Tromino.PortDualityKernelAxiomAudit

theorem triangleAllFacesTriangular : PortAllFacesTriangular trianglePortMap := by
  intro F
  change F.val.card = 3
  rcases (portFaceOrbits_mem_iff trianglePortRotation trianglePortCrossing F.val).mp
      F.property with ⟨p, hp⟩
  have hcardA : triangleFaceOrbitA.card = 3 := by decide
  have hcardB : triangleFaceOrbitB.card = 3 := by decide
  rw [hp]
  fin_cases p
  · simpa [t00, trianglePort] using
      (congrArg Finset.card triangle_faceOrbit_t00).trans hcardA
  · simpa [t01, trianglePort] using
      (congrArg Finset.card triangle_faceOrbit_t01).trans hcardB
  · simpa [t10, trianglePort] using
      (congrArg Finset.card triangle_faceOrbit_t10).trans hcardA
  · simpa [t11, trianglePort] using
      (congrArg Finset.card triangle_faceOrbit_t11).trans hcardB
  · simpa [t20, trianglePort] using
      (congrArg Finset.card triangle_faceOrbit_t20).trans hcardA
  · simpa [t21, trianglePort] using
      (congrArg Finset.card triangle_faceOrbit_t21).trans hcardB

example : IsTriangularPortFace
    (faceCellOfPort trianglePortRotation trianglePortCrossing t00) := by
  change IsTriangularPortFace
    (faceCellOfPort trianglePortMap.localRotation trianglePortMap.crossing t00)
  exact triangleAllFacesTriangular _

example :
    facePortLabelSet triangleColoringAssignment
      (faceCellOfPort trianglePortRotation trianglePortCrossing t00) =
      ({deltaA, deltaB, deltaC} : Finset TrominoState) := by
  apply (triangular_faceLabelSet_iff_faceCellLabelSum_zero
    triangleColoringAssignment
    (faceCellOfPort trianglePortRotation trianglePortCrossing t00)
    (triangleAllFacesTriangular _)).mp
  exact (isFaceCellKirchhoff_iff_dualFaceKirchhoff
    triangleColoringAssignment).mpr triangleColoringAssignment_dualFace _

example :
    faceCellLabelSum triangleColoringAssignment trianglePortRotation
      (faceCellOfPort trianglePortRotation trianglePortCrossing t00) = 0 := by
  exact (isFaceCellKirchhoff_iff_dualFaceKirchhoff
    triangleColoringAssignment).mpr triangleColoringAssignment_dualFace _

example :
    IsTetrahedralFacePattern triangleColoringAssignment
      (faceCellOfPort trianglePortRotation trianglePortCrossing t00) := by
  exact (isDualFaceKirchhoff_iff_tetrahedralFacePattern trianglePortMap
    triangleAllFacesTriangular triangleColoringAssignment).mp
    triangleColoringAssignment_dualFace _

example :
    ∀ F : PortFaceCell trianglePortRotation trianglePortCrossing,
      IsTetrahedralFacePattern triangleColoringAssignment F :=
  (isDualFaceKirchhoff_iff_tetrahedralFacePattern trianglePortMap
    triangleAllFacesTriangular triangleColoringAssignment).mp
    triangleColoringAssignment_dualFace

example : ¬ IsTetrahedralFacePattern triangleAllDeltaA
    (faceCellOfPort trianglePortRotation trianglePortCrossing t00) := by
  intro h
  have hset := h.2
  rw [facePortLabelSet]
    at hset
  have hFval :
      (faceCellOfPort trianglePortRotation trianglePortCrossing t00).val =
        triangleFaceOrbitA := by
    change portFaceOrbit trianglePortRotation trianglePortCrossing t00 =
      triangleFaceOrbitA
    exact triangle_faceOrbit_t00
  rw [hFval] at hset
  simp only [triangleAllDeltaA, triangleFaceOrbitA,
    Finset.image_insert, Finset.image_singleton,
    Finset.mem_singleton, Finset.insert_eq_of_mem] at hset
  exact (by decide : ({deltaA} : Finset TrominoState) ≠
    {deltaA, deltaB, deltaC}) hset

example :
    DualLoopFree trianglePortRotation trianglePortCrossing := by
  apply allTriangular_dualFaceKirchhoff_dualLoopFree
    trianglePortMap triangleAllFacesTriangular triangleColoringAssignment
  exact triangleColoringAssignment_dualFace

example :
    IsDualFaceKirchhoff triangleColoringAssignment trianglePortRotation ↔
      ∀ F : PortFaceCell trianglePortRotation trianglePortCrossing,
        IsTetrahedralFacePattern triangleColoringAssignment F :=
  isDualFaceKirchhoff_iff_tetrahedralFacePattern trianglePortMap
    triangleAllFacesTriangular triangleColoringAssignment

example : HasTetrahedralFaceAssignment triangleGenusZeroHolonomy.map ↔
    HasDualFaceKirchhoffV4Assignment triangleGenusZeroHolonomy.map :=
  hasTetrahedralFaceAssignment_iff_dualFaceKirchhoff
    triangleGenusZeroHolonomy triangleAllFacesTriangular

example : HasTetrahedralFaceAssignment triangleGenusZeroHolonomy.map ↔
    PortFourStateColorable triangleGenusZeroHolonomy.map.crossing :=
  hasTetrahedralFaceAssignment_iff_fourStateColorable
    triangleGenusZeroHolonomy triangleAllFacesTriangular

example (A : V4FlowAssignment trianglePortCrossing)
    (F : PortFaceCell trianglePortRotation trianglePortCrossing) :
    facePortLabelSet A F ⊆ ({deltaA, deltaB, deltaC} : Finset TrominoState) :=
  facePortLabelSet_subset_deltaSet A F

example (c : TrominoState) (ds : List TetraDirection)
    (h : (ds.map (fun d => d.1)).sum = 0) :
    tetraRollBottomList c ds = c := by
  rw [tetraRollBottomList_eq_add_sum, h, add_zero]

#print axioms DkMath.Tromino.triangular_faceLabelSet_iff_faceCellLabelSum_zero
#print axioms DkMath.Tromino.isDualFaceKirchhoff_iff_tetrahedralFacePattern
#print axioms DkMath.Tromino.hasTetrahedralFaceAssignment_iff_fourStateColorable
#print axioms DkMath.Tromino.allTriangular_dualFaceKirchhoff_dualLoopFree

end DkMathTest.Tromino.PortTriangularTetrahedralAxiomAudit
