/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortGenusZeroHolonomy
import DkMathTest.Tromino.PortF2ExactnessAxiomAudit

#print "file: DkMathTest.Tromino.PortGenusZeroHolonomyAxiomAudit"

namespace DkMathTest.Tromino.PortGenusZeroHolonomyAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortF2ExactnessAxiomAudit
open DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
open DkMathTest.Tromino.PortDualityKernelAxiomAudit
open DkMathTest.Tromino.PortTensionColoringAxiomAudit

def triangleGenusZeroHolonomy :
    PortGenusZeroCombinatorialMap trianglePortNetwork where
  map := trianglePortMap
  genusZero := by
    rw [portCombinatorialGenus_zero_iff]
    exact triangle_eulerCharacteristic

def triangleColoringAssignment :
    V4FlowAssignment trianglePortCrossing :=
  coloringToV4Assignment triangleColoring

def triangleClosedWalk :
    PortRegionWalk trianglePortCrossing
      (⟨0, by decide⟩) (⟨0, by decide⟩) :=
  PortRegionWalk.append
    (PortRegionWalk.singleton trianglePortCrossing t00)
    (PortRegionWalk.append
      (PortRegionWalk.singleton trianglePortCrossing t20)
      (PortRegionWalk.singleton trianglePortCrossing t10))

example (p : PortNetworkPort trianglePortNetwork) :
    assignmentEdgeLabel triangleColoringAssignment
      (edgeCellOfPort trianglePortCrossing p) =
        triangleColoringAssignment.label p :=
  assignmentEdgeLabel_edgeCellOfPort triangleColoringAssignment p

example (p : PortNetworkPort trianglePortNetwork) :
    assignmentEdgeLabel triangleColoringAssignment
      (edgeCellOfPort trianglePortCrossing (trianglePortCrossing.cross p)) =
        triangleColoringAssignment.label p :=
  assignmentEdgeLabel_edgeCellOfPort_cross triangleColoringAssignment p

example (p : PortNetworkPort trianglePortNetwork) :
    portEdgeLabelEval triangleColoringAssignment
        (fun E => if edgeCellOfPort trianglePortCrossing p = E then 1 else 0) =
      triangleColoringAssignment.label p :=
  portEdgeLabelEval_edgeBasis triangleColoringAssignment p

example :
    portEdgeLabelEval triangleColoringAssignment
        (fun E => walkEdgeCoeff trianglePortCrossing E [t00, t20, t10]) =
      ([t00, t20, t10].map triangleColoringAssignment.label).sum :=
  portEdgeLabelEval_walkEdgeCoeff triangleColoringAssignment [t00, t20, t10]

example :
    portEdgeLabelEval triangleColoringAssignment
        (portWalkEdgeChain triangleClosedWalk) =
      regionWalkXor (triangleClosedWalk.toFlowRegionWalk
        triangleColoringAssignment) :=
  portEdgeLabelEval_portWalkEdgeChain triangleColoringAssignment triangleClosedWalk

example :
    portEdgeLabelEval triangleColoringAssignment
        (portWalkEdgeChain (triangleClosedWalk.toFlowRegionWalk
          triangleColoringAssignment).toPortRegionWalk) =
      regionWalkXor (triangleClosedWalk.toFlowRegionWalk
        triangleColoringAssignment) :=
  portEdgeLabelEval_flowWalk triangleColoringAssignment
    (triangleClosedWalk.toFlowRegionWalk triangleColoringAssignment)

example (p : PortNetworkPort trianglePortNetwork) :
    faceCellLabelSum triangleColoringAssignment trianglePortRotation
        (faceCellOfPort trianglePortRotation trianglePortCrossing p) =
      faceBoundaryLabelSum triangleColoringAssignment trianglePortRotation p :=
  faceCellLabelSum_faceCellOfPort triangleColoringAssignment p

example :
    IsFaceCellKirchhoff triangleColoringAssignment trianglePortRotation ↔
      IsDualFaceKirchhoff triangleColoringAssignment trianglePortRotation :=
  isFaceCellKirchhoff_iff_dualFaceKirchhoff triangleColoringAssignment

example (y : PortFaceChain trianglePortRotation trianglePortCrossing) :
    portEdgeLabelEval triangleColoringAssignment
        (portBoundary2 trianglePortRotation trianglePortCrossing y) =
      ∑ F : PortFaceCell trianglePortRotation trianglePortCrossing,
        y F • faceCellLabelSum triangleColoringAssignment trianglePortRotation F :=
  portEdgeLabelEval_boundary2 triangleColoringAssignment y

theorem triangleColoringAssignment_dualFace :
    IsDualFaceKirchhoff triangleColoringAssignment trianglePortRotation := by
  exact tension_implies_dualFaceKirchhoff triangleColoringAssignment
    trianglePortRotation (coloringToV4Assignment_isZeroHolonomy triangleColoring)

example (y : PortFaceChain trianglePortRotation trianglePortCrossing) :
    portEdgeLabelEval triangleColoringAssignment
        (portBoundary2 trianglePortRotation trianglePortCrossing y) = 0 :=
  portEdgeLabelEval_boundary2_eq_zero_of_dualFaceKirchhoff
    triangleColoringAssignment triangleColoringAssignment_dualFace y

example :
    regionWalkXor (triangleClosedWalk.toFlowRegionWalk
      triangleColoringAssignment) = 0 :=
  portGenusZero_closedWalk_xor_eq_zero_of_dualFaceKirchhoff
    triangleGenusZeroHolonomy triangleColoringAssignment
    triangleColoringAssignment_dualFace triangleClosedWalk

example :
    IsZeroHolonomyV4Tension triangleColoringAssignment :=
  portGenusZero_zeroHolonomy_of_dualFaceKirchhoff
    triangleGenusZeroHolonomy triangleColoringAssignment
    triangleColoringAssignment_dualFace

example :
    IsDualFaceKirchhoff triangleColoringAssignment trianglePortRotation ↔
      IsZeroHolonomyV4Tension triangleColoringAssignment :=
  portGenusZero_dualFaceKirchhoff_iff_zeroHolonomy
    triangleGenusZeroHolonomy triangleColoringAssignment

example :
    ∃ K : (portRegionSimpleGraph trianglePortCrossing).Coloring TrominoState,
      ∀ p, (coloringToV4Assignment K).label p =
        triangleColoringAssignment.label p :=
  exists_portColoring_of_dualFaceKirchhoff
    triangleGenusZeroHolonomy triangleColoringAssignment
    triangleColoringAssignment_dualFace

example :
    HasDualFaceKirchhoffV4Assignment triangleGenusZeroHolonomy.map ↔
      PortFourStateColorable triangleGenusZeroHolonomy.map.crossing :=
  triangleGenusZeroHolonomy.dualFaceKirchhoff_iff_colorable

example :
    PortGenusZeroDualFaceKirchhoffTarget ↔
      PortGenusZeroFourColorTarget :=
  portGenusZeroDualFaceKirchhoffTarget_iff_fourColorTarget

example : IsKirchhoffV4Flow triangleAllDeltaA :=
  triangle_kirchhoff_not_tension.1

example : ¬ IsDualFaceKirchhoff triangleAllDeltaA trianglePortRotation := by
  intro hdual
  exact triangleAllDeltaA_not_tension
    (portGenusZero_zeroHolonomy_of_dualFaceKirchhoff
      triangleGenusZeroHolonomy triangleAllDeltaA hdual)

example :
    PortGenusZeroDualFaceKirchhoffTarget =
      PortGenusZeroDualFaceKirchhoffTarget := rfl

#print axioms DkMath.Tromino.portGenusZero_closedWalk_xor_eq_zero_of_dualFaceKirchhoff
#print axioms DkMath.Tromino.portGenusZero_zeroHolonomy_of_dualFaceKirchhoff
#print axioms DkMath.Tromino.portGenusZero_dualFaceKirchhoff_iff_zeroHolonomy
#print axioms DkMath.Tromino.exists_portColoring_of_dualFaceKirchhoff
#print axioms DkMath.Tromino.portGenusZeroDualFaceKirchhoffTarget_iff_fourColorTarget

end DkMathTest.Tromino.PortGenusZeroHolonomyAxiomAudit
