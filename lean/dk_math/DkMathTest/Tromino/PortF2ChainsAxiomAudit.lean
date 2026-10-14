/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortF2Chains
import DkMathTest.Tromino.PortDualityKernelAxiomAudit

#print "file: DkMathTest.Tromino.PortF2ChainsAxiomAudit"

namespace DkMathTest.Tromino.PortF2ChainsAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
open DkMathTest.Tromino.PortDualityKernelAxiomAudit

example : Fintype.card (PortEdgeCell trianglePortCrossing) = 3 := by
  rw [PortEdgeCell_card]
  decide

example : Fintype.card (PortFaceCell trianglePortRotation trianglePortCrossing) = 2 := by
  rw [PortFaceCell_card]
  exact triangle_faceCount

example : Fintype.card (PortEdgeCell triangleDualCrossing) = 3 := by
  rw [PortEdgeCell_card]
  decide

example : Fintype.card (PortFaceCell triangleDualRotation triangleDualCrossing) = 3 := by
  rw [PortFaceCell_card]
  exact triangleDual_faceCount

example : Module.finrank PortF2 (PortVertexChain trianglePortNetwork) = 3 := by
  simpa [trianglePortNetwork] using (finrank_portVertexChain (P := trianglePortNetwork))

example : Module.finrank PortF2 (PortEdgeChain trianglePortCrossing) = 3 := by
  rw [finrank_portEdgeChain]
  decide

example : Module.finrank PortF2
    (PortFaceChain trianglePortRotation trianglePortCrossing) = 2 := by
  rw [finrank_portFaceChain]
  exact triangle_faceCount

example : Module.finrank PortF2 (PortVertexChain triangleDualNetwork) = 2 := by
  simpa [triangleDualNetwork] using (finrank_portVertexChain (P := triangleDualNetwork))

example : Module.finrank PortF2 (PortEdgeChain triangleDualCrossing) = 3 := by
  rw [finrank_portEdgeChain]
  decide

example : Module.finrank PortF2
    (PortFaceChain triangleDualRotation triangleDualCrossing) = 3 := by
  rw [finrank_portFaceChain]
  exact triangleDual_faceCount

example : edgeCellOfPort trianglePortCrossing t00 =
    edgeCellOfPort trianglePortCrossing t21 := by
  rw [← triangle_face_t00]
  exact (edgeCellOfPort_cross trianglePortCrossing t00).symm

example : faceCellOfPort trianglePortRotation trianglePortCrossing t00 =
    faceCellOfPort trianglePortRotation trianglePortCrossing t20 := by
  apply Subtype.ext
  change portFaceOrbit trianglePortRotation trianglePortCrossing t00 =
    portFaceOrbit trianglePortRotation trianglePortCrossing t20
  exact triangle_faceOrbit_t00.trans triangle_faceOrbit_t20.symm

example : portWalkEdgeChain (PortRegionWalk.nil trianglePortCrossing (⟨0, by decide⟩)) = 0 := by
  exact portWalkEdgeChain_nil trianglePortCrossing _

example : portBoundary1 trianglePortCrossing
    (portWalkEdgeChain (PortRegionWalk.singleton trianglePortCrossing t00)) =
      endpointVertexChain t00.1 (trianglePortCrossing.cross t00).1 := by
  exact portBoundary1_portWalkEdgeChain (PortRegionWalk.singleton trianglePortCrossing t00)

example : portBoundary1 trianglePortCrossing
    (faceBoundaryEdgeChain
      (faceCellOfPort trianglePortRotation trianglePortCrossing t00)) = 0 := by
  exact faceBoundaryEdgeChain_cycle trianglePortRotation trianglePortCrossing _

example : (portBoundary1 trianglePortCrossing).comp
    (portBoundary2 trianglePortRotation trianglePortCrossing) = 0 := by
  exact portBoundary1_boundary2 trianglePortRotation trianglePortCrossing

example : PortFaceBoundarySpace trianglePortRotation trianglePortCrossing ≤
    PortCycleSpace trianglePortCrossing := by
  exact faceBoundarySpace_le_cycleSpace trianglePortRotation trianglePortCrossing

example : portBoundary2 trianglePortRotation trianglePortCrossing 0 = 0 := by
  exact portBoundary2_zero trianglePortRotation trianglePortCrossing

#print axioms DkMath.Tromino.portBoundary1_boundary2
#print axioms DkMath.Tromino.faceBoundarySpace_le_cycleSpace

end DkMathTest.Tromino.PortF2ChainsAxiomAudit
