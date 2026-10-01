/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortF2Exactness
import DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
import DkMathTest.Tromino.PortDualityKernelAxiomAudit

#print "file: DkMathTest.Tromino.PortF2ExactnessAxiomAudit"

namespace DkMathTest.Tromino.PortF2ExactnessAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
open DkMathTest.Tromino.PortDualityKernelAxiomAudit

def triangleGenusZero' : PortGenusZeroCombinatorialMap trianglePortNetwork where
  map := trianglePortMap
  genusZero := by
    rw [portCombinatorialGenus_zero_iff]
    exact triangle_eulerCharacteristic

def triangleDualGenusZero' : PortGenusZeroCombinatorialMap triangleDualNetwork where
  map := triangleDualMap
  genusZero := by
    rw [portCombinatorialGenus_zero_iff]
    exact triangleDual_eulerCharacteristic

example : Module.finrank PortF2 (PortVertexChain trianglePortNetwork) = 3 := by
  rw [finrank_portVertexChain]
  rfl

example : Module.finrank PortF2 (PortEdgeChain trianglePortCrossing) = 3 := by
  rw [finrank_portEdgeChain]
  decide

example : Module.finrank PortF2
    (PortFaceChain trianglePortRotation trianglePortCrossing) = 2 := by
  rw [finrank_portFaceChain]
  exact triangle_faceCount

example : Module.finrank PortF2 (PortCycleSpace trianglePortCrossing) = 1 := by
  change Module.finrank PortF2 (PortCycleSpace trianglePortMap.crossing) = 1
  rw [finrank_portCycleSpace trianglePortMap]
  decide

example : Module.finrank PortF2
    (PortFaceBoundarySpace trianglePortRotation trianglePortCrossing) = 1 := by
  change Module.finrank PortF2
    (PortFaceBoundarySpace triangleGenusZero'.map.localRotation triangleGenusZero'.map.crossing) = 1
  have h := finrank_portFaceBoundarySpace triangleGenusZero'
  change Module.finrank PortF2
      (PortFaceBoundarySpace trianglePortMap.localRotation trianglePortMap.crossing) =
    portFaceCount trianglePortMap.localRotation trianglePortMap.crossing - 1 at h
  rw [show portFaceCount trianglePortMap.localRotation trianglePortMap.crossing = 2 by exact triangle_faceCount] at h
  norm_num at h
  exact h

example :
    PortFaceBoundarySpace trianglePortRotation trianglePortCrossing =
      PortCycleSpace trianglePortCrossing :=
  portGenusZero_faceBoundarySpace_eq_cycleSpace triangleGenusZero'

example : Module.finrank PortF2 (PortVertexChain triangleDualNetwork) = 2 := by
  rw [finrank_portVertexChain]
  rfl

example : Module.finrank PortF2 (PortEdgeChain triangleDualCrossing) = 3 := by
  rw [finrank_portEdgeChain]
  decide

example : Module.finrank PortF2
    (PortFaceChain triangleDualRotation triangleDualCrossing) = 3 := by
  rw [finrank_portFaceChain]
  exact triangleDual_faceCount

example : Module.finrank PortF2 (PortCycleSpace triangleDualCrossing) = 2 := by
  change Module.finrank PortF2 (PortCycleSpace triangleDualMap.crossing) = 2
  rw [finrank_portCycleSpace triangleDualMap]
  decide

example : Module.finrank PortF2
    (PortFaceBoundarySpace triangleDualRotation triangleDualCrossing) = 2 := by
  change Module.finrank PortF2
    (PortFaceBoundarySpace triangleDualGenusZero'.map.localRotation triangleDualGenusZero'.map.crossing) = 2
  have h := finrank_portFaceBoundarySpace triangleDualGenusZero'
  change Module.finrank PortF2
      (PortFaceBoundarySpace triangleDualMap.localRotation triangleDualMap.crossing) =
    portFaceCount triangleDualMap.localRotation triangleDualMap.crossing - 1 at h
  rw [show portFaceCount triangleDualMap.localRotation triangleDualMap.crossing = 3 by exact triangleDual_faceCount] at h
  norm_num at h
  exact h

example :
    PortFaceBoundarySpace triangleDualRotation triangleDualCrossing =
      PortCycleSpace triangleDualCrossing :=
  portGenusZero_faceBoundarySpace_eq_cycleSpace triangleDualGenusZero'

def triangleClosedWalk :
    PortRegionWalk trianglePortCrossing
      (⟨0, by decide⟩) (⟨0, by decide⟩) :=
  PortRegionWalk.append
    (PortRegionWalk.singleton trianglePortCrossing t00)
    (PortRegionWalk.append
      (PortRegionWalk.singleton trianglePortCrossing t20)
      (PortRegionWalk.singleton trianglePortCrossing t10))

example :
    portWalkEdgeChain triangleClosedWalk ∈
      PortFaceBoundarySpace trianglePortRotation trianglePortCrossing :=
  portGenusZero_closed_portWalkEdgeChain_mem_faceBoundarySpace
    triangleGenusZero' triangleClosedWalk

#print axioms DkMath.Tromino.portGenusZero_faceBoundarySpace_eq_cycleSpace
#print axioms DkMath.Tromino.portGenusZero_closed_portWalkEdgeChain_mem_faceBoundarySpace

end DkMathTest.Tromino.PortF2ExactnessAxiomAudit
