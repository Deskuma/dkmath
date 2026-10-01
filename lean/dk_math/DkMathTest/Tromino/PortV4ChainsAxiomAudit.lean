import DkMath.Tromino.PortV4Chains
import DkMathTest.Tromino.LocalFrameEquivAxiomAudit
import DkMathTest.Tromino.PortDualityKernelAxiomAudit

namespace DkMathTest.Tromino.PortV4ChainsAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.LocalFrameEquivAxiomAudit
open DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
open DkMathTest.Tromino.PortDualityKernelAxiomAudit

example (x : PortV4EdgeChain trianglePortCrossing) (E : PortEdgeCell trianglePortCrossing) :
    (v4EdgeChainEquiv x).1 E = (x E).1 :=
  v4EdgeChainEquiv_fst x E

example (x : PortV4EdgeChain trianglePortCrossing) (E : PortEdgeCell trianglePortCrossing) :
    (v4EdgeChainEquiv x).2 E = (x E).2 :=
  v4EdgeChainEquiv_snd x E

example (x : PortV4FaceChain trianglePortRotation trianglePortCrossing)
    (F : PortFaceCell trianglePortRotation trianglePortCrossing) :
    (v4FaceChainEquiv x).1 F = (x F).1 :=
  v4FaceChainEquiv_fst x F

example (x : PortV4FaceChain trianglePortRotation trianglePortCrossing)
    (F : PortFaceCell trianglePortRotation trianglePortCrossing) :
    (v4FaceChainEquiv x).2 F = (x F).2 :=
  v4FaceChainEquiv_snd x F

example (x : PortV4EdgeChain trianglePortCrossing) :
    (v4VertexChainEquiv (portV4Boundary1 trianglePortCrossing x)).1 =
      portBoundary1 trianglePortCrossing (v4EdgeChainEquiv x).1 :=
  portV4Boundary1_fst trianglePortCrossing x

example (x : PortV4EdgeChain trianglePortCrossing) :
    (v4VertexChainEquiv (portV4Boundary1 trianglePortCrossing x)).2 =
      portBoundary1 trianglePortCrossing (v4EdgeChainEquiv x).2 :=
  portV4Boundary1_snd trianglePortCrossing x

example (y : PortV4FaceChain trianglePortRotation trianglePortCrossing) :
    (v4EdgeChainEquiv (portV4Boundary2 trianglePortRotation trianglePortCrossing y)).1 =
      portBoundary2 trianglePortRotation trianglePortCrossing (v4FaceChainEquiv y).1 :=
  portV4Boundary2_fst trianglePortRotation trianglePortCrossing y

example (y : PortV4FaceChain trianglePortRotation trianglePortCrossing) :
    (v4EdgeChainEquiv (portV4Boundary2 trianglePortRotation trianglePortCrossing y)).2 =
      portBoundary2 trianglePortRotation trianglePortCrossing (v4FaceChainEquiv y).2 :=
  portV4Boundary2_snd trianglePortRotation trianglePortCrossing y

example :
    (portV4Boundary1 trianglePortCrossing).comp
        (portV4Boundary2 trianglePortRotation trianglePortCrossing) = 0 :=
  portV4Boundary1_boundary2 trianglePortRotation trianglePortCrossing

example (x : PortV4EdgeChain trianglePortCrossing) :
    x ∈ PortV4CycleSpace trianglePortCrossing ↔
      (v4EdgeChainEquiv x).1 ∈ PortCycleSpace trianglePortCrossing ∧
        (v4EdgeChainEquiv x).2 ∈ PortCycleSpace trianglePortCrossing :=
  mem_portV4CycleSpace_iff trianglePortCrossing x

example :
    PortV4FaceBoundarySpace trianglePortRotation trianglePortCrossing ≤
      PortV4CycleSpace trianglePortCrossing :=
  portV4FaceBoundarySpace_le_cycleSpace trianglePortRotation trianglePortCrossing

example (A : V4FlowAssignment trianglePortCrossing)
    (r : Fin trianglePortNetwork.regionCount) :
    vertexKirchhoffSum A r = 0 ↔
      (vertexKirchhoffSum A r).1 = 0 ∧ (vertexKirchhoffSum A r).2 = 0 :=
  vertexKirchhoffSum_eq_zero_iff_coordinates A r

example : deltaA = ((1 : PortF2), 0) := deltaA_coordinates
example : deltaB = ((0 : PortF2), 1) := deltaB_coordinates
example : deltaC = ((1 : PortF2), 1) := deltaC_coordinates
example : deltaA + deltaB = deltaC := deltaA_add_deltaB_eq_deltaC
example : deltaA + deltaB + deltaC = 0 := deltaA_add_deltaB_add_deltaC_eq_zero

example :
    triangleDualAssignment.label d00 + triangleDualAssignment.label d01 +
      triangleDualAssignment.label d02 = 0 := by
  rcases triangleColoring_to_dual_labels with ⟨h0, h1, h2⟩
  rw [h0, h1, h2]
  decide

example :
    faceCellOfPort trianglePortRotation trianglePortCrossing t20 =
      faceCellOfPort trianglePortRotation trianglePortCrossing t00 := by
  apply faceCellOfPort_eq_of_mem
  rw [triangle_faceOrbit_t00]
  decide

example :
    portWalkEdgeChain
        (PortRegionWalk.reverse
          (portFaceBoundaryWalk trianglePortRotation trianglePortCrossing t00)) =
      portWalkEdgeChain
        (portFaceBoundaryWalk trianglePortRotation trianglePortCrossing t00) :=
  portWalkEdgeChain_reverse _

example :
    faceBoundaryEdgeChain
        (faceCellOfPort trianglePortRotation trianglePortCrossing t00) =
      (fun _ => (1 : PortF2)) := by
  funext E
  simp only [faceBoundaryEdgeChain, faceEdgeIncidence, faceCellOfPort]
  change ((portFaceOrbit trianglePortRotation trianglePortCrossing t00 ∩ E.val).card : PortF2) = 1
  fin_cases E <;> rw [triangle_faceOrbit_t00] <;> decide

example :
    faceBoundaryEdgeChain
        (faceCellOfPort trianglePortRotation trianglePortCrossing t01) =
      (fun _ => (1 : PortF2)) := by
  funext E
  simp only [faceBoundaryEdgeChain, faceEdgeIncidence, faceCellOfPort]
  change ((portFaceOrbit trianglePortRotation trianglePortCrossing t01 ∩ E.val).card : PortF2) = 1
  fin_cases E <;> rw [triangle_faceOrbit_t01] <;> decide

def dualEdgeD00 : PortEdgeCell triangleDualCrossing :=
  edgeCellOfPort triangleDualCrossing d00

def dualEdgeD10 : PortEdgeCell triangleDualCrossing :=
  edgeCellOfPort triangleDualCrossing d10

example :
    faceBoundaryEdgeChain
        (faceCellOfPort triangleDualRotation triangleDualCrossing d00) =
      (fun E => if E = dualEdgeD00 then 1 else
        if E = dualEdgeD10 then 1 else 0) := by
  have hface : portFaceOrbit triangleDualRotation triangleDualCrossing d00 =
      {d00, d10} := by
    rw [portFaceOrbit, triangleDual_firstReturn_d00]
    decide
  funext E
  simp only [faceBoundaryEdgeChain, faceEdgeIncidence, faceCellOfPort]
  change ((portFaceOrbit triangleDualRotation triangleDualCrossing d00 ∩ E.val).card : PortF2) = _
  fin_cases E <;> rw [hface] <;> decide

example :
    faceBoundaryEdgeChain
        (faceCellOfPort triangleDualRotation triangleDualCrossing d00) ≠ 0 := by
  have hface : portFaceOrbit triangleDualRotation triangleDualCrossing d00 =
      {d00, d10} := by
    rw [portFaceOrbit, triangleDual_firstReturn_d00]
    decide
  have hinc : faceBoundaryEdgeChain
      (faceCellOfPort triangleDualRotation triangleDualCrossing d00) dualEdgeD00 = 1 := by
    simp only [faceBoundaryEdgeChain, faceEdgeIncidence, faceCellOfPort, dualEdgeD00]
    change ((portFaceOrbit triangleDualRotation triangleDualCrossing d00 ∩
      (edgeCellOfPort triangleDualCrossing d00).val).card : PortF2) = 1
    rw [hface]
    decide
  intro h
  have hz := congrFun h dualEdgeD00
  rw [hinc] at hz
  exact (by decide : (1 : PortF2) ≠ 0) hz

example :
    faceBoundaryEdgeChain
        (faceCellOfPort triangleDualRotation triangleDualCrossing d00) ≠
      faceBoundaryEdgeChain
        (faceCellOfPort triangleDualRotation triangleDualCrossing d01) := by
  have hface0 : portFaceOrbit triangleDualRotation triangleDualCrossing d00 =
      {d00, d10} := by
    rw [portFaceOrbit, triangleDual_firstReturn_d00]
    decide
  have hface1 : portFaceOrbit triangleDualRotation triangleDualCrossing d01 =
      {d01, d12} := by
    rw [portFaceOrbit, triangleDual_firstReturn_d01]
    decide
  have h0 : faceBoundaryEdgeChain
      (faceCellOfPort triangleDualRotation triangleDualCrossing d00) dualEdgeD10 = 1 := by
    simp only [faceBoundaryEdgeChain, faceEdgeIncidence, faceCellOfPort, dualEdgeD10]
    change ((portFaceOrbit triangleDualRotation triangleDualCrossing d00 ∩
      (edgeCellOfPort triangleDualCrossing d10).val).card : PortF2) = 1
    rw [hface0]
    decide
  have h1 : faceBoundaryEdgeChain
      (faceCellOfPort triangleDualRotation triangleDualCrossing d01) dualEdgeD10 = 0 := by
    simp only [faceBoundaryEdgeChain, faceEdgeIncidence, faceCellOfPort, dualEdgeD10]
    change ((portFaceOrbit triangleDualRotation triangleDualCrossing d01 ∩
      (edgeCellOfPort triangleDualCrossing d10).val).card : PortF2) = 0
    rw [hface1]
    decide
  intro h
  have hz := congrFun h dualEdgeD10
  rw [h0, h1] at hz
  exact (by decide : (1 : PortF2) ≠ 0) hz

#print axioms DkMath.Tromino.portV4Boundary1_boundary2
#print axioms DkMath.Tromino.mem_portV4CycleSpace_iff

end DkMathTest.Tromino.PortV4ChainsAxiomAudit
