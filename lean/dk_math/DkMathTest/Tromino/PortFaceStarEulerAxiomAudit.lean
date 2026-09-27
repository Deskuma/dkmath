/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarEuler
import DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
import DkMathTest.Tromino.PortDualityKernelAxiomAudit

/-!
# Face-star count and Euler/genus axiom audit

This audit checks the port/face-cell equivalence, exact count identities,
Euler preservation, and genus-zero packaging.
-/

namespace DkMathTest.Tromino

open DkMath.Tromino
open DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
open DkMathTest.Tromino.PortDualityKernelAxiomAudit

/-! ## Port and face-cell structure -/

#check faceStar_portCount
#check faceStarOldPortToFaceCell
#check faceStarOldPortToFaceCell_val
#check faceStarTriangle_oldEdge_mem
#check faceStarTriangle_oldEdge_unique
#check faceStarOldPortToFaceCell_injective
#check faceStarOldPortToFaceCell_surjective
#check faceStarFaceCellEquiv

/-! ## Count identities and Euler characteristic -/

#check faceStar_faceCount
#check faceStar_vertexCount
#check two_mul_edgeCount_eq_portCount
#check faceStar_edgeCount
#check faceStar_edgeCount_eq_add_portCount
#check portCombinatorialMap_eulerCharacteristic_eq
#check faceStar_eulerCharacteristic

/-! ## Genus preservation and genus-zero package -/

#check faceStar_preserves_combinatorial_genus
#check faceStar_combinatorial_genus_iff
#check faceStarGenusZero
#check faceStarGenusZero_map
#check faceStarGenusZero_vertexCount
#check faceStarGenusZero_edgeCount
#check faceStarGenusZero_faceCount
#check faceStarGenusZero_portCount
#check faceStarGenusZero_eulerCharacteristic

/-! ## Axiom dependencies of the central declarations -/

#print axioms faceStarFaceCellEquiv
#print axioms faceStar_faceCount
#print axioms faceStar_edgeCount
#print axioms faceStar_eulerCharacteristic
#print axioms faceStarGenusZero

/-! ## Existing fixture regressions -/

example : trianglePortMap.vertexCount = 3 := by decide
example : trianglePortMap.edgeCount = 3 := by decide
example : trianglePortMap.faceCount = 2 := by exact triangle_faceCount
example : trianglePortMap.portCount = 6 := by decide
example : trianglePortMap.eulerCharacteristic = 2 := by
  exact triangle_eulerCharacteristic

example (I : PortFaceStarIndexing trianglePortMap) :
    (faceStarCombinatorialMap trianglePortMap I).vertexCount = 5 := by
  rw [faceStar_vertexCount, show trianglePortMap.vertexCount = 3 by decide,
    show trianglePortMap.faceCount = 2 by exact triangle_faceCount]

example (I : PortFaceStarIndexing trianglePortMap) :
    (faceStarCombinatorialMap trianglePortMap I).edgeCount = 9 := by
  rw [faceStar_edgeCount, show trianglePortMap.edgeCount = 3 by decide]

example (I : PortFaceStarIndexing trianglePortMap) :
    (faceStarCombinatorialMap trianglePortMap I).faceCount = 6 := by
  rw [faceStar_faceCount, show trianglePortMap.portCount = 6 by decide]

example (I : PortFaceStarIndexing trianglePortMap) :
    (faceStarCombinatorialMap trianglePortMap I).portCount = 18 := by
  rw [faceStar_portCount, show trianglePortMap.portCount = 6 by decide]

example (I : PortFaceStarIndexing trianglePortMap) :
    (faceStarCombinatorialMap trianglePortMap I).eulerCharacteristic = 2 := by
  rw [faceStar_eulerCharacteristic]
  exact triangle_eulerCharacteristic

example : triangleDualMap.vertexCount = 2 := by decide
example : triangleDualMap.edgeCount = 3 := by decide
example : triangleDualMap.faceCount = 3 := by exact triangleDual_faceCount
example : triangleDualMap.portCount = 6 := by decide
example : triangleDualMap.eulerCharacteristic = 2 := by
  exact triangleDual_eulerCharacteristic

example (I : PortFaceStarIndexing triangleDualMap) :
    (faceStarCombinatorialMap triangleDualMap I).vertexCount = 5 := by
  rw [faceStar_vertexCount, show triangleDualMap.vertexCount = 2 by decide,
    show triangleDualMap.faceCount = 3 by exact triangleDual_faceCount]

example (I : PortFaceStarIndexing triangleDualMap) :
    (faceStarCombinatorialMap triangleDualMap I).edgeCount = 9 := by
  rw [faceStar_edgeCount, show triangleDualMap.edgeCount = 3 by decide]

example (I : PortFaceStarIndexing triangleDualMap) :
    (faceStarCombinatorialMap triangleDualMap I).faceCount = 6 := by
  rw [faceStar_faceCount, show triangleDualMap.portCount = 6 by decide]

example (I : PortFaceStarIndexing triangleDualMap) :
    (faceStarCombinatorialMap triangleDualMap I).portCount = 18 := by
  rw [faceStar_portCount, show triangleDualMap.portCount = 6 by decide]

example (I : PortFaceStarIndexing triangleDualMap) :
    (faceStarCombinatorialMap triangleDualMap I).eulerCharacteristic = 2 := by
  rw [faceStar_eulerCharacteristic]
  exact triangleDual_eulerCharacteristic

end DkMathTest.Tromino
