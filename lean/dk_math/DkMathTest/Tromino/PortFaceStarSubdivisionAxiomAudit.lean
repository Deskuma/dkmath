/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortTriangulationReduction

/-!
# Face-star subdivision API and axiom audit

This audit checks the verified indexing, semantic descriptor, region split,
actual-port constructor surface, and semantic crossing/rotation layer.
-/

namespace DkMathTest.Tromino

open DkMath.Tromino

/-! ## Public declarations -/

#check exists_portFaceStarIndexing
#check FaceStarPortDesc.card
#check oldRegion_injective
#check faceCenterRegion_injective
#check oldRegion_ne_faceCenterRegion
#check faceStarOldEdgePort
#check faceStarRadialOldPort
#check faceStarRadialCenterPort
#check faceStar_descriptor_card
#check faceStar_regionCount_eq

/-! ## Semantic crossing and rotation -/

#check faceStarCrossDesc
#check faceStarCrossDesc_involutive
#check faceStarRotateDesc
#check faceStarRotateDescEquiv

/-! ## Axiom dependencies -/

#print axioms exists_portFaceStarIndexing
#print axioms FaceStarPortDesc.card
#print axioms faceStarCrossDesc_involutive
#print axioms faceStarRotateDescEquiv

end DkMathTest.Tromino
