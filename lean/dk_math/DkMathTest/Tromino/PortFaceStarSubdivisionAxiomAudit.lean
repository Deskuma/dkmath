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
#check faceStarPortEquiv
#check faceStarPortEncode
#check faceStarPortDecode
#check faceStarPortDecode_encode
#check faceStarPortEncode_decode
#check faceStarDescSource
#check faceStarPortDecode_source

/-! ## Actual-port calibration -/

#check faceStarPortEncode_oldEdge
#check faceStarPortEncode_radialOld
#check faceStarPortEncode_radialCenter
#check faceStarPortDecode_oldEdgePort
#check faceStarPortDecode_radialOldPort
#check faceStarPortDecode_radialCenterPort
#check faceStarCross_oldEdge
#check faceStarCross_radialOld
#check faceStarCross_radialCenter
#check faceStarRotate_radialOld
#check faceStarRotate_oldEdge
#check faceStarRotate_radialCenter

/-! ## Semantic crossing and rotation -/

#check faceStarCrossDesc
#check faceStarCrossDesc_involutive
#check faceStarRotateDesc
#check faceStarRotateDescEquiv
#check faceStarCrossing
#check faceStarLocalRotation
#check faceStarCrossing_encode
#check faceStarLocalRotation_encode

/-! ## Axiom dependencies -/

#print axioms exists_portFaceStarIndexing
#print axioms FaceStarPortDesc.card
#print axioms faceStarCrossDesc_involutive
#print axioms faceStarRotateDescEquiv
#print axioms faceStarPortDecode_encode
#print axioms faceStarPortEncode_decode
#print axioms faceStarPortDecode_source
#print axioms faceStarPortEncode_oldEdge
#print axioms faceStarPortEncode_radialOld
#print axioms faceStarPortEncode_radialCenter
#print axioms faceStarCross_oldEdge
#print axioms faceStarRotate_radialOld
#print axioms faceStarCrossing
#print axioms faceStarLocalRotation
#print axioms faceStarCrossing_encode
#print axioms faceStarLocalRotation_encode

end DkMathTest.Tromino
