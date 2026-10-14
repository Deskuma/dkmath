/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarMap

/-!
# Face-star connectivity and map-packaging axiom audit

This audit checks the region decomposition, lifted walks, attachments,
connectivity, packaged map fields, and packaged triangular face theorem.
-/

namespace DkMathTest.Tromino

open DkMath.Tromino

/-! ## Region decomposition and lifted walks -/

#check faceStar_region_cases
#check faceStar_oldWalk_valid
#check liftFaceStarOldWalk
#check liftFaceStarOldWalk_edges
#check faceStar_oldRegion_reachable
#check faceStar_oldRegions_connected

/-! ## Face-center attachment and global connectivity -/

#check faceStar_faceCell_nonempty
#check faceStar_faceCell_representative
#check faceStar_center_attachment
#check faceStar_region_reaches_old
#check faceStar_regionConnected
#check faceStar_nonemptyRegions

/-! ## Packaged map and triangular face cells -/

#check faceStarCombinatorialMap
#check faceStarCombinatorialMap_crossing
#check faceStarCombinatorialMap_rotation
#check faceStarCombinatorialMap_localRotation
#check faceStarCombinatorialMap_everyFaceCell_card_three

/-! ## Axiom dependencies of the central declarations -/

#print axioms liftFaceStarOldWalk
#print axioms faceStar_center_attachment
#print axioms faceStar_regionConnected
#print axioms faceStarCombinatorialMap
#print axioms faceStarCombinatorialMap_everyFaceCell_card_three

end DkMathTest.Tromino
