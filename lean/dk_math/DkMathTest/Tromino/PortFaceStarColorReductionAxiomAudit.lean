/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarColorReduction

#print "file: DkMathTest.Tromino.PortFaceStarColorReductionAxiomAudit"

/-!
# Face-star coloring restriction axiom audit

This audit checks the packaged triangular map, old-region adjacency embedding,
coloring pullback, and the one-way tetrahedral reduction.
-/

namespace DkMathTest.Tromino

open DkMath.Tromino

/-! ## Packaged triangulation and old-edge calibration -/

#check faceStar_allFacesTriangular
#check faceStarGenusZero_allFacesTriangular
#check faceStar_oldEdge_source
#check faceStar_oldEdge_target

/-! ## Old-region adjacency and coloring restriction -/

#check faceStarOldRegionEmbedding
#check faceStarOldRegionEmbedding_injective
#check faceStar_oldAdjacency_of_port
#check faceStar_oldAdjacency
#check faceStarRestrictColoring
#check faceStarRestrictColoring_apply
#check faceStarRestrictColoring_edge_ne

/-! ## Colorability and tetrahedral consequences -/

#check faceStar_colorable_imp_original
#check faceStarGenusZero_colorable_imp_original
#check faceStar_tetrahedral_iff_colorable
#check faceStar_tetrahedral_imp_original_colorable

/-! ## Axiom dependencies of the central declarations -/

#print axioms faceStar_allFacesTriangular
#print axioms faceStar_oldAdjacency
#print axioms faceStarRestrictColoring
#print axioms faceStar_colorable_imp_original
#print axioms faceStar_tetrahedral_imp_original_colorable

end DkMathTest.Tromino
