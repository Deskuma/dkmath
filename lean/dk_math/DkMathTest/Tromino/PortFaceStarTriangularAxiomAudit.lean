/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortTriangulationReduction

/-!
# Face-star triangular dynamics and axiom audit

This audit checks the region classifications, cyclic rotation system, exact
face-step cycle, primitive return, canonical triangle, and face-cell size.
-/

namespace DkMathTest.Tromino

open DkMath.Tromino

/-! ## Region classification and cyclicity -/

#check faceStar_port_at_oldRegion_cases
#check faceStar_port_at_centerRegion_cases
#check faceStarRotate_radialOld_iterate_even
#check faceStarRotate_radialOld_iterate_odd
#check faceStar_oldRegion_cyclic
#check oldFace_backward_reachable
#check faceStar_centerRegion_cyclic
#check faceStarRotationSystem

/-! ## Exact face dynamics -/

#check faceStarFaceStep_oldEdge
#check faceStarFaceStep_radialOld
#check faceStarFaceStep_radialCenter
#check faceStarFaceStep_oldEdge_return
#check faceStarFaceStep_radialOld_return
#check faceStarFaceStep_radialCenter_return
#check faceStarFaceStep_oldEdge_no_return_one
#check faceStarFaceStep_oldEdge_no_return_two
#check faceStarFaceStep_radialOld_no_return_one
#check faceStarFaceStep_radialOld_no_return_two
#check faceStarFaceStep_radialCenter_no_return_one
#check faceStarFaceStep_radialCenter_no_return_two
#check firstPortFaceReturn_faceStar_oldEdge
#check firstPortFaceReturn_faceStar_radialOld
#check firstPortFaceReturn_faceStar_radialCenter

/-! ## Canonical triangles and face cells -/

#check faceStarTriangle
#check faceStarTriangle_card
#check faceStarTriangle_eq_oldEdge_orbit
#check faceStarTriangle_eq_radialOld_orbit
#check faceStarTriangle_eq_radialCenter_orbit
#check faceStarTriangle_coverage
#check faceStar_everyFaceCell_card_three

/-! ## Axiom dependencies of the central declarations -/

#print axioms faceStarRotationSystem
#print axioms faceStar_oldRegion_cyclic
#print axioms faceStarFaceStep_oldEdge
#print axioms firstPortFaceReturn_faceStar_oldEdge
#print axioms faceStar_everyFaceCell_card_three

end DkMathTest.Tromino
