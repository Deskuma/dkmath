/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarSubdivision

/-!
# Face-star triangulation reduction surface

This module is the public reduction surface for the verified face-star
carrier.  The crossing, rotation, face-orbit, and coloring theorems remain
separate from the finite indexing layer.
-/

#print "file: DkMath.Tromino.PortTriangulationReduction"

namespace DkMath.Tromino

/-! ## Public carrier facts -/

/-- The face-star descriptor contains three ports for every old port. -/
theorem faceStar_descriptor_card {P : PortNetwork} (M : PortCombinatorialMap P) :
    Fintype.card (FaceStarPortDesc M) = 3 * M.portCount :=
  FaceStarPortDesc.card M

/-- The face-star network has one old region for every old region and one
center region for every old face. -/
theorem faceStar_regionCount_eq {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) :
    (faceStarNetwork M I).regionCount = M.vertexCount + M.faceCount :=
  faceStarNetwork_regionCount I

end DkMath.Tromino
