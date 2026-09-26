/- Copyright (c) 2026 D. and Wise Wolf. All rights reserved. -/
import DkMath.Tromino.PortFaceStarSubdivision

namespace DkMath.Tromino

/-! The reduction layer exposes the verified finite carrier and region split. -/

theorem faceStar_descriptor_card {P : PortNetwork} (M : PortCombinatorialMap P) :
    Fintype.card (FaceStarPortDesc M) = 3 * M.portCount :=
  FaceStarPortDesc.card M

theorem faceStar_regionCount_eq {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) :
    (faceStarNetwork M I).regionCount = M.vertexCount + M.faceCount :=
  faceStarNetwork_regionCount I

end DkMath.Tromino
