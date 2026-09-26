import DkMath.Tromino.PortTriangulationReduction

namespace DkMathTest.Tromino

open DkMath.Tromino

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

#print axioms exists_portFaceStarIndexing
#print axioms FaceStarPortDesc.card
#print axioms faceStar_descriptor_card

end DkMathTest.Tromino
