/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarSubdivision

/-!
# Face-star triangulation reduction

This module records the semantic crossing and rotation permutations for the
face-star carrier. The actual dependent-Fin transport is kept separate so
that these operations can be checked without duplicating their mathematics.
-/

#print "file: DkMath.Tromino.PortTriangulationReduction"

namespace DkMath.Tromino

/-! ## Semantic crossing -/

def faceStarCrossDesc {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M → FaceStarPortDesc M
  | .oldEdge p => .oldEdge (M.crossing.cross p)
  | .radialOld p => .radialCenter p
  | .radialCenter p => .radialOld p

theorem faceStarCrossDesc_involutive {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    Function.Involutive (faceStarCrossDesc M) := by
  intro d
  cases d with
  | oldEdge p =>
      exact congrArg FaceStarPortDesc.oldEdge (M.crossing.involutive p)
  | radialOld p =>
      rfl
  | radialCenter p =>
      rfl

/-! ## Semantic rotation -/

def faceStarRotateDesc {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M → FaceStarPortDesc M
  | .radialOld p => .oldEdge p
  | .oldEdge p => .radialOld (M.localRotation.rotate p)
  | .radialCenter p =>
      .radialCenter ((portFaceEquiv M.localRotation M.crossing).symm p)

def faceStarRotateDescEquiv {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M ≃ FaceStarPortDesc M where
  toFun := faceStarRotateDesc M
  invFun
    | .oldEdge p => .radialOld p
    | .radialOld p => .oldEdge (M.localRotation.rotate.symm p)
    | .radialCenter p =>
        .radialCenter (portFaceEquiv M.localRotation M.crossing p)
  left_inv := by
    intro d
    cases d with
    | oldEdge p =>
        simp [faceStarRotateDesc]
    | radialOld p =>
        simp [faceStarRotateDesc]
    | radialCenter p =>
        simp [faceStarRotateDesc]
  right_inv := by
    intro d
    cases d with
    | oldEdge p =>
        simp [faceStarRotateDesc]
    | radialOld p =>
        simp [faceStarRotateDesc]
    | radialCenter p =>
        simp [faceStarRotateDesc]

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
