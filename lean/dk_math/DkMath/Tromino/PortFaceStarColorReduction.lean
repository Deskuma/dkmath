/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarEuler
import DkMath.Tromino.PortTriangularTetrahedral

#print "file: DkMath.Tromino.PortFaceStarColorReduction"

/-!
# Face-star triangulation and coloring restriction

This module exposes the packaged face-star map as an all-triangular map and
pulls any face-star region coloring back along the old-region embedding.
The reduction is intentionally one-way: a coloring of the refined map
restricts to a coloring of the original map, while no converse extension is
asserted here.
-/

namespace DkMath.Tromino

/-! ## Triangular packaging and old-edge calibration -/

/-- Every face cell of the packaged face-star map has the three darts created
by the face-star construction.

The old edge and the two radial edges form a triangular boundary around
each face center. -/
theorem faceStar_allFacesTriangular {P : PortNetwork}
    (M : PortCombinatorialMap P) (I : PortFaceStarIndexing M) :
    PortAllFacesTriangular (faceStarCombinatorialMap M I) := by
  intro F
  change F.val.card = 3
  exact faceStarCombinatorialMap_everyFaceCell_card_three I F

/-- The genus-zero wrapper inherits triangularity from its packaged map. -/
theorem faceStarGenusZero_allFacesTriangular {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P) (I : PortFaceStarIndexing G.map) :
    PortAllFacesTriangular (faceStarGenusZero G I).map := by
  rw [faceStarGenusZero_map]
  exact faceStar_allFacesTriangular G.map I

/-- The source region of an old-edge port is the old-region copy of the
original source region. -/
theorem faceStar_oldEdge_source {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarOldEdgePort I p).1 = oldRegion I p.1 :=
  faceStarOldEdgePort_source I p

/-- The old-edge crossing transports the original target region to its
old-region copy in the face-star map. -/
theorem faceStar_oldEdge_target {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    ((faceStarCombinatorialMap M I).crossing.cross
      (faceStarOldEdgePort I p)).1 =
      oldRegion I (M.crossing.cross p).1 := by
  rw [faceStarCombinatorialMap_crossing, faceStarCross_oldEdge]
  exact faceStarOldEdgePort_source I (M.crossing.cross p)

/-! ## Old-region embedding and adjacency -/

/-- The canonical inclusion of original regions into the old-region part of
the face-star region carrier.

This embedding is the interface along which colorings are restricted. -/
def faceStarOldRegionEmbedding {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    Fin P.regionCount → Fin (faceStarNetwork M I).regionCount :=
  oldRegion I

/-- Distinct original regions remain distinct after the face-star inclusion. -/
theorem faceStarOldRegionEmbedding_injective {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    Function.Injective (faceStarOldRegionEmbedding I) := by
  exact oldRegion_injective I

/-- Each original edge yields an adjacency between the corresponding old
regions in the face-star graph. -/
theorem faceStar_oldAdjacency_of_port {P : PortNetwork}
    (M : PortCombinatorialMap P) (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (portRegionSimpleGraph (faceStarCombinatorialMap M I).crossing).Adj
      (oldRegion I p.1) (oldRegion I (M.crossing.cross p).1) := by
  apply (portRegionSimpleGraph_adj_iff
    (faceStarCombinatorialMap M I).crossing _ _).2
  refine ⟨faceStarOldEdgePort I p, ?_, ?_⟩
  · exact faceStar_oldEdge_source I p
  · exact faceStar_oldEdge_target I p

/-- Every original region adjacency embeds through the old-region inclusion. -/
theorem faceStar_oldAdjacency {P : PortNetwork}
    (M : PortCombinatorialMap P) (I : PortFaceStarIndexing M)
    {r s : Fin P.regionCount}
    (h : (portRegionSimpleGraph M.crossing).Adj r s) :
    (portRegionSimpleGraph (faceStarCombinatorialMap M I).crossing).Adj
      (oldRegion I r) (oldRegion I s) := by
  rcases (portRegionSimpleGraph_adj_iff M.crossing r s).mp h with
    ⟨p, hsource, htarget⟩
  apply (portRegionSimpleGraph_adj_iff
    (faceStarCombinatorialMap M I).crossing _ _).2
  refine ⟨faceStarOldEdgePort I p, ?_, ?_⟩
  · exact (faceStar_oldEdge_source I p).trans (congrArg (oldRegion I) hsource)
  · exact (faceStar_oldEdge_target I p).trans (congrArg (oldRegion I) htarget)

/-! ## Pullback of a face-star coloring -/

/-- Pull a face-star region coloring back along the old-region embedding.

The old-region values are read directly from the refined coloring; old
adjacency is preserved by the old-edge darts. -/
def faceStarRestrictColoring {P : PortNetwork}
    (M : PortCombinatorialMap P) (I : PortFaceStarIndexing M)
    (K : (portRegionSimpleGraph
      (faceStarCombinatorialMap M I).crossing).Coloring TrominoState) :
    (portRegionSimpleGraph M.crossing).Coloring TrominoState :=
  SimpleGraph.Coloring.mk (fun r => K (oldRegion I r)) (by
    intro r s h
    exact K.valid (faceStar_oldAdjacency M I h))

/-- Evaluation of the restricted coloring is exactly evaluation of the source
coloring at the corresponding old region. -/
@[simp] theorem faceStarRestrictColoring_apply {P : PortNetwork}
    (M : PortCombinatorialMap P) (I : PortFaceStarIndexing M)
    (K : (portRegionSimpleGraph
      (faceStarCombinatorialMap M I).crossing).Coloring TrominoState)
    (r : Fin P.regionCount) :
    faceStarRestrictColoring M I K r = K (oldRegion I r) := rfl

/-- The pulled-back coloring separates the endpoints of every original edge. -/
theorem faceStarRestrictColoring_edge_ne {P : PortNetwork}
    (M : PortCombinatorialMap P) (I : PortFaceStarIndexing M)
    (K : (portRegionSimpleGraph
      (faceStarCombinatorialMap M I).crossing).Coloring TrominoState)
    (p : PortNetworkPort P) :
    faceStarRestrictColoring M I K p.1 ≠
      faceStarRestrictColoring M I K (M.crossing.cross p).1 := by
  change K (oldRegion I p.1) ≠ K (oldRegion I (M.crossing.cross p).1)
  exact K.valid (faceStar_oldAdjacency_of_port M I p)

/-! ## One-way colorability reduction -/

/-- Four-state colorability of the face-star graph implies four-state
colorability of the original graph.

Properness is inherited along the old-region embedding, so the refined
triangular map supplies a coloring certificate for the original graph. -/
theorem faceStar_colorable_imp_original {P : PortNetwork}
    (M : PortCombinatorialMap P) (I : PortFaceStarIndexing M) :
    PortFourStateColorable (faceStarCombinatorialMap M I).crossing →
      PortFourStateColorable M.crossing := by
  rintro ⟨K⟩
  exact ⟨faceStarRestrictColoring M I K⟩

/-- The preceding restriction specializes to the genus-zero face-star
wrapper. -/
theorem faceStarGenusZero_colorable_imp_original {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P) (I : PortFaceStarIndexing G.map) :
    PortFourStateColorable (faceStarGenusZero G I).map.crossing →
      PortFourStateColorable G.map.crossing := by
  intro h
  exact faceStar_colorable_imp_original G.map I h

/-! ## Tetrahedral consequence on the packaged face-star map -/

/-- On the triangular genus-zero face-star map, tetrahedral assignments and
four-state colorings are equivalent.

The triangular face interface identifies the tetrahedral face assignment
with the four-state region coloring on this packaged map. -/
theorem faceStar_tetrahedral_iff_colorable {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P) (I : PortFaceStarIndexing G.map) :
    HasTetrahedralFaceAssignment (faceStarGenusZero G I).map ↔
      PortFourStateColorable (faceStarGenusZero G I).map.crossing := by
  exact hasTetrahedralFaceAssignment_iff_fourStateColorable
    (faceStarGenusZero G I) (faceStarGenusZero_allFacesTriangular G I)

/-- A tetrahedral assignment on the face-star map restricts to a coloring of
the original genus-zero map. -/
theorem faceStar_tetrahedral_imp_original_colorable {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P) (I : PortFaceStarIndexing G.map) :
    HasTetrahedralFaceAssignment (faceStarGenusZero G I).map →
      PortFourStateColorable G.map.crossing := by
  intro h
  apply faceStarGenusZero_colorable_imp_original G I
  exact (faceStar_tetrahedral_iff_colorable G I).mp h

end DkMath.Tromino
