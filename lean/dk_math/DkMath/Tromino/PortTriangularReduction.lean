/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarColorReduction

#print "file: DkMath.Tromino.PortTriangularReduction"

/-!
# Universal triangular reduction

This module packages the face-star construction into universal target
schemas. It proves equivalences between those schemas and the existing
genus-zero four-color target; it does not prove any target itself.

In particular, this module does not prove a universal four-color theorem, a
universal tetrahedral assignment theorem, an arbitrary coloring extension,
or an Euclidean/Eisenstein realization.
-/

namespace DkMath.Tromino

/-! ## Indexing-free face-star reductions -/

/-- Every genus-zero map has a face-star indexing whose packaged map is
triangular and whose coloring pulls back to a coloring of the original map. -/
theorem exists_faceStarGenusZeroTriangulation {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P) :
    ∃ I : PortFaceStarIndexing G.map,
      PortAllFacesTriangular (faceStarGenusZero G I).map ∧
        (PortFourStateColorable (faceStarGenusZero G I).map.crossing →
          PortFourStateColorable G.map.crossing) := by
  obtain ⟨I⟩ := exists_portFaceStarIndexing G.map
  refine ⟨I, faceStarGenusZero_allFacesTriangular G I, ?_⟩
  exact faceStarGenusZero_colorable_imp_original G I

/-- The same indexing gives a one-way reduction from a face-star tetrahedral
assignment to a four-state coloring of the original map. -/
theorem exists_faceStarGenusZeroTetrahedralReduction {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P) :
    ∃ I : PortFaceStarIndexing G.map,
      PortAllFacesTriangular (faceStarGenusZero G I).map ∧
        (HasTetrahedralFaceAssignment (faceStarGenusZero G I).map →
          PortFourStateColorable G.map.crossing) := by
  obtain ⟨I⟩ := exists_portFaceStarIndexing G.map
  refine ⟨I, faceStarGenusZero_allFacesTriangular G I, ?_⟩
  exact faceStar_tetrahedral_imp_original_colorable G I

/-! ## Universal target schemas -/

/-- The universal four-color assertion restricted to all-triangular
genus-zero combinatorial maps. This is a target proposition, not a theorem. -/
def PortGenusZeroTriangularFourColorTarget : Prop :=
  ∀ (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
    PortAllFacesTriangular G.map →
      PortFourStateColorable G.map.crossing

/-- A coloring theorem for every genus-zero map immediately applies to the
subclass whose faces are triangular. -/
theorem portGenusZeroFourColorTarget_imp_triangular :
    PortGenusZeroFourColorTarget →
      PortGenusZeroTriangularFourColorTarget := by
  intro h P G _
  exact h P G

/-- A triangular coloring target implies the general target by replacing an
arbitrary map with its all-triangular face-star subdivision and restricting
the resulting coloring along old regions. -/
theorem portGenusZeroTriangularFourColorTarget_imp_general :
    PortGenusZeroTriangularFourColorTarget →
      PortGenusZeroFourColorTarget := by
  intro h P G
  obtain ⟨I⟩ := exists_portFaceStarIndexing G.map
  have hstar :
      PortFourStateColorable (faceStarGenusZero G I).map.crossing :=
    h (faceStarNetwork G.map I) (faceStarGenusZero G I)
      (faceStarGenusZero_allFacesTriangular G I)
  exact faceStarGenusZero_colorable_imp_original G I hstar

/-- The face-star construction identifies the triangular and general
four-color target propositions. -/
theorem portGenusZeroTriangularFourColorTarget_iff_fourColorTarget :
    PortGenusZeroTriangularFourColorTarget ↔
      PortGenusZeroFourColorTarget := by
  constructor
  · exact portGenusZeroTriangularFourColorTarget_imp_general
  · exact portGenusZeroFourColorTarget_imp_triangular

/-- The universal existence assertion for tetrahedral A/B/C face assignments
on all-triangular genus-zero maps. This is the remaining target proposition. -/
def PortGenusZeroTriangularTetrahedralTarget : Prop :=
  ∀ (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
    PortAllFacesTriangular G.map →
      HasTetrahedralFaceAssignment G.map

/-- On a triangular genus-zero map, the local tetrahedral normal form makes a
tetrahedral assignment equivalent to a four-state region coloring. -/
theorem portGenusZeroTriangularTetrahedralTarget_iff_triangularFourColorTarget :
    PortGenusZeroTriangularTetrahedralTarget ↔
      PortGenusZeroTriangularFourColorTarget := by
  constructor
  · intro h P G htri
    exact (hasTetrahedralFaceAssignment_iff_fourStateColorable G htri).mp
      (h P G htri)
  · intro h P G htri
    exact (hasTetrahedralFaceAssignment_iff_fourStateColorable G htri).mpr
      (h P G htri)

/-- Composing the preceding local equivalence with face-star reduction gives
the branch-closing equivalence with the general four-color target. -/
theorem portGenusZeroTriangularTetrahedralTarget_iff_fourColorTarget :
    PortGenusZeroTriangularTetrahedralTarget ↔
      PortGenusZeroFourColorTarget := by
  constructor
  · intro h
    exact portGenusZeroTriangularFourColorTarget_iff_fourColorTarget.mp
      (portGenusZeroTriangularTetrahedralTarget_iff_triangularFourColorTarget.mp h)
  · intro h
    exact portGenusZeroTriangularTetrahedralTarget_iff_triangularFourColorTarget.mpr
      (portGenusZeroTriangularFourColorTarget_iff_fourColorTarget.mpr h)

end DkMath.Tromino
