/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortTriangulationReduction

#print "file: DkMath.Tromino.PortFaceStarMap"

/-!
# Face-star connectivity and combinatorial-map packaging

This module lifts old region walks through old-edge ports, attaches the new
face-center regions, and packages the resulting connected map.

Mathematically, the new region set is the disjoint union of old regions and
one center for each old face. Connectivity is proved by lifting old walks and
then attaching every center to an old region along a radial edge.
-/

namespace DkMath.Tromino

/-! ## Region classification -/

/-- Every new region is either an old region or the center of an old face. -/
theorem faceStar_region_cases {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (x : Fin (faceStarNetwork M I).regionCount) :
    (∃ r : Fin M.vertexCount, x = oldRegion I r) ∨
      (∃ F : PortFaceCell M.localRotation M.crossing,
        x = faceCenterRegion I F) := by
  generalize hsum : (faceStarRegionEquiv M I).symm x = s
  have hs : faceStarRegionEquiv M I s = x := by
    rw [← hsum]
    exact (faceStarRegionEquiv M I).apply_symm_apply x
  cases s with
  | inl r =>
      change faceStarRegionEquiv M I (.inl r) = x at hs
      refine Or.inl ⟨r, ?_⟩
      change x = faceStarRegionEquiv M I (.inl r)
      exact hs.symm
  | inr f =>
      let F := I.faceEquiv.symm f
      have hF : I.faceEquiv F = f := by
        exact I.faceEquiv.apply_symm_apply f
      right
      refine ⟨F, ?_⟩
      change faceStarRegionEquiv M I (.inr f) = x at hs
      change x = faceStarRegionEquiv M I (.inr (I.faceEquiv F))
      rw [hF]
      exact hs.symm

/-! ## Old-walk lifting -/

/-- Mapping each edge of an old region walk to its old-edge port preserves
walk validity in the face-star crossing. -/
theorem faceStar_oldWalk_valid {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    {r s : Fin P.regionCount} {xs : List (PortNetworkPort P)}
    (h : PortRegionWalk.Valid M.crossing r s xs) :
    PortRegionWalk.Valid (faceStarCrossing I)
      (oldRegion I r) (oldRegion I s)
      (xs.map (faceStarOldEdgePort I)) := by
  induction xs generalizing r s with
  | nil =>
      simp only [PortRegionWalk.Valid, List.map_nil] at h ⊢
      exact congrArg (oldRegion I) h
  | cons p xs ih =>
      simp only [PortRegionWalk.Valid, List.map_cons] at h ⊢
      refine ⟨?_, ?_⟩
      · change oldRegion I p.1 = oldRegion I r
        exact congrArg (oldRegion I) h.1
      · rw [faceStarCross_oldEdge]
        exact ih h.2

/-- Lift an old region walk to a walk between the corresponding old regions
of the face-star map. -/
def liftFaceStarOldWalk {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    {r s : Fin P.regionCount}
    (W : PortRegionWalk M.crossing r s) :
    PortRegionWalk (faceStarCrossing I)
      (oldRegion I r) (oldRegion I s) :=
  ⟨W.edges.map (faceStarOldEdgePort I), faceStar_oldWalk_valid I W.valid⟩

/-- The lifted walk has exactly the pointwise image of the old edge list. -/
@[simp] theorem liftFaceStarOldWalk_edges {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    {r s : Fin P.regionCount} (W : PortRegionWalk M.crossing r s) :
    (liftFaceStarOldWalk I W).edges = W.edges.map (faceStarOldEdgePort I) :=
  rfl

/-- Reachability between old regions is preserved by the face-star lift. -/
theorem faceStar_oldRegion_reachable {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    {r s : Fin P.regionCount}
    (h : PortRegionReachable M.crossing r s) :
    PortRegionReachable (faceStarCrossing I)
      (oldRegion I r) (oldRegion I s) := by
  rcases h with ⟨W⟩
  exact ⟨liftFaceStarOldWalk I W⟩

/-- The old-region subgraph remains connected because the original map is
connected. -/
theorem faceStar_oldRegions_connected {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (r s : Fin P.regionCount) :
    PortRegionReachable (faceStarCrossing I)
      (oldRegion I r) (oldRegion I s) :=
  faceStar_oldRegion_reachable I (M.connected r s)

/-! ## Face-center attachment -/

/-- Every old face cell contains a port and therefore has a boundary witness. -/
theorem faceStar_faceCell_nonempty {P : PortNetwork}
    {M : PortCombinatorialMap P} (F : PortFaceCell M.localRotation M.crossing) :
    ∃ p : PortNetworkPort P, p ∈ F.val := by
  rcases (portFaceOrbits_mem_iff M.localRotation M.crossing F.val).mp
      F.property with ⟨p, hF⟩
  refine ⟨p, ?_⟩
  rw [hF]
  exact portFaceOrbit_contains M.localRotation M.crossing p

/-- A port lying in a face cell represents that face cell. -/
theorem faceStar_faceCell_representative {P : PortNetwork}
    {M : PortCombinatorialMap P} (F : PortFaceCell M.localRotation M.crossing)
    (p : PortNetworkPort P) (hp : p ∈ F.val) :
    faceCellOfPort M.localRotation M.crossing p = F :=
  (faceCellOfPort_eq_iff M.localRotation M.crossing p F).2 hp

/-- Each face-center region is attached to an old region by one radial edge. -/
theorem faceStar_center_attachment {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell M.localRotation M.crossing) :
    ∃ p : PortNetworkPort P, p ∈ F.val ∧
      PortRegionReachable (faceStarCrossing I)
        (oldRegion I p.1) (faceCenterRegion I F) := by
  rcases faceStar_faceCell_nonempty F with ⟨p, hp⟩
  have hcell : faceCellOfPort M.localRotation M.crossing p = F :=
    faceStar_faceCell_representative F p hp
  refine ⟨p, hp, ?_⟩
  have htarget :
      ((faceStarCrossing I).cross (faceStarRadialOldPort I p)).1 =
        faceCenterRegion I F := by
    rw [faceStarCross_radialOld, faceStarRadialCenterPort_source, hcell]
  rw [← htarget]
  exact ⟨PortRegionWalk.singleton (faceStarCrossing I)
    (faceStarRadialOldPort I p)⟩

/-! ## Global region connectivity -/

/-- Every new region can reach an old region: old regions already do, and
centers reach an old boundary region by radial attachment. -/
theorem faceStar_region_reaches_old {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (x : Fin (faceStarNetwork M I).regionCount) :
    ∃ r : Fin M.vertexCount,
      PortRegionReachable (faceStarCrossing I) x (oldRegion I r) := by
  rcases faceStar_region_cases I x with hold | hcenter
  · rcases hold with ⟨r, hx⟩
    refine ⟨r, ?_⟩
    rw [hx]
    exact portRegionReachable_refl (faceStarCrossing I) _
  · rcases hcenter with ⟨F, hx⟩
    rcases faceStar_center_attachment I F with ⟨p, hp, hattach⟩
    refine ⟨p.1, ?_⟩
    rw [hx]
    exact portRegionReachable_symm (faceStarCrossing I) hattach

/-- The entire face-star region graph is connected. -/
theorem faceStar_regionConnected {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortRegionConnected (faceStarCrossing I) := by
  intro x y
  rcases faceStar_region_reaches_old I x with ⟨r, hxr⟩
  rcases faceStar_region_reaches_old I y with ⟨s, hys⟩
  exact portRegionReachable_trans (faceStarCrossing I) hxr
    (portRegionReachable_trans (faceStarCrossing I)
      (faceStar_oldRegions_connected I r s)
      (portRegionReachable_symm (faceStarCrossing I) hys))

/-- The face-star carrier has at least one region. -/
theorem faceStar_nonemptyRegions {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    0 < (faceStarNetwork M I).regionCount := by
  rw [faceStarNetwork_regionCount I]
  have hv : 0 < M.vertexCount := by
    simpa [PortCombinatorialMap.vertexCount, portRegionVertexCount]
      using M.nonemptyRegions
  omega

/-! ## Packaged connected map -/

/-- Package the face-star crossing and rotation system as a connected
combinatorial map. -/
def faceStarCombinatorialMap {P : PortNetwork}
    (M : PortCombinatorialMap P) (I : PortFaceStarIndexing M) :
    PortCombinatorialMap (faceStarNetwork M I) where
  crossing := faceStarCrossing I
  rotation := faceStarRotationSystem I
  nonemptyRegions := faceStar_nonemptyRegions I
  connected := faceStar_regionConnected I

/-- Calibration of the packaged crossing with the constructed crossing. -/
@[simp] theorem faceStarCombinatorialMap_crossing {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).crossing = faceStarCrossing I := rfl

/-- Calibration of the packaged rotation with the constructed rotation. -/
@[simp] theorem faceStarCombinatorialMap_rotation {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).rotation = faceStarRotationSystem I := rfl

/-- Calibration of the packaged local rotation. -/
@[simp] theorem faceStarCombinatorialMap_localRotation {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).localRotation =
      (faceStarRotationSystem I).toPortLocalRotation := rfl

/-- Every face cell of the packaged map is a triangle. -/
theorem faceStarCombinatorialMap_everyFaceCell_card_three {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell (faceStarCombinatorialMap M I).localRotation
      (faceStarCombinatorialMap M I).crossing) :
    F.val.card = 3 := by
  exact faceStar_everyFaceCell_card_three I F

end DkMath.Tromino
