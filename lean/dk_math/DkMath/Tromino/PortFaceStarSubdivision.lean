/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortCombinatorialMap
import DkMath.Tromino.PortF2Chains

/-!
# Face-star subdivision carrier

This module defines the finite carrier used by the face-star subdivision.
The semantic three-way port descriptor is kept separate from the dependent
Fin encoding of the new regions. An explicit indexing package makes the
production constructors computable; classical finite equivalences are used
only by the indexing existence theorem.

The carrier has one old-region copy for each original region and one
face-center copy for each original face. Each old port contributes one old
edge dart and two radial darts.
-/

#print "file: DkMath.Tromino.PortFaceStarSubdivision"

namespace DkMath.Tromino

/-! ## Explicit indexing of old face cells and their boundary ports -/

/-- Finite enumerations needed to turn the semantic face-star carrier into a
computable dependent `Fin` carrier. -/
structure PortFaceStarIndexing {P : PortNetwork} (M : PortCombinatorialMap P) where
  /-- Enumeration of the old face cells by Fin M.faceCount. -/
  faceEquiv : PortFaceCell M.localRotation M.crossing ≃ Fin M.faceCount
  /-- Enumeration of the ports on one old face cell. -/
  facePortEquiv : ∀ F : PortFaceCell M.localRotation M.crossing,
    {p : PortNetworkPort P // p ∈ F.val} ≃ Fin F.val.card

/-- Every finite map admits an explicit face-star indexing package; the
classical choice is confined to this existence proof. -/
theorem exists_portFaceStarIndexing {P : PortNetwork} (M : PortCombinatorialMap P) :
    Nonempty (PortFaceStarIndexing M) := by
  classical
  let e : PortFaceCell M.localRotation M.crossing ≃ Fin M.faceCount :=
    (Fintype.equivFin (PortFaceCell M.localRotation M.crossing)).trans
      (finCongr (PortFaceCell_card M.localRotation M.crossing))
  refine ⟨{ faceEquiv := e, facePortEquiv := fun F => ?_ }⟩
  exact (Fintype.equivFin {p : PortNetworkPort P // p ∈ F.val}).trans
    (finCongr (Fintype.card_coe F.val))

/-! ## Semantic port descriptor -/

/-- Semantic classification of a new dart into old-edge, radial-old, or
radial-center type. -/
inductive FaceStarPortDesc {P : PortNetwork} (M : PortCombinatorialMap P)
  | oldEdge (p : PortNetworkPort P)
  | radialOld (p : PortNetworkPort P)
  | radialCenter (p : PortNetworkPort P)
deriving DecidableEq

/-- Identify semantic face-star darts with three disjoint copies of the old
ports. -/
def faceStarDescSumEquiv {P : PortNetwork} (M : PortCombinatorialMap P) :
    FaceStarPortDesc M ≃
      PortNetworkPort P ⊕ (PortNetworkPort P ⊕ PortNetworkPort P) where
  toFun x :=
    match x with
    | .oldEdge p => Sum.inl p
    | .radialOld p => Sum.inr (Sum.inl p)
    | .radialCenter p => Sum.inr (Sum.inr p)
  invFun x :=
    match x with
    | Sum.inl p => .oldEdge p
    | Sum.inr (Sum.inl p) => .radialOld p
    | Sum.inr (Sum.inr p) => .radialCenter p
  left_inv x := by
    cases x <;> rfl
  right_inv x := by
    cases x with
    | inl p => rfl
    | inr q => cases q <;> rfl

namespace FaceStarPortDesc

instance instFintype {P : PortNetwork} (M : PortCombinatorialMap P) :
    Fintype (FaceStarPortDesc M) :=
  Fintype.ofEquiv _ (faceStarDescSumEquiv M).symm

/-- The semantic carrier has one old-edge and two radial ports per old port. -/
theorem card {P : PortNetwork} (M : PortCombinatorialMap P) :
    Fintype.card (FaceStarPortDesc M) = 3 * M.portCount := by
  rw [Fintype.card_congr (faceStarDescSumEquiv M)]
  simp only [Fintype.card_sum]
  change Fintype.card (PortNetworkPort P) +
      (Fintype.card (PortNetworkPort P) + Fintype.card (PortNetworkPort P)) =
    3 * Fintype.card (PortNetworkPort P)
  omega

end FaceStarPortDesc

/-! ## New regions and their local arities -/

/-- The local arity is doubled at old regions and equals the old face length
at a face center. -/
def faceStarRegionArity {P : PortNetwork} (M : PortCombinatorialMap P)
    (I : PortFaceStarIndexing M) :
    Fin M.vertexCount ⊕ Fin M.faceCount → Nat
  | Sum.inl r => 2 * P.arity r
  | Sum.inr F => (I.faceEquiv.symm F).val.card

/-- The finite port network underlying the face-star subdivision. -/
def faceStarNetwork {P : PortNetwork} (M : PortCombinatorialMap P)
    (I : PortFaceStarIndexing M) : PortNetwork where
  regionCount := M.vertexCount + M.faceCount
  arity := fun r => faceStarRegionArity M I (finSumFinEquiv.symm r)

/-- Canonical sum equivalence separating old regions from face centers. -/
def faceStarRegionEquiv {P : PortNetwork} (M : PortCombinatorialMap P)
    (I : PortFaceStarIndexing M) :
    (Fin M.vertexCount ⊕ Fin M.faceCount) ≃
      Fin (faceStarNetwork M I).regionCount :=
  finSumFinEquiv

/-- The old-region part of the new region index. -/
def oldRegion {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (r : Fin M.vertexCount) :
    Fin (faceStarNetwork M I).regionCount :=
  faceStarRegionEquiv M I (.inl r)

/-- The center-region part of the new region index. -/
def faceCenterRegion {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M)
    (F : PortFaceCell M.localRotation M.crossing) :
    Fin (faceStarNetwork M I).regionCount :=
  faceStarRegionEquiv M I (.inr (I.faceEquiv F))

/-- The sum encoding makes the old-region inclusion injective. -/
theorem oldRegion_injective {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) :
    Function.Injective (oldRegion I) := by
  intro r s h
  have h' : (Sum.inl r : Fin M.vertexCount ⊕ Fin M.faceCount) = Sum.inl s :=
    (faceStarRegionEquiv M I).injective h
  cases h'
  rfl

/-- Distinct old faces give distinct center regions. -/
theorem faceCenterRegion_injective {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) :
    Function.Injective (faceCenterRegion I) := by
  intro F G h
  have h' : (Sum.inr (I.faceEquiv F) : Fin M.vertexCount ⊕ Fin M.faceCount) =
      Sum.inr (I.faceEquiv G) :=
    (faceStarRegionEquiv M I).injective h
  have hfg : I.faceEquiv F = I.faceEquiv G := by
    injection h'
  exact Subtype.ext (congrArg Subtype.val (I.faceEquiv.injective hfg))

/-- Old-region and face-center copies are disjoint summands. -/
theorem oldRegion_ne_faceCenterRegion
    {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (r : Fin M.vertexCount)
    (F : PortFaceCell M.localRotation M.crossing) :
    oldRegion I r ≠ faceCenterRegion I F := by
  intro h
  have h' : (Sum.inl r : Fin M.vertexCount ⊕ Fin M.faceCount) =
      Sum.inr (I.faceEquiv F) :=
    (faceStarRegionEquiv M I).injective h
  cases h'

/-! ## Actual port constructors -

The following constructors realize the three semantic dart types in the
dependent `Fin` representation of the new network.
-/

/-- A two-slot old-region encoding: slot 0 is old-edge, slot 1 is radial-old. -/
def oldPortFin {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) (b : Fin 2) :
    Fin ((faceStarNetwork M I).arity (oldRegion I p.1)) := by
  refine Fin.cast ?_ (finProdFinEquiv (m := 2) (n := P.arity p.1) (b, p.2))
  change 2 * P.arity p.1 = faceStarRegionArity M I
    (finSumFinEquiv.symm (finSumFinEquiv (.inl p.1)))
  rw [Equiv.symm_apply_apply]
  rfl

/-- A center-region slot obtained from the indexed boundary port of F. -/
def centerPortFin {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M)
    (F : PortFaceCell M.localRotation M.crossing)
    (q : {p : PortNetworkPort P // p ∈ F.val}) :
    Fin ((faceStarNetwork M I).arity (faceCenterRegion I F)) := by
  refine Fin.cast ?_ (I.facePortEquiv F q)
  change F.val.card = faceStarRegionArity M I
    (finSumFinEquiv.symm (finSumFinEquiv (.inr (I.faceEquiv F))))
  rw [Equiv.symm_apply_apply]
  simp [faceStarRegionArity]

/-- The old-edge port associated with an old port p. -/
def faceStarOldEdgePort {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    PortNetworkPort (faceStarNetwork M I) :=
  ⟨oldRegion I p.1, oldPortFin I p 0⟩

/-- The old-region endpoint of the radial edge associated with p. -/
def faceStarRadialOldPort {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    PortNetworkPort (faceStarNetwork M I) :=
  ⟨oldRegion I p.1, oldPortFin I p 1⟩

/-- The center-region endpoint of the radial edge associated with p. -/
def faceStarRadialCenterPort {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    PortNetworkPort (faceStarNetwork M I) :=
  let F := faceCellOfPort M.localRotation M.crossing p
  let q : {q : PortNetworkPort P // q ∈ F.val} :=
    ⟨p, faceCellOfPort_mem _ _ _⟩
  ⟨faceCenterRegion I F, centerPortFin I F q⟩

/-- The old-edge dart starts at the old copy of the source region. -/
theorem faceStarOldEdgePort_source {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    (faceStarOldEdgePort I p).1 = oldRegion I p.1 :=
  rfl

/-- The radial-old dart starts at the old copy of the source region. -/
theorem faceStarRadialOldPort_source {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    (faceStarRadialOldPort I p).1 = oldRegion I p.1 :=
  rfl

/-- The radial-center dart starts at the center of the face containing the
original port. -/
theorem faceStarRadialCenterPort_source
    {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) (p : PortNetworkPort P) :
    (faceStarRadialCenterPort I p).1 =
      faceCenterRegion I (faceCellOfPort M.localRotation M.crossing p) :=
  rfl

/-- The new region count is the sum of old regions and old faces. -/
theorem faceStarNetwork_regionCount {P : PortNetwork} {M : PortCombinatorialMap P}
    (I : PortFaceStarIndexing M) :
    (faceStarNetwork M I).regionCount = M.vertexCount + M.faceCount :=
  rfl

end DkMath.Tromino
