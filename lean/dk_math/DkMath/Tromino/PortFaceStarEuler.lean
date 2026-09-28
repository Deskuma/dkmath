/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortFaceStarMap
import Mathlib.Data.Sigma.Order

/-!
# Face-star counts, Euler characteristic, and genus preservation

This module counts the packaged face-star map through explicit port and
face-cell equivalences, then transports Euler and genus-zero statements.
The key identities are `D' = 3D`, `V' = V + F`, `E' = 3E`, and
`F' = D`; their cancellation proves preservation of the finite Euler
characteristic and hence of every certified combinatorial genus.
-/

namespace DkMath.Tromino

/-! ## Port count and old-port face cells -/

/-- The three descriptor families give three copies of every old port, hence
the face-star port count is `D' = 3D`.

The semantic descriptor equivalence makes the count independent of the
dependent `Fin` encoding used by the constructed carrier. -/
theorem faceStar_portCount {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).portCount = 3 * M.portCount := by
  change Fintype.card (PortNetworkPort (faceStarNetwork M I)) = 3 * M.portCount
  rw [Fintype.card_congr (faceStarPortEquiv I)]
  exact faceStar_descriptor_card M

/-- Associate to an old port the face cell containing its old-edge dart.

This is the map that later identifies old ports with the new triangular face
cells. -/
def faceStarOldPortToFaceCell {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    PortFaceCell (faceStarCombinatorialMap M I).localRotation
      (faceStarCombinatorialMap M I).crossing :=
  faceCellOfPort _ _ (faceStarOldEdgePort I p)

/-- The face cell of an old port is the triangular orbit attached to that
old port. -/
theorem faceStarOldPortToFaceCell_val {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarOldPortToFaceCell I p).val = faceStarTriangle M I p := by
  change portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I) (faceStarOldEdgePort I p) = faceStarTriangle M I p
  exact (faceStarTriangle_eq_oldEdge_orbit I p).symm

/-- Every face-star triangle contains the old-edge dart from which it is
indexed. -/
theorem faceStarTriangle_oldEdge_mem {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarOldEdgePort I p ∈ faceStarTriangle M I p := by
  simp [faceStarTriangle]

/-- The old-edge constructor remembers its original port. -/
theorem faceStarOldEdgePort_injective {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    Function.Injective (faceStarOldEdgePort I) := by
  intro p q hpq
  have hd := congrArg (faceStarPortDecode I) hpq
  simpa using hd

/-- Within a face-star triangle, the old-edge dart identifies its source
old port uniquely. -/
theorem faceStarTriangle_oldEdge_unique {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    {p q : PortNetworkPort P}
    (hq : faceStarOldEdgePort I q ∈ faceStarTriangle M I p) :
    q = p := by
  simp only [faceStarTriangle, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with hq | hq | hq
  · exact faceStarOldEdgePort_injective I hq
  · have hd := congrArg (faceStarPortDecode I) hq
    simp at hd
  · have hd := congrArg (faceStarPortDecode I) hq
    simp at hd

/-- Different old ports determine different face cells.

The old-edge dart is unique inside its generated triangle, so equality of
the resulting face cells forces equality of the indexing old ports. -/
theorem faceStarOldPortToFaceCell_injective {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    Function.Injective (faceStarOldPortToFaceCell I) := by
  intro p q hcell
  have htri : faceStarTriangle M I p = faceStarTriangle M I q := by
    calc
      faceStarTriangle M I p = (faceStarOldPortToFaceCell I p).val :=
        (faceStarOldPortToFaceCell_val I p).symm
      _ = (faceStarOldPortToFaceCell I q).val := congrArg Subtype.val hcell
      _ = faceStarTriangle M I q := faceStarOldPortToFaceCell_val I q
  have hmem : faceStarOldEdgePort I q ∈ faceStarTriangle M I p := by
    rw [htri]
    exact faceStarTriangle_oldEdge_mem I q
  exact (faceStarTriangle_oldEdge_unique I (p := p) (q := q) hmem).symm

/-- A finite face cell has a representative port, allowing a computable
representative to be selected in the explicit face-star carrier. -/
theorem faceStar_newFaceCell_nonempty {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell (faceStarCombinatorialMap M I).localRotation
      (faceStarCombinatorialMap M I).crossing) :
    F.val.Nonempty := by
  rcases (portFaceOrbits_mem_iff
    (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I) F.val).mp
      F.property with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hq]
  exact portFaceOrbit_contains _ _ q

/-- Choose a deterministic port representative for a face cell by decoding
the least port in its orbit. -/
def faceStarFaceCellRepresentative {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell (faceStarCombinatorialMap M I).localRotation
      (faceStarCombinatorialMap M I).crossing) : PortNetworkPort P :=
  letI : LinearOrder (PortNetworkPort (faceStarNetwork M I)) :=
    Sigma.Lex.linearOrder
  let q := F.val.min' (faceStar_newFaceCell_nonempty I F)
  match faceStarPortDecode I q with
  | .oldEdge p => p
  | .radialOld p => (portFaceEquiv M.localRotation M.crossing).symm p
  | .radialCenter p => p

/-- The chosen representative maps back to the face cell from which it was
selected. -/
theorem faceStarFaceCellRepresentative_cell {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (F : PortFaceCell (faceStarCombinatorialMap M I).localRotation
      (faceStarCombinatorialMap M I).crossing) :
    faceStarOldPortToFaceCell I (faceStarFaceCellRepresentative I F) = F := by
  let : LinearOrder (PortNetworkPort (faceStarNetwork M I)) := Sigma.Lex.linearOrder
  let q := F.val.min' (faceStar_newFaceCell_nonempty I F)
  have hq : q ∈ F.val := by
    exact Finset.min'_mem _ (faceStar_newFaceCell_nonempty I F)
  generalize hd : faceStarPortDecode I q = d
  have hqenc : faceStarPortEncode I d = q := by
    calc
      faceStarPortEncode I d = faceStarPortEncode I (faceStarPortDecode I q) := by
        rw [hd]
      _ = q := faceStarPortEncode_decode I q
  cases d with
  | oldEdge p =>
      have hrep : faceStarFaceCellRepresentative I F = p := by
        simp [faceStarFaceCellRepresentative, q, hd]
      rw [hrep]
      apply (faceCellOfPort_eq_iff _ _ _ F).2
      rw [← hqenc] at hq
      simpa using hq
  | radialOld p =>
      let p0 := (portFaceEquiv M.localRotation M.crossing).symm p
      have hp0 : portFaceStep M.localRotation M.crossing p0 = p := by
        dsimp [p0]
        exact (portFaceEquiv M.localRotation M.crossing).apply_symm_apply p
      have hrep : faceStarFaceCellRepresentative I F = p0 := by
        simp [faceStarFaceCellRepresentative, q, hd, p0]
      rw [hrep]
      have hmem : faceStarRadialOldPort I p ∈ F.val := by
        rw [← hqenc] at hq
        simpa using hq
      have hcell : faceCellOfPort
          (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)
          (faceStarRadialOldPort I p) = F :=
        (faceCellOfPort_eq_iff _ _ _ F).2 hmem
      have hstep : faceStarRadialOldPort I p =
          portFaceStep (faceStarRotationSystem I).toPortLocalRotation
            (faceStarCrossing I) (faceStarOldEdgePort I p0) := by
        rw [faceStarFaceStep_oldEdge, hp0]
      have hmemOrbit : faceStarRadialOldPort I p ∈
          portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
            (faceStarCrossing I) (faceStarOldEdgePort I p0) := by
        rw [hstep]
        exact portFaceOrbit_mem_iterate _ _ _ 1
      exact (faceCellOfPort_eq_of_mem _ _ _ _ hmemOrbit).symm.trans hcell
  | radialCenter p =>
      have hrep : faceStarFaceCellRepresentative I F = p := by
        simp [faceStarFaceCellRepresentative, q, hd]
      rw [hrep]
      have hmem : faceStarRadialCenterPort I p ∈ F.val := by
        rw [← hqenc] at hq
        simpa using hq
      have hcell : faceCellOfPort
          (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)
          (faceStarRadialCenterPort I p) = F :=
        (faceCellOfPort_eq_iff _ _ _ F).2 hmem
      have horbit :
          portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
              (faceStarCrossing I) (faceStarOldEdgePort I p) =
            portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
              (faceStarCrossing I) (faceStarRadialCenterPort I p) :=
        (faceStarTriangle_eq_oldEdge_orbit I p).symm.trans
          (faceStarTriangle_eq_radialCenter_orbit I p)
      have hmemOrbit : faceStarRadialCenterPort I p ∈
          portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
            (faceStarCrossing I) (faceStarOldEdgePort I p) := by
        rw [horbit]
        exact portFaceOrbit_contains _ _ _
      exact (faceCellOfPort_eq_of_mem _ _ _ _ hmemOrbit).symm.trans hcell

/-- Every face-star face cell is represented by an old port.

The triangle coverage theorem supplies an old-edge representative even when
the chosen representative of the face cell is radial. -/
theorem faceStarOldPortToFaceCell_surjective {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    Function.Surjective (faceStarOldPortToFaceCell I) := by
  intro F
  rcases (portFaceOrbits_mem_iff
    (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I) F.val).mp
      F.property with ⟨q, hF⟩
  have hFcell : F = faceCellOfPort
      (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I) q := by
    apply Subtype.ext
    exact hF
  rcases faceStarTriangle_coverage I q with ⟨p, hp⟩
  rw [faceStarTriangle_eq_oldEdge_orbit I p] at hp
  refine ⟨p, ?_⟩
  apply Subtype.ext
  calc
    (faceStarOldPortToFaceCell I p).val =
        portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
          (faceStarCrossing I) (faceStarOldEdgePort I p) := rfl
    _ = portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
          (faceStarCrossing I) q :=
      (portFaceOrbit_eq_of_mem _ _ _ _ hp).symm
    _ = F.val := hFcell.symm ▸ rfl

/-! ## Face-cell equivalence and counts -/

/-- The old ports and the new face cells are equivalent finite sets.

Injectivity and surjectivity combine into the finite equivalence responsible
for the identity `F' = D`. -/
def faceStarFaceCellEquiv {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    PortNetworkPort P ≃
      PortFaceCell (faceStarCombinatorialMap M I).localRotation
        (faceStarCombinatorialMap M I).crossing where
  toFun := faceStarOldPortToFaceCell I
  invFun := faceStarFaceCellRepresentative I
  left_inv := by
    intro p
    apply faceStarOldPortToFaceCell_injective I
    exact faceStarFaceCellRepresentative_cell I _
  right_inv := by
    intro F
    exact faceStarFaceCellRepresentative_cell I F

/-- The face-cell equivalence gives `F' = D`, since old ports index the new
face cells. -/
theorem faceStar_faceCount {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).faceCount = M.portCount := by
  change portFaceCount (faceStarRotationSystem I).toPortLocalRotation
    (faceStarCrossing I) = M.portCount
  calc
    portFaceCount (faceStarRotationSystem I).toPortLocalRotation
        (faceStarCrossing I) =
        Fintype.card (PortFaceCell
          (faceStarRotationSystem I).toPortLocalRotation (faceStarCrossing I)) :=
      (PortFaceCell_card _ _).symm
    _ = Fintype.card (PortNetworkPort P) :=
      (Fintype.card_congr (faceStarFaceCellEquiv I)).symm
    _ = M.portCount := rfl

/-- Face-star subdivision adds one center region for each old face, so
`V' = V + F`.

The new region carrier is the disjoint sum of old regions and one center per
old face. -/
theorem faceStar_vertexCount {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).vertexCount = M.vertexCount + M.faceCount := by
  change (faceStarNetwork M I).regionCount = M.vertexCount + M.faceCount
  exact faceStarNetwork_regionCount I

/-- Each crossing edge has two ports, giving the basic identity `2E = D`. -/
theorem two_mul_edgeCount_eq_portCount {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    2 * M.edgeCount = M.portCount := by
  exact two_mul_portCrossingEdgeCount M.crossing

/-- The face-star construction triples the old edge count: `E' = 3E`.

Each old edge remains one edge and each of its two ports contributes one
radial edge, giving two additional radial edges per old edge. -/
theorem faceStar_edgeCount {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).edgeCount = 3 * M.edgeCount := by
  have hnew := two_mul_edgeCount_eq_portCount
    (faceStarCombinatorialMap M I)
  have hold := two_mul_edgeCount_eq_portCount M
  have hport := faceStar_portCount I
  omega

/-- The same edge count can be read as old edges plus one radial edge per
old port: `E' = E + D`. -/
theorem faceStar_edgeCount_eq_add_portCount {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).edgeCount = M.edgeCount + M.portCount := by
  have hedge := faceStar_edgeCount I
  have hold := two_mul_edgeCount_eq_portCount M
  omega

/-- Expand the packaged Euler characteristic as `V - E + F`. -/
theorem portCombinatorialMap_eulerCharacteristic_eq {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    M.eulerCharacteristic =
      (M.vertexCount : Int) - (M.edgeCount : Int) + (M.faceCount : Int) := by
  rfl

/-- The count identities preserve Euler characteristic under face-star
subdivision: `χ' = χ`.

Substituting the four finite count identities gives
`(V + F) - 3E + 3D = V - E + F` using `D = 2E`. -/
theorem faceStar_eulerCharacteristic {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).eulerCharacteristic =
      M.eulerCharacteristic := by
  rw [portCombinatorialMap_eulerCharacteristic_eq,
    portCombinatorialMap_eulerCharacteristic_eq,
    faceStar_vertexCount I, faceStar_edgeCount I, faceStar_faceCount I]
  have hold := two_mul_edgeCount_eq_portCount M
  have hcast : (M.portCount : Int) = 2 * (M.edgeCount : Int) := by
    exact_mod_cast hold.symm
  omega

/-! ## Genus preservation -/

/-- Any stated combinatorial genus is preserved because it is determined by
Euler characteristic.

This is preservation of the certificate equation, not an independent
topological invariance theorem. -/
theorem faceStar_preserves_combinatorial_genus {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    {g : Nat} (hg : PortHasCombinatorialGenus M g) :
    PortHasCombinatorialGenus (faceStarCombinatorialMap M I) g := by
  unfold PortHasCombinatorialGenus at hg ⊢
  rw [faceStar_eulerCharacteristic I, hg]

/-- The face-star map has genus `g` exactly when the original map has genus
`g`. -/
theorem faceStar_combinatorial_genus_iff {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) (g : Nat) :
    PortHasCombinatorialGenus (faceStarCombinatorialMap M I) g ↔
      PortHasCombinatorialGenus M g := by
  rw [PortHasCombinatorialGenus, PortHasCombinatorialGenus,
    faceStar_eulerCharacteristic I]

/-- Package the face-star map and its preserved genus-zero witness. -/
def faceStarGenusZero {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    PortGenusZeroCombinatorialMap (faceStarNetwork G.map I) where
  map := faceStarCombinatorialMap G.map I
  genusZero := faceStar_preserves_combinatorial_genus I G.genusZero

/-- The map field of the genus-zero wrapper is the packaged face-star map. -/
@[simp] theorem faceStarGenusZero_map {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).map = faceStarCombinatorialMap G.map I := rfl

/-- Vertex-count calibration for the genus-zero face-star wrapper. -/
@[simp] theorem faceStarGenusZero_vertexCount {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).vertexCount = G.map.vertexCount + G.map.faceCount :=
  faceStar_vertexCount I

/-- Edge-count calibration for the genus-zero face-star wrapper. -/
@[simp] theorem faceStarGenusZero_edgeCount {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).edgeCount = 3 * G.map.edgeCount :=
  faceStar_edgeCount I

/-- Face-count calibration for the genus-zero face-star wrapper. -/
@[simp] theorem faceStarGenusZero_faceCount {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).faceCount = G.map.portCount :=
  faceStar_faceCount I

/-- Port-count calibration for the genus-zero face-star wrapper. -/
@[simp] theorem faceStarGenusZero_portCount {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).portCount = 3 * G.map.portCount :=
  faceStar_portCount I

/-- Euler-characteristic calibration for the genus-zero face-star wrapper. -/
@[simp] theorem faceStarGenusZero_eulerCharacteristic {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).eulerCharacteristic = G.map.eulerCharacteristic :=
  faceStar_eulerCharacteristic I

end DkMath.Tromino
