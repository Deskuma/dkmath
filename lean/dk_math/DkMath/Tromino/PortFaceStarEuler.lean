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
-/

namespace DkMath.Tromino

/-! ## Port count and old-port face cells -/

theorem faceStar_portCount {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).portCount = 3 * M.portCount := by
  change Fintype.card (PortNetworkPort (faceStarNetwork M I)) = 3 * M.portCount
  rw [Fintype.card_congr (faceStarPortEquiv I)]
  exact faceStar_descriptor_card M

def faceStarOldPortToFaceCell {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    PortFaceCell (faceStarCombinatorialMap M I).localRotation
      (faceStarCombinatorialMap M I).crossing :=
  faceCellOfPort _ _ (faceStarOldEdgePort I p)

theorem faceStarOldPortToFaceCell_val {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    (faceStarOldPortToFaceCell I p).val = faceStarTriangle M I p := by
  change portFaceOrbit (faceStarRotationSystem I).toPortLocalRotation
      (faceStarCrossing I) (faceStarOldEdgePort I p) = faceStarTriangle M I p
  exact (faceStarTriangle_eq_oldEdge_orbit I p).symm

theorem faceStarTriangle_oldEdge_mem {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    (p : PortNetworkPort P) :
    faceStarOldEdgePort I p ∈ faceStarTriangle M I p := by
  simp [faceStarTriangle]

theorem faceStarOldEdgePort_injective {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    Function.Injective (faceStarOldEdgePort I) := by
  intro p q hpq
  have hd := congrArg (faceStarPortDecode I) hpq
  simpa using hd

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

theorem faceStar_vertexCount {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).vertexCount = M.vertexCount + M.faceCount := by
  change (faceStarNetwork M I).regionCount = M.vertexCount + M.faceCount
  exact faceStarNetwork_regionCount I

theorem two_mul_edgeCount_eq_portCount {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    2 * M.edgeCount = M.portCount := by
  exact two_mul_portCrossingEdgeCount M.crossing

theorem faceStar_edgeCount {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).edgeCount = 3 * M.edgeCount := by
  have hnew := two_mul_edgeCount_eq_portCount
    (faceStarCombinatorialMap M I)
  have hold := two_mul_edgeCount_eq_portCount M
  have hport := faceStar_portCount I
  omega

theorem faceStar_edgeCount_eq_add_portCount {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) :
    (faceStarCombinatorialMap M I).edgeCount = M.edgeCount + M.portCount := by
  have hedge := faceStar_edgeCount I
  have hold := two_mul_edgeCount_eq_portCount M
  omega

theorem portCombinatorialMap_eulerCharacteristic_eq {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    M.eulerCharacteristic =
      (M.vertexCount : Int) - (M.edgeCount : Int) + (M.faceCount : Int) := by
  rfl

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

theorem faceStar_preserves_combinatorial_genus {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M)
    {g : Nat} (hg : PortHasCombinatorialGenus M g) :
    PortHasCombinatorialGenus (faceStarCombinatorialMap M I) g := by
  unfold PortHasCombinatorialGenus at hg ⊢
  rw [faceStar_eulerCharacteristic I, hg]

theorem faceStar_combinatorial_genus_iff {P : PortNetwork}
    {M : PortCombinatorialMap P} (I : PortFaceStarIndexing M) (g : Nat) :
    PortHasCombinatorialGenus (faceStarCombinatorialMap M I) g ↔
      PortHasCombinatorialGenus M g := by
  rw [PortHasCombinatorialGenus, PortHasCombinatorialGenus,
    faceStar_eulerCharacteristic I]

def faceStarGenusZero {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    PortGenusZeroCombinatorialMap (faceStarNetwork G.map I) where
  map := faceStarCombinatorialMap G.map I
  genusZero := faceStar_preserves_combinatorial_genus I G.genusZero

@[simp] theorem faceStarGenusZero_map {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).map = faceStarCombinatorialMap G.map I := rfl

@[simp] theorem faceStarGenusZero_vertexCount {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).vertexCount = G.map.vertexCount + G.map.faceCount :=
  faceStar_vertexCount I

@[simp] theorem faceStarGenusZero_edgeCount {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).edgeCount = 3 * G.map.edgeCount :=
  faceStar_edgeCount I

@[simp] theorem faceStarGenusZero_faceCount {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).faceCount = G.map.portCount :=
  faceStar_faceCount I

@[simp] theorem faceStarGenusZero_portCount {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).portCount = 3 * G.map.portCount :=
  faceStar_portCount I

@[simp] theorem faceStarGenusZero_eulerCharacteristic {P : PortNetwork}
    (G : PortGenusZeroCombinatorialMap P)
    (I : PortFaceStarIndexing G.map) :
    (faceStarGenusZero G I).eulerCharacteristic = G.map.eulerCharacteristic :=
  faceStar_eulerCharacteristic I

end DkMath.Tromino
