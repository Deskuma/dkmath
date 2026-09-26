/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortF2Chains
import DkMath.Tromino.PortCombinatorialMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.Tromino.PortF2Exactness"

namespace DkMath.Tromino

open scoped BigOperators

/-! ## Representative-free boundary coefficients -/

theorem faceCellOfPort_eq_iff {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) (F : PortFaceCell R C) :
    faceCellOfPort R C p = F ↔ p ∈ F.val := by
  constructor
  · intro h
    rw [← h]
    exact faceCellOfPort_mem R C p
  · intro hp
    rcases (portFaceOrbits_mem_iff R C F.val).mp F.property with ⟨q, hq⟩
    have hpq : p ∈ portFaceOrbit R C q := by
      rw [← hq]
      exact hp
    have hcell := faceCellOfPort_eq_of_mem R C q p hpq
    exact hcell.trans (Subtype.ext hq).symm

theorem faceEdgeIncidence_edgeCellOfPort {P : PortNetwork}
    {R : PortLocalRotation P} {C : PortCrossing P}
    (F : PortFaceCell R C) (p : PortNetworkPort P) :
    faceEdgeIncidence F (edgeCellOfPort C p) =
      (if p ∈ F.val then 1 else 0) +
        (if C.cross p ∈ F.val then 1 else 0) := by
  classical
  change ((F.val ∩ {p, C.cross p}).card : PortF2) = _
  have hne : p ≠ C.cross p := by
    intro h
    exact C.cross_ne p h.symm
  have hcard : ({p, C.cross p} : Finset (PortNetworkPort P)).card = 2 :=
    Finset.card_pair hne
  by_cases hp : p ∈ F.val <;> by_cases hq : C.cross p ∈ F.val
  all_goals simp [hp, hq, hcard]
  all_goals norm_num

theorem sum_face_indicator {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P)
    (y : PortFaceChain R C) :
    (∑ F : PortFaceCell R C,
      y F * (if p ∈ F.val then (1 : PortF2) else 0)) =
      y (faceCellOfPort R C p) := by
  classical
  have hsum := Finset.sum_eq_single_of_mem
    (s := (Finset.univ : Finset (PortFaceCell R C)))
    (f := fun F : PortFaceCell R C =>
      y F * (if p ∈ F.val then (1 : PortF2) else 0))
    (faceCellOfPort R C p) (Finset.mem_univ _)
    (by
      intro F hF hne
      have hnot : p ∉ F.val := by
        intro hp
        exact hne ((faceCellOfPort_eq_iff R C p F).2 hp).symm
      simp [hnot])
  simpa [faceCellOfPort_mem] using hsum

theorem portBoundary2_edgeCellOfPort {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (y : PortFaceChain R C) (p : PortNetworkPort P) :
    (portBoundary2 R C y) (edgeCellOfPort C p) =
      y (faceCellOfPort R C p) +
        y (faceCellOfPort R C (C.cross p)) := by
  classical
  change (∑ F : PortFaceCell R C,
      y F * faceEdgeIncidence F (edgeCellOfPort C p)) = _
  calc
    (∑ F : PortFaceCell R C,
        y F * faceEdgeIncidence F (edgeCellOfPort C p)) =
        ∑ F : PortFaceCell R C,
          y F * ((if p ∈ F.val then (1 : PortF2) else 0) +
            (if C.cross p ∈ F.val then (1 : PortF2) else 0)) := by
              apply Finset.sum_congr rfl
              intro F hF
              rw [faceEdgeIncidence_edgeCellOfPort]
    _ = (∑ F : PortFaceCell R C,
        y F * (if p ∈ F.val then (1 : PortF2) else 0)) +
        (∑ F : PortFaceCell R C,
        y F * (if C.cross p ∈ F.val then (1 : PortF2) else 0)) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro F hF
              ring
    _ = _ := by rw [sum_face_indicator, sum_face_indicator]

/-! ## Constant faces and dual reachability -/

def constantFaceChain {P : PortNetwork} {R : PortLocalRotation P}
    {C : PortCrossing P} (a : PortF2) : PortFaceChain R C :=
  fun _ => a

theorem portBoundary2_constantFaceChain {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (a : PortF2) :
    portBoundary2 R C (constantFaceChain a) = 0 := by
  funext E
  rcases (portCrossingEdgeOrbits_mem_iff C E.val).mp E.property with ⟨p, hp⟩
  have hE : E = edgeCellOfPort C p := by
    apply Subtype.ext
    exact hp
  rw [hE, portBoundary2_edgeCellOfPort]
  simpa [constantFaceChain] using ZModModule.add_self a

def PortFaceAdjacent {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (F G : PortFaceCell R C) : Prop :=
  ∃ p : PortNetworkPort P,
    faceCellOfPort R C p = F ∧
      faceCellOfPort R C (C.cross p) = G

theorem portFaceAdjacent_symm {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) {F G : PortFaceCell R C} :
    PortFaceAdjacent R C F G → PortFaceAdjacent R C G F := by
  rintro ⟨p, hp, hq⟩
  refine ⟨C.cross p, hq, ?_⟩
  simpa [C.involutive p] using hp

theorem portFaceAdjacent_self_iff {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (F : PortFaceCell R C) :
    PortFaceAdjacent R C F F ↔
      ∃ p, faceCellOfPort R C p = F ∧
        faceCellOfPort R C (C.cross p) = F := Iff.rfl

def PortFaceReachable {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :=
  Relation.ReflTransGen (PortFaceAdjacent R C)

theorem portFaceReachable_refl {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (F : PortFaceCell R C) :
    PortFaceReachable R C F F :=
  Relation.ReflTransGen.refl

theorem portFaceReachable_trans {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) {F G H : PortFaceCell R C} :
    PortFaceReachable R C F G → PortFaceReachable R C G H →
      PortFaceReachable R C F H :=
  Relation.ReflTransGen.trans

theorem portFaceReachable_symm {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) {F G : PortFaceCell R C} :
    PortFaceReachable R C F G → PortFaceReachable R C G F := by
  intro h
  induction h with
  | refl => exact portFaceReachable_refl R C _
  | tail hab hbc ih =>
      exact Relation.ReflTransGen.head (portFaceAdjacent_symm R C hbc) ih

theorem portFaceReachable_rotate {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    PortFaceReachable R C (faceCellOfPort R C p)
      (faceCellOfPort R C (R.rotate p)) := by
  have hstep : portFaceStep R C (C.cross p) = R.rotate p := by
    change R.rotate (C.cross (C.cross p)) = R.rotate p
    rw [C.involutive]
  have hmem := portFaceOrbit_mem_iterate R C (C.cross p) 1
  have hcell := faceCellOfPort_eq_of_mem R C (C.cross p)
    (portFaceStep R C (C.cross p)) hmem
  apply Relation.ReflTransGen.single
  refine ⟨p, rfl, ?_⟩
  rw [← hstep]
  exact hcell.symm

theorem portFaceReachable_rotate_iterate {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) (n : Nat)
    (p : PortNetworkPort P) :
    PortFaceReachable R C (faceCellOfPort R C p)
      (faceCellOfPort R C ((R.rotate : PortNetworkPort P → PortNetworkPort P)^[n] p)) := by
  induction n generalizing p with
  | zero => exact portFaceReachable_refl R C _
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact portFaceReachable_trans R C
        (portFaceReachable_rotate R C p) (ih (R.rotate p))

theorem portFaceReachable_same_region {P : PortNetwork}
    (M : PortCombinatorialMap P) (p q : PortNetworkPort P)
    (hregion : p.1 = q.1) :
    PortFaceReachable M.localRotation M.crossing
      (faceCellOfPort M.localRotation M.crossing p)
      (faceCellOfPort M.localRotation M.crossing q) := by
  rcases M.rotation_reaches_same_region p q hregion with ⟨n, hn⟩
  rw [← hn]
  exact portFaceReachable_rotate_iterate M.localRotation M.crossing n p

theorem portFaceReachable_valid_edges {P : PortNetwork}
    (M : PortCombinatorialMap P) {r s : Fin P.regionCount}
    {xs : List (PortNetworkPort P)}
    (hvalid : PortRegionWalk.Valid M.crossing r s xs)
    (p q : PortNetworkPort P) (hp : p.1 = r) (hq : q.1 = s) :
    PortFaceReachable M.localRotation M.crossing
      (faceCellOfPort M.localRotation M.crossing p)
      (faceCellOfPort M.localRotation M.crossing q) := by
  induction xs generalizing r s p q with
  | nil =>
      simp only [PortRegionWalk.Valid] at hvalid
      subst s
      exact portFaceReachable_same_region M p q (hp.trans hq.symm)
  | cons a xs ih =>
      simp only [PortRegionWalk.Valid] at hvalid
      have hpa : p.1 = a.1 := hp.trans hvalid.1.symm
      exact portFaceReachable_trans M.localRotation M.crossing
        (portFaceReachable_same_region M p a hpa)
        (portFaceReachable_trans M.localRotation M.crossing
          (Relation.ReflTransGen.single ⟨a, rfl, rfl⟩)
          (ih hvalid.2 (M.crossing.cross a) q rfl hq))

theorem portFaceReachable_regionWalk {P : PortNetwork}
    (M : PortCombinatorialMap P) {r s : Fin P.regionCount}
    (W : PortRegionWalk M.crossing r s)
    (p q : PortNetworkPort P) (hp : p.1 = r) (hq : q.1 = s) :
    PortFaceReachable M.localRotation M.crossing
      (faceCellOfPort M.localRotation M.crossing p)
      (faceCellOfPort M.localRotation M.crossing q) :=
  portFaceReachable_valid_edges M W.valid p q hp hq


/-! ## Dual connectivity and the boundary-two kernel -/

theorem portFaceCells_connected {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    ∀ F G : PortFaceCell M.localRotation M.crossing,
      PortFaceReachable M.localRotation M.crossing F G := by
  classical
  intro F G
  rcases (portFaceOrbits_mem_iff M.localRotation M.crossing F.val).mp F.property with
    ⟨p, hp⟩
  rcases (portFaceOrbits_mem_iff M.localRotation M.crossing G.val).mp G.property with
    ⟨q, hq⟩
  have hFp : F = faceCellOfPort M.localRotation M.crossing p := Subtype.ext hp
  have hGq : G = faceCellOfPort M.localRotation M.crossing q := Subtype.ext hq
  rw [hFp, hGq]
  rcases M.connected p.1 q.1 with ⟨W⟩
  exact portFaceReachable_regionWalk M W p q rfl rfl

theorem portFaceAdjacent_eq_of_boundary2_zero {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (y : PortFaceChain R C) (hy : portBoundary2 R C y = 0)
    {F G : PortFaceCell R C} :
    PortFaceAdjacent R C F G → y F = y G := by
  rintro ⟨p, hp, hq⟩
  have hz := congrFun hy (edgeCellOfPort C p)
  rw [portBoundary2_edgeCellOfPort, hp, hq] at hz
  have hz' : y F + y G = 0 := by simpa using hz
  apply add_left_cancel (a := y F)
  calc
    y F + y F = 0 := ZModModule.add_self _
    _ = y F + y G := hz'.symm

theorem portFaceReachable_eq_of_boundary2_zero {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (y : PortFaceChain R C) (hy : portBoundary2 R C y = 0)
    {F G : PortFaceCell R C} :
    PortFaceReachable R C F G → y F = y G := by
  intro h
  induction h with
  | refl => rfl
  | tail hab hbc ih =>
      exact ih.trans (portFaceAdjacent_eq_of_boundary2_zero R C y hy hbc)

def portConstantFace {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    PortF2 →ₗ[PortF2] PortFaceChain M.localRotation M.crossing :=
  { toFun := fun a _ => a
    map_add' := by
      intro a b
      funext F
      simp
    map_smul' := by
      intro a b
      funext F
      simp }

def PortConstantFaceSpace {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    Submodule PortF2 (PortFaceChain M.localRotation M.crossing) :=
  LinearMap.range (portConstantFace M)

theorem portConstantFaceSpace_le_boundary2_ker {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    PortConstantFaceSpace M ≤
      LinearMap.ker (portBoundary2 M.localRotation M.crossing) := by
  rintro y ⟨a, rfl⟩
  exact LinearMap.mem_ker.mpr (portBoundary2_constantFaceChain
    M.localRotation M.crossing a)

theorem portBoundary2_ker_eq_portConstantFaceSpace {P : PortNetwork}
    (M : PortCombinatorialMap P)
    (hfaces : Nonempty (PortFaceCell M.localRotation M.crossing)) :
    LinearMap.ker (portBoundary2 M.localRotation M.crossing) =
      PortConstantFaceSpace M := by
  apply le_antisymm
  · intro y hy
    change portBoundary2 M.localRotation M.crossing y = 0 at hy
    let F₀ := Classical.choice hfaces
    let a : PortF2 := y F₀
    have hconst : ∀ F : PortFaceCell M.localRotation M.crossing, y F = a := by
      intro F
      exact portFaceReachable_eq_of_boundary2_zero
        M.localRotation M.crossing y hy
        (portFaceCells_connected M F F₀)
    refine ⟨a, ?_⟩
    ext F
    exact (hconst F).symm
  · exact portConstantFaceSpace_le_boundary2_ker M


/-! ## Vertex augmentation -/

def portVertexAugmentation {P : PortNetwork} :
    PortVertexChain P →ₗ[PortF2] PortF2 :=
  { toFun := fun x => ∑ r : Fin P.regionCount, x r
    map_add' := by
      intro x y
      simp [Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      simp [smul_eq_mul, Finset.mul_sum] }

theorem portVertexAugmentation_portBoundary1 {P : PortNetwork}
    (C : PortCrossing P) (x : PortEdgeChain C) :
    portVertexAugmentation (portBoundary1 C x) = 0 := by
  change ∑ r : Fin P.regionCount,
    ∑ E : PortEdgeCell C, x E * edgeVertexIncidence E r = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro E hE
  rw [← Finset.mul_sum]
  rw [edgeVertexIncidence_two_support C E]
  simp

theorem portBoundary1_range_le_vertexAugmentation_ker {P : PortNetwork}
    (C : PortCrossing P) :
    LinearMap.range (portBoundary1 C) ≤
      LinearMap.ker (portVertexAugmentation) := by
  rintro z ⟨x, rfl⟩
  apply LinearMap.mem_ker.mpr
  exact portVertexAugmentation_portBoundary1 C x


theorem portVertexAugmentation_ker_le_boundary1_range
    {P : PortNetwork} (M : PortCombinatorialMap P) :
    LinearMap.ker (portVertexAugmentation) ≤
      LinearMap.range (portBoundary1 M.crossing) := by
  classical
  intro z hz
  change (∑ r : Fin P.regionCount, z r) = 0 at hz
  let base : Fin P.regionCount := ⟨0, M.nonemptyRegions⟩
  let W : ∀ r : Fin P.regionCount, PortRegionWalk M.crossing base r :=
    fun r => Classical.choice (M.connected base r)
  let x : PortEdgeChain M.crossing :=
    ∑ r : Fin P.regionCount, z r • portWalkEdgeChain (W r)
  refine ⟨x, ?_⟩
  ext v
  dsimp [x]
  rw [map_sum]
  simp_rw [map_smul, portBoundary1_portWalkEdgeChain]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change ∑ r : Fin P.regionCount,
      z r * endpointVertexChain base r v = z v
  simp only [endpointVertexChain]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  by_cases hv : v = base
  · simp [hv, hz]
  · simp [hv]

theorem portBoundary1_range_eq_vertexAugmentation_ker
    {P : PortNetwork} (M : PortCombinatorialMap P) :
    LinearMap.range (portBoundary1 M.crossing) =
      LinearMap.ker (portVertexAugmentation) :=
  le_antisymm
    (portBoundary1_range_le_vertexAugmentation_ker M.crossing)
    (portVertexAugmentation_ker_le_boundary1_range M)


theorem portVertexAugmentation_surjective {P : PortNetwork}
    (hregions : 0 < P.regionCount) :
    Function.Surjective (@portVertexAugmentation P) := by
  intro a
  let base : Fin P.regionCount := ⟨0, hregions⟩
  refine ⟨fun r => if r = base then a else 0, ?_⟩
  simp [portVertexAugmentation, base]

theorem finrank_portBoundary1_range {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    Module.finrank PortF2 (LinearMap.range (portBoundary1 M.crossing)) =
      P.regionCount - 1 := by
  rw [portBoundary1_range_eq_vertexAugmentation_ker M]
  have hsurj := portVertexAugmentation_surjective M.nonemptyRegions
  have htop : LinearMap.range (@portVertexAugmentation P) = ⊤ :=
    (LinearMap.range_eq_top.mpr hsurj)
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (@portVertexAugmentation P)
  rw [htop, finrank_top, Module.finrank_self, finrank_portVertexChain] at hrank
  omega



theorem portVertexCount_le_edgeCount_add_one {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    P.regionCount ≤ portCrossingEdgeCount M.crossing + 1 := by
  have hle := (portBoundary1 M.crossing).finrank_range_le
  rw [finrank_portBoundary1_range M, finrank_portEdgeChain] at hle
  omega

theorem portGenusZero_faceCell_nonempty {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) :
    Nonempty (PortFaceCell M.map.localRotation M.map.crossing) := by
  classical
  have hV := portVertexCount_le_edgeCount_add_one M.map
  have hchar := M.hasSphereCharacteristic
  unfold PortHasSphereCharacteristic PortCombinatorialMap.eulerCharacteristic
    portCombinatorialEulerCharacteristic at hchar
  by_contra h
  have hcount : portFaceCount M.map.localRotation M.map.crossing = 0 := by
    have hcard : Fintype.card
        (PortFaceCell M.map.localRotation M.map.crossing) = 0 :=
      Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp h)
    rw [PortFaceCell_card] at hcard
    exact hcard
  rw [hcount] at hchar
  have hchar' :
      (P.regionCount : Int) - (portCrossingEdgeCount M.map.crossing : Int) = 2 := by
    simpa [PortCombinatorialMap.vertexCount, PortCombinatorialMap.edgeCount, portRegionVertexCount] using hchar
  omega

theorem portConstantFace_injective {P : PortNetwork}
    (M : PortCombinatorialMap P)
    (hfaces : Nonempty (PortFaceCell M.localRotation M.crossing)) :
    Function.Injective (portConstantFace M) := by
  intro a b hab
  have F := Classical.choice hfaces
  exact congrFun hab F

theorem finrank_portFaceBoundarySpace {P : PortNetwork}
    (M : PortGenusZeroCombinatorialMap P) :
    Module.finrank PortF2
        (PortFaceBoundarySpace M.map.localRotation M.map.crossing) =
      portFaceCount M.map.localRotation M.map.crossing - 1 := by
  have hfaces := portGenusZero_faceCell_nonempty M
  have hker := portBoundary2_ker_eq_portConstantFaceSpace M.map hfaces
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (portBoundary2 M.map.localRotation M.map.crossing)
  have hconst :
      Module.finrank PortF2 (PortConstantFaceSpace M.map) = 1 := by
    rw [show PortConstantFaceSpace M.map = LinearMap.range
      (portConstantFace M.map) from rfl]
    rw [LinearMap.finrank_range_of_inj
      (portConstantFace_injective M.map hfaces), Module.finrank_self]
  change Module.finrank PortF2
      (LinearMap.range (portBoundary2 M.map.localRotation M.map.crossing)) = _
  rw [finrank_portFaceChain, hker, hconst] at hrank
  omega

theorem finrank_portCycleSpace {P : PortNetwork}
    (M : PortCombinatorialMap P) :
    Module.finrank PortF2 (PortCycleSpace M.crossing) =
      portCrossingEdgeCount M.crossing - (P.regionCount - 1) := by
  change Module.finrank PortF2
    (LinearMap.ker (portBoundary1 M.crossing)) = _
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (portBoundary1 M.crossing)
  rw [finrank_portEdgeChain, finrank_portBoundary1_range M] at hrank
  omega

theorem portGenusZero_cycleSpace_finrank_eq_faceBoundarySpace_finrank
    {P : PortNetwork} (M : PortGenusZeroCombinatorialMap P) :
    Module.finrank PortF2 (PortCycleSpace M.map.crossing) =
      Module.finrank PortF2
        (PortFaceBoundarySpace M.map.localRotation M.map.crossing) := by
  rw [finrank_portCycleSpace, finrank_portFaceBoundarySpace]
  have hchar := M.hasSphereCharacteristic
  unfold PortHasSphereCharacteristic PortCombinatorialMap.eulerCharacteristic
    portCombinatorialEulerCharacteristic at hchar
  change (P.regionCount : Int) -
      (portCrossingEdgeCount M.map.crossing : Int) +
      (portFaceCount M.map.localRotation M.map.crossing : Int) = 2 at hchar
  have hVpos : 1 ≤ P.regionCount := M.map.nonemptyRegions
  have hFpos : 1 ≤ portFaceCount M.map.localRotation M.map.crossing := by
    have := (Fintype.card_pos_iff.mpr (portGenusZero_faceCell_nonempty M))
    rw [PortFaceCell_card] at this
    omega
  have hVEdge := portVertexCount_le_edgeCount_add_one M.map
  have hEsub : P.regionCount - 1 ≤ portCrossingEdgeCount M.map.crossing := by
    omega
  have hcast :
      ((portCrossingEdgeCount M.map.crossing - (P.regionCount - 1) : Nat) : Int) =
        ((portFaceCount M.map.localRotation M.map.crossing - 1 : Nat) : Int) := by
    rw [Nat.cast_sub hEsub, Nat.cast_sub hFpos, Nat.cast_sub hVpos]
    omega
  exact_mod_cast hcast

theorem portGenusZero_faceBoundarySpace_eq_cycleSpace
    {P : PortNetwork} (M : PortGenusZeroCombinatorialMap P) :
    PortFaceBoundarySpace M.map.localRotation M.map.crossing =
      PortCycleSpace M.map.crossing := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact faceBoundarySpace_le_cycleSpace M.map.localRotation M.map.crossing
  · exact (portGenusZero_cycleSpace_finrank_eq_faceBoundarySpace_finrank M).symm


theorem portGenusZero_closed_portWalkEdgeChain_mem_faceBoundarySpace
    {P : PortNetwork} (M : PortGenusZeroCombinatorialMap P)
    {r : Fin P.regionCount} (W : PortRegionWalk M.map.crossing r r) :
    portWalkEdgeChain W ∈
      PortFaceBoundarySpace M.map.localRotation M.map.crossing := by
  rw [portGenusZero_faceBoundarySpace_eq_cycleSpace M]
  exact closed_portWalkEdgeChain_mem_cycleSpace W

end DkMath.Tromino

#print axioms DkMath.Tromino.portBoundary2_edgeCellOfPort
#print axioms DkMath.Tromino.portFaceReachable_same_region
#print axioms DkMath.Tromino.portFaceReachable_regionWalk
