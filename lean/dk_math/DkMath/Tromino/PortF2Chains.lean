/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortDualityKernel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The F₂ chain scaffold of a port combinatorial map

This file records the finite, multigraph-safe chain spaces attached to a port
combinatorial map.  Edge cells are crossing orbits and face cells are face
orbits; in particular, parallel edges are not identified by a `SimpleGraph`.
The endpoint of this file is the chain condition `im ∂₂ ≤ ker ∂₁`.
-/

namespace DkMath.Tromino

abbrev PortF2 := ZMod 2

def PortEdgeCell {P : PortNetwork} (C : PortCrossing P) :=
  {E : Finset (PortNetworkPort P) // E ∈ portCrossingEdgeOrbits C}

def PortFaceCell {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :=
  {F : Finset (PortNetworkPort P) // F ∈ portFaceOrbits R C}

instance portEdgeCellFintype {P : PortNetwork} (C : PortCrossing P) :
    Fintype (PortEdgeCell C) :=
  Fintype.subtype (portCrossingEdgeOrbits C) (fun _ => Iff.rfl)

instance portFaceCellFintype {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : Fintype (PortFaceCell R C) :=
  Fintype.subtype (portFaceOrbits R C) (fun _ => Iff.rfl)

instance portEdgeCellDecidableEq {P : PortNetwork} (C : PortCrossing P) :
    DecidableEq (PortEdgeCell C) := fun a b =>
  if h : a.val = b.val then isTrue (Subtype.ext h)
  else isFalse (fun hab => h (congrArg Subtype.val hab))

instance portFaceCellDecidableEq {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : DecidableEq (PortFaceCell R C) := fun a b =>
  if h : a.val = b.val then isTrue (Subtype.ext h)
  else isFalse (fun hab => h (congrArg Subtype.val hab))

theorem PortEdgeCell_card {P : PortNetwork} (C : PortCrossing P) :
    Fintype.card (PortEdgeCell C) = portCrossingEdgeCount C := by
  exact Fintype.card_coe (portCrossingEdgeOrbits C)

theorem PortFaceCell_card {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :
    Fintype.card (PortFaceCell R C) = portFaceCount R C := by
  exact Fintype.card_coe (portFaceOrbits R C)

def edgeCellOfPort {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : PortEdgeCell C :=
  ⟨portCrossingEdgePair C p, portCrossingEdgePair_mem_orbits C p⟩

theorem edgeCellOfPort_cross {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : edgeCellOfPort C (C.cross p) = edgeCellOfPort C p := by
  apply Subtype.ext
  exact portCrossingEdgePair_cross_eq C p

theorem edgeCellOfPort_mem {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) : p ∈ (edgeCellOfPort C p).val :=
  portCrossingEdgePair_mem C p

def faceCellOfPort {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) : PortFaceCell R C :=
  ⟨portFaceOrbit R C p, portFaceOrbit_mem_orbits R C p⟩

theorem faceCellOfPort_mem {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (p : PortNetworkPort P) :
    p ∈ (faceCellOfPort R C p).val := by
  exact portFaceOrbit_contains R C p

abbrev PortVertexChain (P : PortNetwork) := Fin P.regionCount → PortF2
abbrev PortEdgeChain {P : PortNetwork} (C : PortCrossing P) :=
  PortEdgeCell C → PortF2
abbrev PortFaceChain {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) := PortFaceCell R C → PortF2

theorem finrank_portVertexChain {P : PortNetwork} :
    Module.finrank PortF2 (PortVertexChain P) = P.regionCount := by
  simp

theorem finrank_portEdgeChain {P : PortNetwork} (C : PortCrossing P) :
    Module.finrank PortF2 (PortEdgeChain C) = portCrossingEdgeCount C := by
  rw [Module.finrank_fintype_fun_eq_card]
  exact PortEdgeCell_card C

theorem finrank_portFaceChain {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :
    Module.finrank PortF2 (PortFaceChain R C) = portFaceCount R C := by
  rw [Module.finrank_fintype_fun_eq_card]
  exact PortFaceCell_card R C

def edgeVertexIncidence {P : PortNetwork} {C : PortCrossing P}
    (E : PortEdgeCell C) (r : Fin P.regionCount) : PortF2 :=
  (E.val.filter (fun p => p.1 = r)).card

theorem edgeVertexIncidence_generated {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) (r : Fin P.regionCount) :
    edgeVertexIncidence (edgeCellOfPort C p) r =
      (if p.1 = r then 1 else 0) + (if (C.cross p).1 = r then 1 else 0) := by
  classical
  change ((Finset.filter (fun q : PortNetworkPort P => q.1 = r) (portCrossingEdgePair C p)).card : PortF2) = _
  rw [Finset.card_filter]
  rw [show portCrossingEdgePair C p = {p, C.cross p} by rfl]
  by_cases h₁ : p.1 = r <;> by_cases h₂ : (C.cross p).1 = r
  all_goals
    have hne : p ∉ ({C.cross p} : Finset (PortNetworkPort P)) := by
      intro hp
      exact C.cross_ne p (Finset.mem_singleton.mp hp).symm
    rw [Finset.sum_insert hne, Finset.sum_singleton]
    norm_num [h₁, h₂]

theorem edgeVertexIncidence_two_support {P : PortNetwork} (C : PortCrossing P)
    (E : PortEdgeCell C) :
    ∑ r : Fin P.regionCount, edgeVertexIncidence E r = 0 := by
  classical
  rcases (portCrossingEdgeOrbits_mem_iff C E.val).mp E.property with ⟨p, hp⟩
  have hE : E = edgeCellOfPort C p := by
    apply Subtype.ext
    exact hp
  rw [hE]
  simp only [edgeVertexIncidence_generated]
  rw [Finset.sum_add_distrib]
  have hp : (∑ x : Fin P.regionCount, if p.1 = x then (1 : PortF2) else 0) = 1 := by
    simp only [eq_comm]
    rw [Finset.sum_ite_eq']
    simp
  have hcp : (∑ x : Fin P.regionCount, if (C.cross p).1 = x then (1 : PortF2) else 0) = 1 := by
    simp only [eq_comm]
    rw [Finset.sum_ite_eq']
    simp
  rw [hp, hcp]
  decide

def portBoundary1 {P : PortNetwork} (C : PortCrossing P) :
    PortEdgeChain C →ₗ[PortF2] PortVertexChain P :=
  { toFun := fun x r => ∑ E : PortEdgeCell C, x E * edgeVertexIncidence E r
    map_add' := by
      intro x y
      funext r
      simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      funext r
      simp [smul_eq_mul, mul_assoc, Finset.mul_sum] }

def PortCycleSpace {P : PortNetwork} (C : PortCrossing P) :
    Submodule PortF2 (PortEdgeChain C) := LinearMap.ker (portBoundary1 C)

def walkEdgeCoeff {P : PortNetwork} (C : PortCrossing P)
    (E : PortEdgeCell C) : List (PortNetworkPort P) → PortF2
  | [] => 0
  | p :: ps => (if p ∈ E.val then 1 else 0) + walkEdgeCoeff C E ps

def portWalkEdgeChain {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (W : PortRegionWalk C r s) : PortEdgeChain C :=
  fun E => walkEdgeCoeff C E W.edges

theorem walkEdgeCoeff_nil {P : PortNetwork} (C : PortCrossing P)
    (E : PortEdgeCell C) : walkEdgeCoeff C E [] = 0 := rfl

theorem walkEdgeCoeff_append {P : PortNetwork} (C : PortCrossing P)
    (E : PortEdgeCell C) (xs ys : List (PortNetworkPort P)) :
    walkEdgeCoeff C E (xs ++ ys) = walkEdgeCoeff C E xs + walkEdgeCoeff C E ys := by
  induction xs with
  | nil => simp [walkEdgeCoeff]
  | cons p xs ih => simp [walkEdgeCoeff, ih, add_assoc]

theorem portWalkEdgeChain_nil {P : PortNetwork} (C : PortCrossing P) (r : Fin P.regionCount) :
    portWalkEdgeChain (PortRegionWalk.nil C r) = 0 := by
  funext E
  rfl

theorem portWalkEdgeChain_append {P : PortNetwork} {C : PortCrossing P}
    {r s t : Fin P.regionCount} (W₁ : PortRegionWalk C r s)
    (W₂ : PortRegionWalk C s t) :
    portWalkEdgeChain (W₁.append W₂) = portWalkEdgeChain W₁ + portWalkEdgeChain W₂ := by
  funext E
  exact walkEdgeCoeff_append C E W₁.edges W₂.edges

theorem edgeCellOfPort_eq_iff {P : PortNetwork} (C : PortCrossing P)
    (p : PortNetworkPort P) (E : PortEdgeCell C) :
    edgeCellOfPort C p = E ↔ p ∈ E.val := by
  constructor
  · intro h
    rw [← h]
    exact edgeCellOfPort_mem C p
  · intro hp
    rcases (portCrossingEdgeOrbits_mem_iff C E.val).mp E.property with ⟨q, hq⟩
    have hpq : p ∈ portCrossingEdgePair C q := by simpa [hq] using hp
    have heq := portCrossingEdgePair_eq_of_mem C q p hpq
    apply Subtype.ext
    exact heq.trans hq.symm

def endpointVertexChain {P : PortNetwork} (r s v : Fin P.regionCount) : PortF2 :=
  (if v = r then 1 else 0) + (if v = s then 1 else 0)

theorem portBoundary1_walk_of_valid {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} {xs : List (PortNetworkPort P)}
    (hvalid : PortRegionWalk.Valid C r s xs) (v : Fin P.regionCount) :
    (∑ E : PortEdgeCell C, walkEdgeCoeff C E xs * edgeVertexIncidence E v) =
      endpointVertexChain r s v := by
  induction xs generalizing r s with
  | nil =>
      simp only [PortRegionWalk.Valid] at hvalid
      subst s
      by_cases h : v = r <;> simp only [walkEdgeCoeff, h, zero_mul, Finset.sum_const_zero,
        endpointVertexChain, ↓reduceIte]
      all_goals norm_num
      all_goals decide
  | cons p xs ih =>
      simp only [PortRegionWalk.Valid] at hvalid
      change (∑ E : PortEdgeCell C, ((if p ∈ E.val then (1 : PortF2) else 0) +
        walkEdgeCoeff C E xs) * edgeVertexIncidence E v) = _
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have hsingle :
          (∑ E : PortEdgeCell C, (if p ∈ E.val then (1 : PortF2) else 0) *
            edgeVertexIncidence E v) = edgeVertexIncidence (edgeCellOfPort C p) v := by
        have heq : ∀ E : PortEdgeCell C,
            (if p ∈ E.val then (1 : PortF2) else 0) =
              if edgeCellOfPort C p = E then 1 else 0 := by
          intro E
          by_cases h : p ∈ E.val
          · have he := (edgeCellOfPort_eq_iff C p E).2 h
            simp [h, he]
          · have he : edgeCellOfPort C p ≠ E := fun heq =>
              h ((edgeCellOfPort_eq_iff C p E).1 heq)
            simp [h, he]
        simp_rw [heq]
        simp
      rw [hsingle, edgeVertexIncidence_generated C p v, ih hvalid.2]
      rw [hvalid.1]
      have htwo : (2 : PortF2) = 0 := by decide
      by_cases hvr : v = r <;> by_cases hvc : v = (C.cross p).1 <;>
        simp [endpointVertexChain, hvr, hvc, eq_comm] <;> ring_nf <;> simp [htwo]


theorem endpointVertexChain_self {P : PortNetwork} (r s : Fin P.regionCount) :
    endpointVertexChain r s r = (if r = s then 1 else 0) + 1 := by
  by_cases h : r = s <;> simp [endpointVertexChain, h]

theorem portWalkEdgeChain_singleton {P : PortNetwork}
    (C : PortCrossing P) (p : PortNetworkPort P) :
    portWalkEdgeChain (PortRegionWalk.singleton C p) =
      fun E => if edgeCellOfPort C p = E then 1 else 0 := by
  funext E
  change walkEdgeCoeff C E [p] = _
  simp only [walkEdgeCoeff, add_zero]
  by_cases h : p ∈ E.val
  · have he := (edgeCellOfPort_eq_iff C p E).2 h
    simp [h, he]
  · have he : edgeCellOfPort C p ≠ E := fun heq =>
      h ((edgeCellOfPort_eq_iff C p E).1 heq)
    simp [h, he]

theorem portBoundary1_portWalkEdgeChain {P : PortNetwork}
    {C : PortCrossing P} {r s : Fin P.regionCount}
    (W : PortRegionWalk C r s) :
    portBoundary1 C (portWalkEdgeChain W) = endpointVertexChain r s := by
  funext v
  exact portBoundary1_walk_of_valid W.valid v

theorem closed_portWalkEdgeChain_mem_cycleSpace {P : PortNetwork}
    {C : PortCrossing P} {r : Fin P.regionCount}
    (W : PortRegionWalk C r r) :
    portWalkEdgeChain W ∈ PortCycleSpace C := by
  change portBoundary1 C (portWalkEdgeChain W) = 0
  rw [portBoundary1_portWalkEdgeChain W]
  have htwo : (2 : PortF2) = 0 := by decide
  funext v
  by_cases hv : v = r <;> simp only [endpointVertexChain, hv, ↓reduceIte, add_zero, Pi.zero_apply]
  norm_num
  exact htwo

def faceEdgeIncidence {P : PortNetwork} {R : PortLocalRotation P}
    {C : PortCrossing P} (F : PortFaceCell R C) (E : PortEdgeCell C) : PortF2 :=
  (F.val ∩ E.val).card

def faceBoundaryEdgeChain {P : PortNetwork} {R : PortLocalRotation P}
    {C : PortCrossing P} (F : PortFaceCell R C) : PortEdgeChain C :=
  fun E => faceEdgeIncidence F E

def portBoundary2 {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : PortFaceChain R C →ₗ[PortF2] PortEdgeChain C :=
  { toFun := fun y E => ∑ F : PortFaceCell R C, y F * faceEdgeIncidence F E
    map_add' := by
      intro x y
      funext E
      simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      funext E
      simp [smul_eq_mul, mul_assoc, Finset.mul_sum] }

def PortFaceBoundarySpace {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) : Submodule PortF2 (PortEdgeChain C) :=
  LinearMap.range (portBoundary2 R C)

theorem faceBoundary_basis {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) (F : PortFaceCell R C) :
    portBoundary2 R C (Pi.single F 1) = faceBoundaryEdgeChain F := by
  classical
  funext E
  change (∑ F' : PortFaceCell R C, (Pi.single F 1 : PortFaceChain R C) F' *
    faceEdgeIncidence F' E) = faceEdgeIncidence F E
  simp [Pi.single_apply]

theorem portBoundary2_zero {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :
    portBoundary2 R C 0 = 0 := by
  exact (portBoundary2 R C).map_zero

theorem walkEdgeCoeff_toFinset {P : PortNetwork} (C : PortCrossing P)
    (E : PortEdgeCell C) (xs : List (PortNetworkPort P)) (hnodup : xs.Nodup) :
    walkEdgeCoeff C E xs =
      (xs.toFinset ∩ E.val).card := by
  have hsum : walkEdgeCoeff C E xs =
      (List.map (fun p => if p ∈ E.val then (1 : PortF2) else 0) xs).sum := by
    induction xs with
    | nil => rfl
    | cons p xs ih =>
        simp [walkEdgeCoeff, ih hnodup.tail]
  rw [hsum]
  rw [← List.sum_toFinset (fun p => if p ∈ E.val then (1 : PortF2) else 0) hnodup]
  rw [Finset.sum_boole]
  rfl

theorem faceBoundaryEdgeChain_eq_walk {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p : PortNetworkPort P) :
    faceBoundaryEdgeChain (faceCellOfPort R C p) =
      portWalkEdgeChain (portFaceBoundaryWalk R C p) := by
  funext E
  change faceBoundaryEdgeChain (faceCellOfPort R C p) E =
    walkEdgeCoeff C E (portFaceBoundaryWalk R C p).edges
  rw [walkEdgeCoeff_toFinset C E _ (portFaceBoundaryWalk_edges_nodup R C p)]
  rw [portFaceBoundaryWalk_edges_toFinset]
  rfl

theorem faceBoundaryEdgeChain_cycle {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (F : PortFaceCell R C) :
    portBoundary1 C (faceBoundaryEdgeChain F) = 0 := by
  rcases (portFaceOrbits_mem_iff R C F.val).mp F.property with ⟨p, hp⟩
  have hF : F = faceCellOfPort R C p := by
    apply Subtype.ext
    exact hp
  rw [hF, faceBoundaryEdgeChain_eq_walk]
  funext v
  have h := portBoundary1_walk_of_valid
    (portFaceBoundaryWalk R C p).valid v
  change (∑ E : PortEdgeCell C, walkEdgeCoeff C E
    (portFaceBoundaryWalk R C p).edges * edgeVertexIncidence E v) = 0
  rw [h]
  have htwo : (2 : PortF2) = 0 := by decide
  by_cases hv : v = p.1 <;> simp only [endpointVertexChain, hv, ↓reduceIte, add_zero]
  norm_num
  exact htwo

theorem faceCellOfPort_eq_of_mem {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (p q : PortNetworkPort P) (hq : q ∈ portFaceOrbit R C p) :
    faceCellOfPort R C q = faceCellOfPort R C p := by
  apply Subtype.ext
  exact portFaceOrbit_eq_of_mem R C p q hq

theorem walkEdgeCoeff_cross_indicator {P : PortNetwork}
    (C : PortCrossing P) (E : PortEdgeCell C) (p : PortNetworkPort P) :
    (if C.cross p ∈ E.val then (1 : PortF2) else 0) =
      if p ∈ E.val then 1 else 0 := by
  by_cases h : p ∈ E.val
  · have hp : edgeCellOfPort C p = E :=
      (edgeCellOfPort_eq_iff C p E).2 h
    have hcp : edgeCellOfPort C (C.cross p) = E := by
      rw [edgeCellOfPort_cross]
      exact hp
    have hcross : C.cross p ∈ E.val :=
      (edgeCellOfPort_eq_iff C (C.cross p) E).1 hcp
    simp [h, hcross]
  · have hp : edgeCellOfPort C p ≠ E := by
      intro he
      exact h ((edgeCellOfPort_eq_iff C p E).1 he)
    have hcp : edgeCellOfPort C (C.cross p) ≠ E := by
      intro he
      apply hp
      rw [edgeCellOfPort_cross] at he
      exact he
    have hcross : C.cross p ∉ E.val := by
      intro hm
      exact hcp ((edgeCellOfPort_eq_iff C (C.cross p) E).2 hm)
    simp [h, hcross]

theorem walkEdgeCoeff_reverseEdges {P : PortNetwork}
    (C : PortCrossing P) (E : PortEdgeCell C)
    (xs : List (PortNetworkPort P)) :
    walkEdgeCoeff C E (PortRegionWalk.reverseEdges C xs) =
      walkEdgeCoeff C E xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      simp only [PortRegionWalk.reverseEdges, List.reverse_cons,
        List.map_append, List.map_singleton]
      rw [walkEdgeCoeff_append]
      change walkEdgeCoeff C E (PortRegionWalk.reverseEdges C xs) +
        walkEdgeCoeff C E [C.cross p] = walkEdgeCoeff C E (p :: xs)
      rw [ih]
      simp [walkEdgeCoeff, walkEdgeCoeff_cross_indicator]
      ac_rfl

theorem portWalkEdgeChain_reverse {P : PortNetwork} {C : PortCrossing P}
    {r s : Fin P.regionCount} (W : PortRegionWalk C r s) :
    portWalkEdgeChain W.reverse = portWalkEdgeChain W := by
  funext E
  exact walkEdgeCoeff_reverseEdges C E W.edges

theorem portBoundary2_as_sum_basis {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P)
    (y : PortFaceChain R C) :
    portBoundary2 R C y =
      ∑ F : PortFaceCell R C, y F • faceBoundaryEdgeChain F := by
  funext E
  simp [portBoundary2, faceBoundaryEdgeChain, smul_eq_mul, Finset.sum_apply]

theorem portBoundary1_boundary2 {P : PortNetwork} (R : PortLocalRotation P)
    (C : PortCrossing P) :
    (portBoundary1 C).comp (portBoundary2 R C) = 0 := by
  apply LinearMap.ext
  intro y
  change portBoundary1 C (portBoundary2 R C y) = 0
  rw [portBoundary2_as_sum_basis]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro F hF
  rw [map_smul, faceBoundaryEdgeChain_cycle R C F]
  simp

theorem faceBoundarySpace_le_cycleSpace {P : PortNetwork}
    (R : PortLocalRotation P) (C : PortCrossing P) :
    PortFaceBoundarySpace R C ≤ PortCycleSpace C := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  change portBoundary1 C (portBoundary2 R C y) = 0
  simpa using congrArg (fun f => f y) (portBoundary1_boundary2 R C)

end DkMath.Tromino
