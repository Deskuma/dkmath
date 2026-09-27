/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortV4Chains

#print "file: DkMath.Tromino.TetrahedralClosure"

namespace DkMath.Tromino

open scoped BigOperators

/-!
# The finite tetrahedral model

The four elements of `TrominoState` are used as the four tetrahedral faces.
An edge is a two-element face subset, and its V4 delta is the sum of its
endpoints.  The three nonzero deltas are therefore the three edge directions
through a face.  Rolling across these directions gives a finite local model
for the triangular face condition; it is a combinatorial calibration layer,
not a global coloring theorem.
-/

/-- Identify the tetrahedral face carrier with the V4 color carrier. -/
abbrev TetraFace := TrominoState

/-- The color carried by a tetrahedral face. -/
def tetraFaceColor : TetraFace -> TrominoState := id

/-- The tetrahedron has four faces. -/
theorem tetraFace_card : Fintype.card TetraFace = 4 := by
  rw [Fintype.card_eq_nat_card]
  exact card_state

/-- A tetrahedral edge is a pair of distinct faces. -/
abbrev TetraEdge := {E : Finset TetraFace // E.card = 2}

instance tetraEdgeFintype : Fintype TetraEdge := inferInstance
instance tetraEdgeDecidableEq : DecidableEq TetraEdge := inferInstance

/-- Construct the edge joining two distinct tetrahedral faces. -/
def tetraEdgeBetween (a b : TetraFace) (h : a ≠ b) : TetraEdge :=
  ⟨{a, b}, by simp [h]⟩

/-- The tetrahedron has six edges. -/
theorem tetraEdge_card : Fintype.card TetraEdge = 6 := by
  decide

/-- The V4 delta assigned to a tetrahedral edge. -/
def tetraEdgeDelta (E : TetraEdge) : TrominoState :=
  Finset.sum E.val id

/-- The delta of an edge is the sum of its two face colors. -/
theorem tetraEdgeDelta_between (a b : TetraFace) (h : a ≠ b) :
    tetraEdgeDelta (tetraEdgeBetween a b h) = a + b := by
  simp [tetraEdgeDelta, tetraEdgeBetween, h]

/-- Every tetrahedral edge has a nonzero V4 delta. -/
theorem tetraEdgeDelta_ne_zero (E : TetraEdge) :
    tetraEdgeDelta E ≠ 0 := by
  rcases Finset.card_eq_two.mp E.property with ⟨a, b, hab, hE⟩
  change (Finset.sum E.val id) ≠ 0
  rw [hE]
  simp only [id_eq, Finset.mem_singleton, hab, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, ne_eq]
  intro hz
  apply hab
  exact add_left_cancel ((state_add_self a).trans hz.symm)

/-- Every tetrahedral edge delta is one of the three nonzero states. -/
theorem tetraEdgeDelta_eq_deltaA_or_deltaB_or_deltaC (E : TetraEdge) :
    tetraEdgeDelta E = deltaA ∨ tetraEdgeDelta E = deltaB ∨
      tetraEdgeDelta E = deltaC :=
  nonzeroState_eq_deltaA_or_deltaB_or_deltaC _
    (tetraEdgeDelta_ne_zero E)

/-- The finite set of tetrahedral edges with prescribed delta. -/
def tetraEdgesWithDelta (d : TrominoState) : Finset TetraEdge :=
  Finset.univ.filter (fun E => tetraEdgeDelta E = d)

/-- Each nonzero delta occurs on exactly two tetrahedral edges. -/
theorem tetraEdgesWithDelta_deltaA_card :
    (tetraEdgesWithDelta deltaA).card = 2 := by
  decide

/-- The delta-B edge fiber has cardinality two. -/
theorem tetraEdgesWithDelta_deltaB_card :
    (tetraEdgesWithDelta deltaB).card = 2 := by
  decide

/-- The delta-C edge fiber has cardinality two. -/
theorem tetraEdgesWithDelta_deltaC_card :
    (tetraEdgesWithDelta deltaC).card = 2 := by
  decide

/-- The image of the edge-delta map is exactly the three nonzero states. -/
theorem tetraEdgeDelta_image :
    Finset.univ.image tetraEdgeDelta = {deltaA, deltaB, deltaC} := by
  decide

/-- Every edge belongs to exactly one nonzero-delta fiber. -/
theorem tetraEdge_mem_delta_partition (E : TetraEdge) :
    E ∈ tetraEdgesWithDelta deltaA ∨ E ∈ tetraEdgesWithDelta deltaB ∨
      E ∈ tetraEdgesWithDelta deltaC := by
  rcases tetraEdgeDelta_eq_deltaA_or_deltaB_or_deltaC E with hA | hB | hC
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)
  · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩))
  · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩))

/-- Distinct edges in one delta fiber are disjoint as face subsets. -/
theorem tetraEdgesWithDelta_pairwise_disjoint {d : TrominoState}
    {E F : TetraEdge} (hE : E ∈ tetraEdgesWithDelta d)
    (hF : F ∈ tetraEdgesWithDelta d) (hneq : E ≠ F) :
    Disjoint E.val F.val := by
  apply Finset.disjoint_left.mpr
  intro x hxE hxF
  rcases Finset.card_eq_two.mp E.property with ⟨a, b, hab, hEs⟩
  rcases Finset.card_eq_two.mp F.property with ⟨c, e, hce, hFs⟩
  have hEd := (Finset.mem_filter.mp hE).2
  have hFd := (Finset.mem_filter.mp hF).2
  rw [tetraEdgeDelta, hEs] at hEd
  rw [tetraEdgeDelta, hFs] at hFd
  -- simp [hab] at hEd
  simp only [id_eq, Finset.mem_singleton, hab, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton] at hEd
  simp [hce] at hFd
  rw [hEs] at hxE
  rw [hFs] at hxF
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxE hxF
  rcases hxE with hxa | hxb
  · rcases hxF with hxc | hxe
    · subst x
      subst c
      have hbe : b = e := by
        apply add_left_cancel (a := a)
        exact hEd.trans hFd.symm
      apply hneq
      apply Subtype.ext
      rw [hEs, hFs]
      simp [hbe]
    · subst x
      subst e
      have hbc : b = c := by
        apply add_left_cancel (a := a)
        calc
          a + b = d := hEd
          _ = c + a := hFd.symm
          _ = a + c := add_comm c a
      apply hneq
      apply Subtype.ext
      rw [hEs, hFs]
      simp [hbc, Finset.pair_comm]
  · rcases hxF with hxc | hxe
    · subst x
      subst c
      have hae : a = e := by
        apply add_left_cancel (a := b)
        calc
          b + a = a + b := add_comm b a
          _ = d := hEd
          _ = b + e := hFd.symm
      apply hneq
      apply Subtype.ext
      rw [hEs, hFs]
      simp [hae, Finset.pair_comm]
    · subst x
      subst e
      have hac : a = c := by
        apply add_left_cancel (a := b)
        calc
          b + a = a + b := add_comm b a
          _ = d := hEd
          _ = c + b := hFd.symm
          _ = b + c := add_comm c b
      apply hneq
      apply Subtype.ext
      rw [hEs, hFs]
      simp [hac]

/-- The finite carrier of nonzero tetrahedral rolling directions. -/
abbrev TetraDirection := {d : TrominoState // d ≠ 0}

/-- There are three nonzero rolling directions. -/
theorem tetraDirection_card : Fintype.card TetraDirection = 3 := by
  decide

/-- The face reached from `c` in direction `d`. -/
def tetraOtherFace (c : TetraFace) (d : TetraDirection) : TetraFace :=
  c + d.1

/-- A roll direction never returns the current face immediately. -/
theorem tetraOtherFace_ne (c : TetraFace) (d : TetraDirection) :
    tetraOtherFace c d ≠ c := by
  intro h
  change c + d.1 = c at h
  apply d.2
  calc
    d.1 = 0 + d.1 := by simp
    _ = (c + c) + d.1 := by rw [state_add_self]
    _ = c + (c + d.1) := by ac_rfl
    _ = c + c := by rw [h]
    _ = 0 := state_add_self c

/-- The three directions enumerate the three faces other than `c`. -/
def tetraOtherFaceEquiv (c : TetraFace) :
    TetraDirection ≃ {q : TetraFace // q ≠ c} where
  toFun d := ⟨tetraOtherFace c d, tetraOtherFace_ne c d⟩
  invFun q := ⟨q.1 + c, by
    intro h
    apply q.2
    exact add_right_cancel (h.trans (state_add_self c).symm)⟩
  left_inv d := by
    apply Subtype.ext
    dsimp [tetraOtherFace]
    calc
      c + d.1 + c = d.1 + (c + c) := by ac_rfl
      _ = d.1 := by rw [state_add_self, add_zero]
  right_inv q := by
    apply Subtype.ext
    dsimp [tetraOtherFace]
    calc
      c + (q.1 + c) = q.1 + (c + c) := by ac_rfl
      _ = q.1 := by rw [state_add_self, add_zero]

/-- The image of the direction enumeration is the complement of `c`. -/
theorem tetraOtherFace_image (c : TetraFace) :
    (Finset.univ : Finset TetraDirection).image (tetraOtherFace c) =
      Finset.univ.erase c := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨d, hd, rfl⟩
    simp [tetraOtherFace_ne]
  · intro hq
    have hne : q ≠ c := (Finset.mem_erase.mp hq).1
    let d : TetraDirection := (tetraOtherFaceEquiv c).symm ⟨q, hne⟩
    refine Finset.mem_image.mpr ⟨d, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val ((tetraOtherFaceEquiv c).apply_symm_apply ⟨q, hne⟩)

/-- The three edges incident to a tetrahedral face. -/
def tetraIncidentEdges (c : TetraFace) : Finset TetraEdge :=
  Finset.univ.filter (fun E => c ∈ E.val)

/-- The incident edge selected by a face and a rolling direction. -/
def tetraIncidentEdge (c : TetraFace) (d : TetraDirection) : TetraEdge :=
  tetraEdgeBetween c (tetraOtherFace c d) (by
    intro h
    exact tetraOtherFace_ne c d h.symm)

/-- The selected incident edge belongs to the incident-edge set. -/
theorem tetraIncidentEdge_mem (c : TetraFace) (d : TetraDirection) :
    tetraIncidentEdge c d ∈ tetraIncidentEdges c := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simp [tetraIncidentEdge, tetraEdgeBetween]

/-- Every tetrahedral face has three incident edges. -/
theorem tetraIncidentEdges_card (c : TetraFace) :
    (tetraIncidentEdges c).card = 3 := by
  fin_cases c <;> decide

/-- The three incident edges realize all three nonzero deltas. -/
theorem tetraIncidentEdges_delta_image (c : TetraFace) :
    (tetraIncidentEdges c).image tetraEdgeDelta = {deltaA, deltaB, deltaC} := by
  fin_cases c <;> decide

/-- The bottom face after rolling across one incident edge. -/
def tetraRollBottom (c : TetraFace) (d : TetraDirection) : TetraFace :=
  tetraOtherFace c d

/-- A roll changes the bottom face. -/
theorem tetraRollBottom_ne (c : TetraFace) (d : TetraDirection) :
    tetraRollBottom c d ≠ c :=
  tetraOtherFace_ne c d

/-- Rolling twice across the same edge returns to the original bottom. -/
theorem tetraRollBottom_twice (c : TetraFace) (d : TetraDirection) :
    tetraRollBottom (tetraRollBottom c d) d = c := by
  simp [tetraRollBottom, tetraOtherFace, state_add_self, add_assoc]

/-- The three rolls from a face reach exactly the other faces. -/
theorem tetraRollBottom_image (c : TetraFace) :
    (Finset.univ : Finset TetraDirection).image (tetraRollBottom c) =
      Finset.univ.erase c :=
  tetraOtherFace_image c

/-- A local tetrahedral roll step records bottom, direction, and edge delta. -/
structure TetraRollStep where
  bottom : TetraFace
  direction : TetraDirection

deriving instance Fintype for TetraRollStep
deriving instance DecidableEq for TetraRollStep

/-- There are twelve oriented local roll steps. -/
theorem tetraRollStep_card : Fintype.card TetraRollStep = 12 := by
  decide

/-- The edge crossed by a tetrahedral roll. -/
def tetraRollEdge (c : TetraFace) (d : TetraDirection) : TetraEdge :=
  tetraIncidentEdge c d

/-- A roll's edge delta is the direction used to make the roll. -/
theorem tetraRollEdge_delta (c : TetraFace) (d : TetraDirection) :
    tetraEdgeDelta (tetraRollEdge c d) = d.1 := by
  change tetraEdgeDelta (tetraIncidentEdge c d) = d.1
  change tetraEdgeDelta (tetraEdgeBetween c (tetraOtherFace c d) _) = d.1
  rw [tetraEdgeDelta_between]
  calc
    c + (c + d.1) = d.1 + (c + c) := by ac_rfl
    _ = d.1 := by rw [state_add_self, add_zero]

/-- Reversing a roll preserves the underlying crossed edge. -/
theorem tetraRollEdge_reverse (c : TetraFace) (d : TetraDirection) :
    tetraRollEdge (tetraRollBottom c d) d = tetraRollEdge c d := by
  apply Subtype.ext
  simp [tetraRollEdge, tetraIncidentEdge, tetraEdgeBetween, tetraRollBottom,
    tetraOtherFace, state_add_self, add_assoc, Finset.pair_comm]

/-- Edge deltas are nonzero by the finite tetrahedral classification. -/
theorem tetraEdge_delta_nonzero_finite (E : TetraEdge) :
    tetraEdgeDelta E = deltaA ∨ tetraEdgeDelta E = deltaB ∨
      tetraEdgeDelta E = deltaC :=
  tetraEdgeDelta_eq_deltaA_or_deltaB_or_deltaC E

/-- Three nonzero V4 states sum to zero exactly when they are pairwise distinct. -/
theorem three_nonzero_sum_zero_iff_pairwise_distinct
    {a b c : TrominoState} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a + b + c = 0 ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC a ha with rfl | rfl | rfl <;>
    rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC b hb with rfl | rfl | rfl <;>
      rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC c hc with rfl | rfl | rfl <;>
        decide

/-- The same condition is equivalent to using all three nonzero states once. -/
theorem three_nonzero_sum_zero_iff_delta_finset
    {a b c : TrominoState} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a + b + c = 0 ↔ ({a, b, c} : Finset TrominoState) = ({deltaA, deltaB, deltaC} : Finset TrominoState) := by
  rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC a ha with rfl | rfl | rfl <;>
    rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC b hb with rfl | rfl | rfl <;>
      rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC c hc with rfl | rfl | rfl <;>
        decide

/-- The three nonzero V4 states have total sum zero. -/
theorem deltaA_add_deltaB_add_deltaC_eq_zero_reused :
    deltaA + deltaB + deltaC = 0 :=
  deltaA_add_deltaB_add_deltaC_eq_zero

/-- Iterate tetrahedral rolling along a finite direction list. -/
def tetraRollBottomList : TetraFace → List TetraDirection → TetraFace
  | c, [] => c
  | c, d :: ds => tetraRollBottomList (tetraRollBottom c d) ds

/-- Iterated rolling is translation by the sum of direction deltas. -/
theorem tetraRollBottomList_eq_add_sum (c : TetraFace)
    (ds : List TetraDirection) :
    tetraRollBottomList c ds =
      c + (ds.map (fun d => d.1)).sum := by
  induction ds generalizing c with
  | nil => simp [tetraRollBottomList]
  | cons d ds ih =>
      simp [tetraRollBottomList, ih, tetraRollBottom, tetraOtherFace, add_assoc]

/-- Rolling along an appended list factors into two successive rolls. -/
theorem tetraRollBottomList_append (c : TetraFace)
    (xs ys : List TetraDirection) :
    tetraRollBottomList c (xs ++ ys) =
      tetraRollBottomList (tetraRollBottomList c xs) ys := by
  rw [tetraRollBottomList_eq_add_sum, tetraRollBottomList_eq_add_sum,
    tetraRollBottomList_eq_add_sum]
  simp [add_assoc]

end DkMath.Tromino
