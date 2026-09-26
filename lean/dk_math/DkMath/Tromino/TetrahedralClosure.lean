/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortV4Chains

#print "file: DkMath.Tromino.TetrahedralClosure"

namespace DkMath.Tromino

open scoped BigOperators

abbrev TetraFace := TrominoState

def tetraFaceColor : TetraFace -> TrominoState := id

theorem tetraFace_card : Fintype.card TetraFace = 4 := by
  rw [Fintype.card_eq_nat_card]
  exact card_state

abbrev TetraEdge := {E : Finset TetraFace // E.card = 2}

instance tetraEdgeFintype : Fintype TetraEdge := inferInstance
instance tetraEdgeDecidableEq : DecidableEq TetraEdge := inferInstance

def tetraEdgeBetween (a b : TetraFace) (h : a ≠ b) : TetraEdge :=
  ⟨{a, b}, by simp [h]⟩

theorem tetraEdge_card : Fintype.card TetraEdge = 6 := by
  decide

def tetraEdgeDelta (E : TetraEdge) : TrominoState :=
  Finset.sum E.val id

theorem tetraEdgeDelta_between (a b : TetraFace) (h : a ≠ b) :
    tetraEdgeDelta (tetraEdgeBetween a b h) = a + b := by
  simp [tetraEdgeDelta, tetraEdgeBetween, h]

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

theorem tetraEdgeDelta_eq_deltaA_or_deltaB_or_deltaC (E : TetraEdge) :
    tetraEdgeDelta E = deltaA ∨ tetraEdgeDelta E = deltaB ∨
      tetraEdgeDelta E = deltaC :=
  nonzeroState_eq_deltaA_or_deltaB_or_deltaC _
    (tetraEdgeDelta_ne_zero E)

def tetraEdgesWithDelta (d : TrominoState) : Finset TetraEdge :=
  Finset.univ.filter (fun E => tetraEdgeDelta E = d)

theorem tetraEdgesWithDelta_deltaA_card :
    (tetraEdgesWithDelta deltaA).card = 2 := by
  decide

theorem tetraEdgesWithDelta_deltaB_card :
    (tetraEdgesWithDelta deltaB).card = 2 := by
  decide

theorem tetraEdgesWithDelta_deltaC_card :
    (tetraEdgesWithDelta deltaC).card = 2 := by
  decide

theorem tetraEdgeDelta_image :
    Finset.univ.image tetraEdgeDelta = {deltaA, deltaB, deltaC} := by
  decide

theorem tetraEdge_mem_delta_partition (E : TetraEdge) :
    E ∈ tetraEdgesWithDelta deltaA ∨ E ∈ tetraEdgesWithDelta deltaB ∨
      E ∈ tetraEdgesWithDelta deltaC := by
  rcases tetraEdgeDelta_eq_deltaA_or_deltaB_or_deltaC E with hA | hB | hC
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)
  · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩))
  · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩))

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

abbrev TetraDirection := {d : TrominoState // d ≠ 0}

theorem tetraDirection_card : Fintype.card TetraDirection = 3 := by
  decide

def tetraOtherFace (c : TetraFace) (d : TetraDirection) : TetraFace :=
  c + d.1

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

def tetraIncidentEdges (c : TetraFace) : Finset TetraEdge :=
  Finset.univ.filter (fun E => c ∈ E.val)

def tetraIncidentEdge (c : TetraFace) (d : TetraDirection) : TetraEdge :=
  tetraEdgeBetween c (tetraOtherFace c d) (by
    intro h
    exact tetraOtherFace_ne c d h.symm)

theorem tetraIncidentEdge_mem (c : TetraFace) (d : TetraDirection) :
    tetraIncidentEdge c d ∈ tetraIncidentEdges c := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simp [tetraIncidentEdge, tetraEdgeBetween]

theorem tetraIncidentEdges_card (c : TetraFace) :
    (tetraIncidentEdges c).card = 3 := by
  fin_cases c <;> decide

theorem tetraIncidentEdges_delta_image (c : TetraFace) :
    (tetraIncidentEdges c).image tetraEdgeDelta = {deltaA, deltaB, deltaC} := by
  fin_cases c <;> decide

def tetraRollBottom (c : TetraFace) (d : TetraDirection) : TetraFace :=
  tetraOtherFace c d

theorem tetraRollBottom_ne (c : TetraFace) (d : TetraDirection) :
    tetraRollBottom c d ≠ c :=
  tetraOtherFace_ne c d

theorem tetraRollBottom_twice (c : TetraFace) (d : TetraDirection) :
    tetraRollBottom (tetraRollBottom c d) d = c := by
  simp [tetraRollBottom, tetraOtherFace, state_add_self, add_assoc]

theorem tetraRollBottom_image (c : TetraFace) :
    (Finset.univ : Finset TetraDirection).image (tetraRollBottom c) =
      Finset.univ.erase c :=
  tetraOtherFace_image c

structure TetraRollStep where
  bottom : TetraFace
  direction : TetraDirection

deriving instance Fintype for TetraRollStep
deriving instance DecidableEq for TetraRollStep

theorem tetraRollStep_card : Fintype.card TetraRollStep = 12 := by
  decide

def tetraRollEdge (c : TetraFace) (d : TetraDirection) : TetraEdge :=
  tetraIncidentEdge c d

theorem tetraRollEdge_delta (c : TetraFace) (d : TetraDirection) :
    tetraEdgeDelta (tetraRollEdge c d) = d.1 := by
  change tetraEdgeDelta (tetraIncidentEdge c d) = d.1
  change tetraEdgeDelta (tetraEdgeBetween c (tetraOtherFace c d) _) = d.1
  rw [tetraEdgeDelta_between]
  calc
    c + (c + d.1) = d.1 + (c + c) := by ac_rfl
    _ = d.1 := by rw [state_add_self, add_zero]

theorem tetraRollEdge_reverse (c : TetraFace) (d : TetraDirection) :
    tetraRollEdge (tetraRollBottom c d) d = tetraRollEdge c d := by
  apply Subtype.ext
  simp [tetraRollEdge, tetraIncidentEdge, tetraEdgeBetween, tetraRollBottom,
    tetraOtherFace, state_add_self, add_assoc, Finset.pair_comm]

theorem tetraEdge_delta_nonzero_finite (E : TetraEdge) :
    tetraEdgeDelta E = deltaA ∨ tetraEdgeDelta E = deltaB ∨
      tetraEdgeDelta E = deltaC :=
  tetraEdgeDelta_eq_deltaA_or_deltaB_or_deltaC E

theorem three_nonzero_sum_zero_iff_pairwise_distinct
    {a b c : TrominoState} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a + b + c = 0 ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC a ha with rfl | rfl | rfl <;>
    rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC b hb with rfl | rfl | rfl <;>
      rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC c hc with rfl | rfl | rfl <;>
        decide

theorem three_nonzero_sum_zero_iff_delta_finset
    {a b c : TrominoState} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a + b + c = 0 ↔ ({a, b, c} : Finset TrominoState) = ({deltaA, deltaB, deltaC} : Finset TrominoState) := by
  rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC a ha with rfl | rfl | rfl <;>
    rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC b hb with rfl | rfl | rfl <;>
      rcases nonzeroState_eq_deltaA_or_deltaB_or_deltaC c hc with rfl | rfl | rfl <;>
        decide

theorem deltaA_add_deltaB_add_deltaC_eq_zero_reused :
    deltaA + deltaB + deltaC = 0 :=
  deltaA_add_deltaB_add_deltaC_eq_zero

def tetraRollBottomList : TetraFace → List TetraDirection → TetraFace
  | c, [] => c
  | c, d :: ds => tetraRollBottomList (tetraRollBottom c d) ds

theorem tetraRollBottomList_eq_add_sum (c : TetraFace)
    (ds : List TetraDirection) :
    tetraRollBottomList c ds =
      c + (ds.map (fun d => d.1)).sum := by
  induction ds generalizing c with
  | nil => simp [tetraRollBottomList]
  | cons d ds ih =>
      simp [tetraRollBottomList, ih, tetraRollBottom, tetraOtherFace, add_assoc]

theorem tetraRollBottomList_append (c : TetraFace)
    (xs ys : List TetraDirection) :
    tetraRollBottomList c (xs ++ ys) =
      tetraRollBottomList (tetraRollBottomList c xs) ys := by
  rw [tetraRollBottomList_eq_add_sum, tetraRollBottomList_eq_add_sum,
    tetraRollBottomList_eq_add_sum]
  simp [add_assoc]

end DkMath.Tromino
