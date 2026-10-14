/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RestorationFlipTransport

#print "file: DkMathTest.Tromino.RestorationFlipTransportRegression"

namespace DkMathTest.Tromino

open DkMath.Tromino

/-! ## A. A finite local diagonal replacement -/

abbrev FlipVertex := Fin 5

def flipParentGraph : SimpleGraph FlipVertex :=
  SimpleGraph.fromRel (fun x y =>
    ¬ SameUndirectedEdge x y (2 : FlipVertex) 3)

def flipChildGraph : SimpleGraph FlipVertex :=
  SimpleGraph.fromRel (fun x y =>
    ¬ SameUndirectedEdge x y (0 : FlipVertex) 1)

def flipAssignment : FlipVertex → TrominoState :=
  fun v => if v = 0 then 0 else if v = 1 then ⟨0, 1⟩
    else if v = 2 then ⟨1, 0⟩ else if v = 3 then ⟨1, 1⟩ else 0

def flipColored : FlipVertex → Prop :=
  fun v => v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3

theorem flip_assignment_ne_of_colored {x y : FlipVertex}
    (hx : flipColored x) (hy : flipColored y) (hxy : x ≠ y) :
    flipAssignment x ≠ flipAssignment y := by
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl
  all_goals first
    | exact (hxy rfl).elim
    | decide

theorem flipReplacement :
    SingleEdgeReplacement flipParentGraph flipChildGraph
      (0 : FlipVertex) 1 2 3 where
  old_edge := by
    rw [flipParentGraph, SimpleGraph.fromRel_adj]
    simp [SameUndirectedEdge]
  new_nonedge := by
    intro h
    rw [flipParentGraph, SimpleGraph.fromRel_adj] at h
    simp [SameUndirectedEdge] at h
  adj_iff := by
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [flipParentGraph, flipChildGraph, SimpleGraph.fromRel_adj,
        SameUndirectedEdge]

theorem flip_parent_proper :
    ProperOnColored flipParentGraph flipColored flipAssignment := by
  intro x y hxy hx hy
  exact flip_assignment_ne_of_colored hx hy
    (flipParentGraph.ne_of_adj hxy)

theorem flip_child_proper :
    ProperOnColored flipChildGraph flipColored flipAssignment := by
  intro x y hxy hx hy
  exact flip_assignment_ne_of_colored hx hy
    (flipChildGraph.ne_of_adj hxy)

theorem flip_old_diagonal_absent :
    ¬ flipChildGraph.Adj (0 : FlipVertex) 1 :=
  flipReplacement.old_edge_absent

theorem flip_new_diagonal_present :
    flipChildGraph.Adj (2 : FlipVertex) 3 :=
  flipReplacement.new_edge_present

theorem flip_unaffected_adjacency :
    flipChildGraph.Adj (0 : FlipVertex) 4 ↔
      flipParentGraph.Adj (0 : FlipVertex) 4 := by
  apply flipReplacement.adj_unchanged
  · simp [SameUndirectedEdge]
  · simp [SameUndirectedEdge]

theorem flip_parent_proper_transfers :
    ProperOnColored flipChildGraph flipColored flipAssignment := by
  apply properOnColored_parent_to_child flipReplacement flip_parent_proper
  intro _ _
  decide

theorem flip_child_proper_transfers :
    ProperOnColored flipParentGraph flipColored flipAssignment := by
  apply properOnColored_child_to_parent flipReplacement flip_child_proper
  intro _ _
  decide

theorem flip_missingAt_locality :
    MissingAt flipParentGraph flipColored flipAssignment (4 : FlipVertex) ↔
      MissingAt flipChildGraph flipColored flipAssignment (4 : FlipVertex) := by
  apply missingAt_flip_locality flipReplacement <;>
    simp

/-! ## B. A two-state rooted child sector and its transport packet -/

def flipMutable : FlipVertex → Prop := fun v => v = 2 ∨ v = 3

def flipRemaining : FlipVertex → Prop := fun _ => False

def flipBase : FlipVertex → TrominoState :=
  fun v => if v = 1 then ⟨0, 1⟩ else 0

def flipParentContext : RestorationContext flipParentGraph flipMutable where
  colored := flipColored
  remaining := flipRemaining
  base := flipBase
  mutable_colored := by
    intro v hv
    rcases hv with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  remaining_uncolored := by
    intro v hv
    change False at hv
    have hfalse : False := hv
    exact hfalse.elim

def flipChildContext : RestorationContext flipChildGraph flipMutable where
  colored := flipColored
  remaining := flipRemaining
  base := flipBase
  mutable_colored := by
    intro v hv
    rcases hv with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  remaining_uncolored := by
    intro v hv
    change False at hv
    have hfalse : False := hv
    exact hfalse.elim

def flipRoot : MutableCoordinates flipMutable := fun v =>
  if v.1 = 2 then ⟨1, 0⟩ else ⟨1, 1⟩

set_option linter.flexible false in
theorem flip_root_proper : flipChildContext.Proper flipRoot := by
  intro x y hxy hx hy
  fin_cases x <;> fin_cases y <;>
    simp_all [flipChildContext, flipChildGraph, flipColored, flipBase,
      flipRoot, realize, flipMutable, SimpleGraph.fromRel_adj,
      SameUndirectedEdge] <;> decide

theorem flip_root_admissible :
    RestorationAdmissible flipChildContext flipRoot := by
  refine ⟨flip_root_proper, ?_⟩
  intro v hv
  change False at hv
  have hfalse : False := hv
  exact hfalse.elim

theorem flip_parent_proper_of_child_proper
    {state : MutableCoordinates flipMutable}
    (hchild : flipChildContext.Proper state) :
    flipParentContext.Proper state := by
  intro x y hxy hx hy
  by_cases hold : SameUndirectedEdge x y (0 : FlipVertex) 1
  · rcases hold with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [flipParentContext, flipBase, realize, flipMutable] using
        (show (0 : TrominoState) ≠ ⟨0, 1⟩ by decide)
    · simp [flipParentContext, flipBase, realize, flipMutable]
  · have hchildxy : flipChildGraph.Adj x y :=
      (flipReplacement.adj_iff x y).mpr (Or.inl ⟨hxy, hold⟩)
    exact hchild hchildxy hx hy

theorem flipRestorationFlip :
    RestorationFlipContext (0 : FlipVertex) 1 2 3
      flipParentContext flipChildContext where
  replacement := flipReplacement
  same_colored := rfl
  same_remaining := rfl

theorem flip_parent_on_child_chamber {state : MutableCoordinates flipMutable}
    (hreach : Reachable (AdmissibleRestorationStep flipChildContext)
      flipRoot state) :
    RestorationAdmissible flipParentContext state := by
  have hadm : RestorationAdmissible flipChildContext state :=
    restricted_reachable_target_admissible flip_root_admissible hreach
  exact ⟨flip_parent_proper_of_child_proper hadm.1, by
    intro v hv
    change False at hv
    have hfalse : False := hv
    exact hfalse.elim⟩

theorem flipCertificate : ExactRestorationSectorCertificate
    flipRestorationFlip flipRoot where
  child_root_admissible := flip_root_admissible
  parent_on_child_chamber := flip_parent_on_child_chamber

theorem flip_exact_sector :
    ∀ state, Reachable (AdmissibleRestorationStep flipChildContext)
      flipRoot state ↔
      AdmissibleChamber (CoordinateOnePointStep flipMutable)
        (TransportAdmissible flipParentContext flipChildContext)
        flipRoot state := by
  intro state
  exact exactRestorationSector_iff flipRestorationFlip flipCertificate

theorem flipRootedPacket :
    RootedChamberTransport
      (RootedChildChamber flipChildContext flipRoot)
      (MutableCoordinates flipMutable)
      (RootedChildChamberStep flipChildContext)
      (CoordinateOnePointStep flipMutable)
      (TransportAdmissible flipParentContext flipChildContext)
      (fun state => state.1)
      ⟨flipRoot, reachable_refl _ flipRoot⟩ flipRoot :=
  exactRestorationSectorTransport flipRestorationFlip flipCertificate

theorem flipRootedPacket_chamber (state : RootedChildChamber flipChildContext flipRoot) :
    Reachable (RootedChildChamberStep flipChildContext)
        ⟨flipRoot, reachable_refl _ flipRoot⟩ state ↔
      AdmissibleChamber (CoordinateOnePointStep flipMutable)
        (TransportAdmissible flipParentContext flipChildContext)
        flipRoot state.1 :=
  RootedChamberTransport.reachable_iff_admissibleChamber flipRootedPacket

end DkMathTest.Tromino
