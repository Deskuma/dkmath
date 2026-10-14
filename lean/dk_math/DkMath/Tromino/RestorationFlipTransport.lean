/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RestorationRepairState
import DkMath.Tromino.StateProjectionTransport

#print "file: DkMath.Tromino.RestorationFlipTransport"

namespace DkMath.Tromino

/-! # Local flip transport for partial restorations

This module isolates the mathematics of a single undirected edge replacement.
`SingleEdgeReplacement` says that the child graph is obtained by removing one
parent edge and adding one new edge; all other adjacency facts are recovered
from its equivalence field.

The topology delta alone is deliberately not treated as a sector theorem.
After properness and Missing-Color locality are transported, an explicit
`ExactRestorationSectorCertificate` is still required to show that every state
reachable in the child chamber is admissible for the parent. Only then can
the shared-coordinate sector be packaged as a generic
`RootedChamberTransport`. -/

/-! ## The local graph delta -/

/-- Equality of two ordered pairs as the same undirected edge.

The disjunction makes the predicate independent of the orientation used to
write an adjacency pair.
-/
def SameUndirectedEdge {V : Type*} (x y u v : V) : Prop :=
  (x = u ∧ y = v) ∨ (x = v ∧ y = u)

theorem sameUndirectedEdge_symm {V : Type*} {x y u v : V} :
    SameUndirectedEdge x y u v → SameUndirectedEdge y x u v := by
  intro h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem sameUndirectedEdge_swap {V : Type*} {x y u v : V} :
    SameUndirectedEdge x y u v ↔ SameUndirectedEdge x y v u := by
  constructor <;> intro h
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩

theorem sameUndirectedEdge_overlap {V : Type*}
    {x y u v a b : V}
    (hxyuv : SameUndirectedEdge x y u v)
    (hxyab : SameUndirectedEdge x y a b) :
    SameUndirectedEdge a b u v := by
  rcases hxyuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hxyab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [SameUndirectedEdge]

/-- A local graph delta replacing one old edge by one new edge.

The `adj_iff` field is the complete topology specification: an edge survives
exactly when it was a parent edge different from the removed edge, or it is
the newly inserted edge. `new_nonedge` guarantees that the replacement is
genuinely different from the removed edge.
-/
structure SingleEdgeReplacement {V : Type*}
    (GParent GChild : SimpleGraph V) (u v a b : V) : Prop where
  old_edge : GParent.Adj u v
  new_nonedge : ¬ GParent.Adj a b
  adj_iff : ∀ x y,
    GChild.Adj x y ↔
      (GParent.Adj x y ∧ ¬ SameUndirectedEdge x y u v) ∨
        SameUndirectedEdge x y a b

theorem SingleEdgeReplacement.old_new_disjoint
    {V : Type*} {GParent GChild : SimpleGraph V} {u v a b : V}
    (R : SingleEdgeReplacement GParent GChild u v a b) :
    ¬ SameUndirectedEdge a b u v := by
  intro h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact R.new_nonedge R.old_edge
  · exact R.new_nonedge (GParent.symm.symm _ _ R.old_edge)

theorem SingleEdgeReplacement.old_edge_absent
    {V : Type*} {GParent GChild : SimpleGraph V} {u v a b : V}
    (R : SingleEdgeReplacement GParent GChild u v a b) :
    ¬ GChild.Adj u v := by
  intro hchild
  rcases (R.adj_iff u v).mp hchild with ⟨_, hold⟩ | hnew
  · exact hold (Or.inl ⟨rfl, rfl⟩)
  · rcases hnew with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact R.new_nonedge R.old_edge
    · exact R.new_nonedge (GParent.symm.symm _ _ R.old_edge)

theorem SingleEdgeReplacement.new_edge_present
    {V : Type*} {GParent GChild : SimpleGraph V} {u v a b : V}
    (R : SingleEdgeReplacement GParent GChild u v a b) :
    GChild.Adj a b := by
  exact (R.adj_iff a b).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem SingleEdgeReplacement.adj_unchanged
    {V : Type*} {GParent GChild : SimpleGraph V} {u v a b x y : V}
    (R : SingleEdgeReplacement GParent GChild u v a b)
    (hold : ¬ SameUndirectedEdge x y u v)
    (hnew : ¬ SameUndirectedEdge x y a b) :
    GChild.Adj x y ↔ GParent.Adj x y := by
  constructor
  · intro h
    rcases (R.adj_iff x y).mp h with ⟨hparent, _⟩ | hedge
    · exact hparent
    · exact (hnew hedge).elim
  · intro h
    exact (R.adj_iff x y).mpr (Or.inl ⟨h, hold⟩)

theorem SingleEdgeReplacement.adj_at_unchanged
    {V : Type*} {GParent GChild : SimpleGraph V} {u v a b w x : V}
    (R : SingleEdgeReplacement GParent GChild u v a b)
    (hwu : w ≠ u) (hwv : w ≠ v) (hwa : w ≠ a) (hwb : w ≠ b) :
    GChild.Adj x w ↔ GParent.Adj x w := by
  apply R.adj_unchanged
  · intro h
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hwv rfl
    · exact hwu rfl
  · intro h
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hwb rfl
    · exact hwa rfl

theorem missingAt_flip_locality
    {V : Type*} {GParent GChild : SimpleGraph V} {u v a b w : V}
    (R : SingleEdgeReplacement GParent GChild u v a b)
    {colored : V → Prop} {assignment : V → TrominoState}
    (hwu : w ≠ u) (hwv : w ≠ v) (hwa : w ≠ a) (hwb : w ≠ b) :
    MissingAt GParent colored assignment w ↔
      MissingAt GChild colored assignment w := by
  constructor
  · rintro ⟨missing, hmissing⟩
    refine ⟨missing, ?_⟩
    intro x hx hcx
    exact hmissing x ((R.adj_at_unchanged hwu hwv hwa hwb).mp hx) hcx
  · rintro ⟨missing, hmissing⟩
    refine ⟨missing, ?_⟩
    intro x hx hcx
    exact hmissing x ((R.adj_at_unchanged hwu hwv hwa hwb).mpr hx) hcx

/-! Properness changes only at the new and removed edge. Consequently, a
proper parent assignment crosses to the child when the new edge has distinct
endpoint values, and a proper child assignment crosses back when the removed
edge has distinct endpoint values. -/
/-! ## Properness transport -/

theorem properOnColored_parent_to_child
    {V : Type*} {GParent GChild : SimpleGraph V} {u v a b : V}
    (R : SingleEdgeReplacement GParent GChild u v a b)
    {colored : V → Prop} {assignment : V → TrominoState}
    (hparent : ProperOnColored GParent colored assignment)
    (hnew : colored a → colored b → assignment a ≠ assignment b) :
    ProperOnColored GChild colored assignment := by
  intro x y hxy hcx hcy
  rcases (R.adj_iff x y).mp hxy with ⟨hparentxy, _⟩ | hnewxy
  · exact hparent hparentxy hcx hcy
  · rcases hnewxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hnew hcx hcy
    · exact (hnew hcy hcx).symm

theorem properOnColored_child_to_parent
    {V : Type*} {GParent GChild : SimpleGraph V} {u v a b : V}
    (R : SingleEdgeReplacement GParent GChild u v a b)
    {colored : V → Prop} {assignment : V → TrominoState}
    (hchild : ProperOnColored GChild colored assignment)
    (hold : colored u → colored v → assignment u ≠ assignment v) :
    ProperOnColored GParent colored assignment := by
  intro x y hxy hcx hcy
  by_cases holdxy : SameUndirectedEdge x y u v
  · rcases holdxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hold hcx hcy
    · exact (hold hcy hcx).symm
  · exact hchild ((R.adj_iff x y).mpr (Or.inl ⟨hxy, holdxy⟩)) hcx hcy

/-! ## Compatible restoration contexts -/

structure RestorationFlipContext {V : Type*}
    {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    (u v a b : V)
    (parentContext : RestorationContext GParent mutable)
    (childContext : RestorationContext GChild mutable) : Prop where
  replacement : SingleEdgeReplacement GParent GChild u v a b
  same_colored : parentContext.colored = childContext.colored
  same_remaining : parentContext.remaining = childContext.remaining

/-! A compatible flip context shares the colored and remaining predicates;
the ambient graphs may still differ by the local edge replacement. -/
theorem restorationContext_proper_parent_to_child
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {u v a b : V}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    (F : RestorationFlipContext u v a b parentContext childContext)
    {state : MutableCoordinates mutable}
    (hrealize : realize parentContext state = realize childContext state)
    (hparent : parentContext.Proper state)
    (hnew : childContext.colored a → childContext.colored b →
      realize childContext state a ≠ realize childContext state b) :
    childContext.Proper state := by
  have hparent' : ProperOnColored GParent parentContext.colored
      (realize parentContext state) := hparent
  have hnew' : parentContext.colored a → parentContext.colored b →
      realize parentContext state a ≠ realize parentContext state b := by
    intro hca hcb hab
    apply hnew
    · simpa [F.same_colored] using hca
    · simpa [F.same_colored] using hcb
    · simpa [hrealize] using hab
  have hchild' := properOnColored_parent_to_child F.replacement hparent' hnew'
  change ProperOnColored GChild childContext.colored (realize childContext state)
  simpa [F.same_colored, hrealize] using hchild'

theorem restorationContext_proper_child_to_parent
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {u v a b : V}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    (F : RestorationFlipContext u v a b parentContext childContext)
    {state : MutableCoordinates mutable}
    (hrealize : realize parentContext state = realize childContext state)
    (hchild : childContext.Proper state)
    (hold : parentContext.colored u → parentContext.colored v →
      realize parentContext state u ≠ realize parentContext state v) :
    parentContext.Proper state := by
  have hchild' : ProperOnColored GChild childContext.colored
      (realize childContext state) := hchild
  have hold' : childContext.colored u → childContext.colored v →
      realize childContext state u ≠ realize childContext state v := by
    intro hcu hcv hab
    apply hold
    · simpa [F.same_colored] using hcu
    · simpa [F.same_colored] using hcv
    · simpa [hrealize] using hab
  have hparent' := properOnColored_child_to_parent F.replacement hchild' hold'
  change ProperOnColored GParent parentContext.colored (realize parentContext state)
  simpa [F.same_colored, hrealize] using hparent'

/-! ## Exact rooted-sector certificates -/

structure ExactRestorationSectorCertificate {V : Type*}
    {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {u v a b : V}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    (flip : RestorationFlipContext u v a b parentContext childContext)
    (root : MutableCoordinates mutable) : Prop where
  child_root_admissible : RestorationAdmissible childContext root
  parent_on_child_chamber : ∀ {state},
    Reachable (AdmissibleRestorationStep childContext) root state →
      RestorationAdmissible parentContext state

/-! The certificate is the missing global ingredient after local topology
transport: it says that the entire rooted child chamber lies in the parent
admissible state space. -/
theorem exactRestorationSector_edge_iff
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    {source target : MutableCoordinates mutable} :
    TransportAdmissibleRestorationStep parentContext childContext source target ↔
      AdmissibleRestorationStep parentContext source target ∧
        RestorationAdmissible childContext source ∧
        RestorationAdmissible childContext target :=
  transportAdmissibleRestorationStep_iff parentContext childContext

theorem childAdmissibleRestorationStep_iff_transport
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    {source target : MutableCoordinates mutable}
    (hsource : RestorationAdmissible parentContext source)
    (htarget : RestorationAdmissible parentContext target) :
    AdmissibleRestorationStep childContext source target ↔
      TransportAdmissibleRestorationStep parentContext childContext source target := by
  constructor
  · intro h
    exact ⟨⟨hsource, h.1⟩, ⟨htarget, h.2.1⟩, h.2.2⟩
  · intro h
    exact ⟨h.1.2, h.2.1.2, h.2.2⟩

/-! ## Exact sector on the shared coordinate carrier -/

/-! Starting from a child-reachable state, every child path can be read as a
path satisfying both parent and child admissibility. In the reverse direction
the shared relation forgets only parent-side evidence, so a transport path is
already a child path. -/
theorem steps_transport_of_child_reachable
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {u v a b : V}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    (flip : RestorationFlipContext u v a b parentContext childContext)
    {root x : MutableCoordinates mutable}
    (certificate : ExactRestorationSectorCertificate flip root)
    {n : Nat} {y : MutableCoordinates mutable}
    (hreach : Reachable (AdmissibleRestorationStep childContext) root x)
    (hsteps : Steps (AdmissibleRestorationStep childContext) n x y) :
    Steps (TransportAdmissibleRestorationStep parentContext childContext) n x y := by
  revert hreach
  induction hsteps with
  | zero =>
      intro _
      exact Steps.zero _
  | @prepend n x y z hxy hrest ih =>
      intro hreach
      have hyreach : Reachable (AdmissibleRestorationStep childContext) root y :=
        reachable_trans (AdmissibleRestorationStep childContext) hreach
          ⟨1, Steps.prepend hxy (Steps.zero _)⟩
      have hxparent := certificate.parent_on_child_chamber hreach
      have hyparent := certificate.parent_on_child_chamber hyreach
      have hxy' : TransportAdmissibleRestorationStep
          parentContext childContext x y :=
        ⟨⟨hxparent, hxy.1⟩, ⟨hyparent, hxy.2.1⟩, hxy.2.2⟩
      exact Steps.prepend hxy' (ih hyreach)

theorem steps_child_of_transport
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    {n : Nat} {x y : MutableCoordinates mutable}
    (hsteps : Steps (TransportAdmissibleRestorationStep parentContext childContext)
      n x y) :
    Steps (AdmissibleRestorationStep childContext) n x y := by
  induction hsteps with
  | zero => exact Steps.zero _
  | @prepend n x y z hxy hrest ih =>
      have hxy' : AdmissibleRestorationStep childContext x y :=
        ⟨hxy.1.2, hxy.2.1.2, hxy.2.2⟩
      exact Steps.prepend hxy' ih

theorem exactRestorationSector_iff
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {u v a b : V}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    (flip : RestorationFlipContext u v a b parentContext childContext)
    {root state : MutableCoordinates mutable}
    (certificate : ExactRestorationSectorCertificate flip root) :
    Reachable (AdmissibleRestorationStep childContext) root state ↔
      AdmissibleChamber (CoordinateOnePointStep mutable)
        (TransportAdmissible parentContext childContext) root state := by
  constructor
  · rintro ⟨n, hpath⟩
    have hrootParent := certificate.parent_on_child_chamber
      (reachable_refl (AdmissibleRestorationStep childContext) root)
    have hrootTransport :
        TransportAdmissible parentContext childContext root :=
      ⟨hrootParent, certificate.child_root_admissible⟩
    refine ⟨hrootTransport, ⟨n, ?_⟩⟩
    exact steps_transport_of_child_reachable flip certificate
      (reachable_refl _ root) hpath
  · rintro ⟨hroot, ⟨n, hpath⟩⟩
    exact ⟨n, steps_child_of_transport hpath⟩

/-! ## Rooted child chamber and generic transport packet -/

def RootedChildChamber {V : Type*}
    {GChild : SimpleGraph V} {mutable : V → Prop}
    (childContext : RestorationContext GChild mutable)
    (root : MutableCoordinates mutable) :=
  {state // Reachable (AdmissibleRestorationStep childContext) root state}

/-! The subtype remembers both a child state and its proof of membership in
the rooted child chamber. This makes the projection to the shared mutable
carrier injective by construction. -/
def RootedChildChamberStep {V : Type*}
    {GChild : SimpleGraph V} {mutable : V → Prop}
    (childContext : RestorationContext GChild mutable)
    {root : MutableCoordinates mutable}
    (source target : RootedChildChamber childContext root) : Prop :=
  AdmissibleRestorationStep childContext source.1 target.1

theorem exactRestorationSectorTransport
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {u v a b : V}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    (flip : RestorationFlipContext u v a b parentContext childContext)
    {root : MutableCoordinates mutable}
    (certificate : ExactRestorationSectorCertificate flip root) :
    RootedChamberTransport
      (RootedChildChamber childContext root)
      (MutableCoordinates mutable)
      (RootedChildChamberStep childContext)
      (CoordinateOnePointStep mutable)
      (TransportAdmissible parentContext childContext)
      (fun state => state.1)
      ⟨root, reachable_refl _ root⟩ root where
  project_injective := by
    intro c d h
    exact Subtype.ext h
  root_project := rfl
  parent_root_admissible := by
    exact ⟨certificate.parent_on_child_chamber (reachable_refl _ root),
      certificate.child_root_admissible⟩
  map_step := by
    intro c d h
    exact ⟨⟨certificate.parent_on_child_chamber c.2, h.1⟩,
      ⟨certificate.parent_on_child_chamber d.2, h.2.1⟩, h.2.2⟩
  lift_step := by
    intro c p h
    have hchild : AdmissibleRestorationStep childContext c.1 p :=
      ⟨h.1.2, h.2.1.2, h.2.2⟩
    let d : RootedChildChamber childContext root :=
      ⟨p, reachable_trans (AdmissibleRestorationStep childContext)
        c.2 ⟨1, Steps.prepend hchild (Steps.zero _)⟩⟩
    exact ⟨d, hchild, rfl⟩

theorem exactRestorationSectorTransport_chamber_iff
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    {u v a b : V}
    {parentContext : RestorationContext GParent mutable}
    {childContext : RestorationContext GChild mutable}
    (flip : RestorationFlipContext u v a b parentContext childContext)
    {root : MutableCoordinates mutable}
    (certificate : ExactRestorationSectorCertificate flip root)
    (state : RootedChildChamber childContext root) :
    Reachable (RootedChildChamberStep childContext)
        ⟨root, reachable_refl _ root⟩ state ↔
      AdmissibleChamber (CoordinateOnePointStep mutable)
        (TransportAdmissible parentContext childContext) root state.1 :=
  RootedChamberTransport.reachable_iff_admissibleChamber
    (exactRestorationSectorTransport flip certificate)

/-! A single-edge replacement is only a topology delta.  It does not supply
the rooted exact-sector certificate above. -/

end DkMath.Tromino
