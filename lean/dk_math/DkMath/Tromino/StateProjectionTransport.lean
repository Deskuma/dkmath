/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RepairChamber
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

#print "file: DkMath.Tromino.StateProjectionTransport"

namespace DkMath.Tromino

/-! # Rooted chamber transport and shared coordinates

This module formalizes the abstract situation in which a child state space is
projected injectively into a parent state space. The parent relation is used
only inside an admissible chamber. A `RootedChamberTransport` supplies the two
directions needed for exactness: child paths map to restricted parent paths,
and every restricted parent edge out of a projected child state lifts back to
a child edge.

The result is an equality of rooted sectors, not a claim about all parent
states. The final definitions record the separate, graph-independent idea of
sharing mutable coordinates between two coloring types. -/

/-! ## Generic rooted chamber transport -/

/-- A rooted transport between a child relation and a parent relation
restricted to an admissible chamber.

The projection is deliberately a function between arbitrary types; no graph
or coloring structure is built into this kernel. `map_step` gives the forward
edge map and `lift_step` gives the converse local lifting property. Together
with injectivity and root alignment they determine the exact rooted sector.
-/
structure RootedChamberTransport
    (Child Parent : Type*)
    (childStep : Child → Child → Prop)
    (parentStep : Parent → Parent → Prop)
    (parentAdmissible : Parent → Prop)
    (project : Child → Parent)
    (childRoot : Child) (parentRoot : Parent) : Prop where
  project_injective : Function.Injective project
  root_project : project childRoot = parentRoot
  parent_root_admissible : parentAdmissible parentRoot
  map_step : ∀ {c d}, childStep c d →
    Restricted parentStep parentAdmissible (project c) (project d)
  lift_step : ∀ {c p},
    Restricted parentStep parentAdmissible (project c) p →
      ∃ d, childStep c d ∧ project d = p

namespace RootedChamberTransport

variable {Child Parent : Type*}
variable {childStep : Child → Child → Prop}
variable {parentStep : Parent → Parent → Prop}
variable {parentAdmissible : Parent → Prop}
variable {project : Child → Parent}
variable {childRoot : Child} {parentRoot : Parent}

/-- A child exact-length path maps to a restricted parent path. -/
theorem map_steps
    (T : RootedChamberTransport Child Parent childStep parentStep
      parentAdmissible project childRoot parentRoot)
    {n : Nat} {c d : Child} :
    Steps childStep n c d →
      Steps (Restricted parentStep parentAdmissible) n (project c) (project d) := by
  intro hpath
  induction hpath with
  | zero =>
      exact Steps.zero _
  | prepend hstep hrest ih =>
      exact Steps.prepend (T.map_step hstep) ih

/-- A restricted parent exact-length path can be lifted from a child point. -/
theorem lift_steps
    (T : RootedChamberTransport Child Parent childStep parentStep
      parentAdmissible project childRoot parentRoot)
    {n : Nat} {c : Child} {p₀ p : Parent}
    (hproject : project c = p₀)
    (hpath : Steps (Restricted parentStep parentAdmissible) n p₀ p) :
    ∃ d, Steps childStep n c d ∧ project d = p := by
  induction hpath generalizing c with
  | zero =>
      exact ⟨c, Steps.zero _, hproject⟩
  | @prepend n x y z hstep hrest ih =>
      have hstep' : Restricted parentStep parentAdmissible (project c) y := by
        rw [hproject]
        exact hstep
      rcases T.lift_step hstep' with ⟨c₁, hc₁, hproject₁⟩
      rcases ih hproject₁ with ⟨d, hpath', hproject'⟩
      exact ⟨d, Steps.prepend hc₁ hpath', hproject'⟩

/-- Reachability in the child relation is exactly membership in the projected
parent chamber.

The parent chamber includes root admissibility by definition, so the theorem
does not silently identify a zero-step path with an admissible state.
-/
theorem reachable_iff_admissibleChamber
    (T : RootedChamberTransport Child Parent childStep parentStep
      parentAdmissible project childRoot parentRoot)
    {c : Child} :
    Reachable childStep childRoot c ↔
      AdmissibleChamber parentStep parentAdmissible parentRoot (project c) := by
  constructor
  · rintro ⟨n, hpath⟩
    refine ⟨T.parent_root_admissible, ⟨n, ?_⟩⟩
    simpa only [T.root_project] using T.map_steps hpath
  · intro hchamber
    rcases hchamber.2 with ⟨n, hpath⟩
    have hpath' : Steps (Restricted parentStep parentAdmissible) n
        (project childRoot) (project c) := by
      simpa only [T.root_project] using hpath
    rcases T.lift_steps rfl hpath' with ⟨d, hchild, hproject⟩
    have hdc : d = c := T.project_injective hproject
    subst d
    exact ⟨n, hchild⟩

/-- The parent chamber is exactly the image of child reachability. -/
theorem admissibleChamber_iff_exists_reachable_project_eq
    (T : RootedChamberTransport Child Parent childStep parentStep
      parentAdmissible project childRoot parentRoot)
    {p : Parent} :
    AdmissibleChamber parentStep parentAdmissible parentRoot p ↔
      ∃ c, Reachable childStep childRoot c ∧ project c = p := by
  constructor
  · intro hchamber
    rcases hchamber.2 with ⟨n, hpath⟩
    have hpath' : Steps (Restricted parentStep parentAdmissible) n
        (project childRoot) p := by
      simpa only [T.root_project] using hpath
    rcases T.lift_steps rfl hpath' with ⟨c, hchild, hproject⟩
    exact ⟨c, ⟨n, hchild⟩, hproject⟩
  · rintro ⟨c, hchild, rfl⟩
    exact T.reachable_iff_admissibleChamber.mp hchild

/-- The projection is edge-exact, once the transport packet supplies both map
and lift data. -/
theorem childStep_iff_restricted_projected
    (T : RootedChamberTransport Child Parent childStep parentStep
      parentAdmissible project childRoot parentRoot)
    {c d : Child} :
    childStep c d ↔
      Restricted parentStep parentAdmissible (project c) (project d) := by
  constructor
  · exact T.map_step
  · intro hstep
    rcases T.lift_step hstep with ⟨d', hchild, hproject⟩
    have hdd' : d' = d := T.project_injective hproject
    subst d'
    exact hchild

end RootedChamberTransport

/-! ## Shared mutable coordinates for Tromino colorings -/

/-- The coordinates on a mutable carrier, independent of any graph topology.

Only vertices satisfying `mutable` receive values. This is the common carrier
used when parent and child graphs have different topologies but the same
mutable vertex set.
-/
def MutableCoordinates {V : Type*} (mutable : V → Prop) :=
  {v : V // mutable v} → TrominoState

/-- Restriction of a graph coloring to mutable coordinates. -/
def mutableColorProjection {V : Type*} (G : SimpleGraph V)
    (mutable : V → Prop) :
    G.Coloring TrominoState → MutableCoordinates mutable :=
  fun coloring v => coloring v.1

/-- Agreement outside a mutable set, with a graph-independent ambient coloring.

This predicate is the fixed-context hypothesis used to recover a total
coloring from its mutable projection.
-/
def AgreesOutside {V : Type*} (mutable : V → Prop)
    (base c : V → TrominoState) : Prop :=
  ∀ v, ¬ mutable v → c v = base v

theorem mutableColorProjection_injective_of_agreesOutside
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    {base : V → TrominoState}
    {source target : G.Coloring TrominoState}
    (hsource : AgreesOutside mutable base source)
    (htarget : AgreesOutside mutable base target)
    (hprojection : mutableColorProjection G mutable source =
      mutableColorProjection G mutable target) :
    source = target := by
  apply DFunLike.ext source target
  intro v
  by_cases hv : mutable v
  · simpa [mutableColorProjection] using
      congrFun hprojection (⟨v, hv⟩ : {v : V // mutable v})
  · exact (hsource v hv).trans (htarget v hv).symm

/-- Equality of mutable coordinates for colorings living on different graphs
with the same vertex type.

The two coloring types may come from different simple graphs; only their
vertex type and the selected mutable coordinates are shared.
-/
def SameMutableProjection {V : Type*} {GParent GChild : SimpleGraph V}
    (mutable : V → Prop)
    (parentColoring : GParent.Coloring TrominoState)
    (childColoring : GChild.Coloring TrominoState) : Prop :=
  mutableColorProjection GParent mutable parentColoring =
    mutableColorProjection GChild mutable childColoring

theorem sameMutableProjection_iff
    {V : Type*} {GParent GChild : SimpleGraph V}
    {mutable : V → Prop}
    {parentColoring : GParent.Coloring TrominoState}
    {childColoring : GChild.Coloring TrominoState} :
    SameMutableProjection mutable parentColoring childColoring ↔
      ∀ v, mutable v → parentColoring v = childColoring v := by
  constructor
  · intro h v hv
    simpa [SameMutableProjection, mutableColorProjection] using
      congrFun h (⟨v, hv⟩ : {v : V // mutable v})
  · intro h
    funext v
    exact h v.1 v.2

end DkMath.Tromino
