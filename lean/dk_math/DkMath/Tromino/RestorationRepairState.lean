/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.StateProjectionTransport

#print "file: DkMath.Tromino.RestorationRepairState"

namespace DkMath.Tromino

/-! # Partial restoration states

This module separates the finite mutable coordinates from the partially
colored graph on which they are interpreted. A `RestorationContext` remembers
which vertices are colored, which remain uncolored, and which values are
fixed outside the mutable set. A mutable state is realized as a total ambient
assignment only for the purpose of checking local conditions.

The admissibility predicate is intentionally local: properness is required on
colored--colored edges, while every remaining vertex must have a missing
color. The final bridge identifies an admissible one-coordinate move with a
singleton Kempe move on the induced colored graph. -/

/-! ## Partial restoration contexts -/

/-- Fixed data for a partial restoration state.

The `base` assignment is only the fixed assignment outside the mutable set;
it is not required to be a proper total coloring. -/
structure RestorationContext {V : Type*} (G : SimpleGraph V)
    (mutable : V → Prop) where
  colored : V → Prop
  remaining : V → Prop
  base : V → TrominoState
  mutable_colored : ∀ v, mutable v → colored v
  remaining_uncolored : ∀ v, remaining v → ¬ colored v

/-- The vertices already colored by a restoration context. -/
def ColoredVertex {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable) :=
  {v : V // context.colored v}

/-- The graph induced by the already-colored vertices.

This is the graph on which a partial assignment becomes an ordinary proper
coloring; uncolored vertices are not silently assigned constraints.
-/
def ColoredGraph {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable) :
    SimpleGraph (ColoredVertex context) :=
  G.induce {v | context.colored v}

/-! ## Realizing mutable coordinates -/

/-- Restore a full ambient assignment from fixed outside data and mutable
coordinates.

Mutable coordinates take precedence on mutable vertices, and `base` supplies
the fixed context elsewhere. The definition does not assert that the result
is proper; properness is a separate predicate below.
-/
noncomputable def realize {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (state : MutableCoordinates mutable) (v : V) : TrominoState :=
  by
    classical
    exact if h : mutable v then state ⟨v, h⟩ else context.base v

@[simp] theorem realize_mutable
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (state : MutableCoordinates mutable) {v : V} (hv : mutable v) :
    realize context state v = state ⟨v, hv⟩ := by
  simp [realize, hv]

@[simp] theorem realize_outside
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (state : MutableCoordinates mutable) {v : V} (hv : ¬ mutable v) :
    realize context state v = context.base v := by
  simp [realize, hv]

theorem realize_injective
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    {source target : MutableCoordinates mutable}
    (h : realize context source = realize context target) :
    source = target := by
  funext v
  have hv := congrFun h v.1
  rw [realize_mutable context source v.2,
    realize_mutable context target v.2] at hv
  exact hv

/-! ## Properness and Missing-Color validity -/

/-- Properness restricted to edges whose two endpoints are colored.

Edges incident to an uncolored endpoint are intentionally outside this
predicate.
-/
def ProperOnColored {V : Type*} (G : SimpleGraph V) (colored : V → Prop)
    (assignment : V → TrominoState) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → colored u → colored v → assignment u ≠ assignment v

/-- Context/state form of partial properness. -/
def RestorationContext.Proper
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (state : MutableCoordinates mutable) : Prop :=
  ProperOnColored G context.colored (realize context state)

/-- A color missing from all colored neighbors of `w`. -/
def MissingAt {V : Type*} (G : SimpleGraph V) (colored : V → Prop)
    (assignment : V → TrominoState) (w : V) : Prop :=
  ∃ missing : TrominoState,
    ∀ u, G.Adj u w → colored u → assignment u ≠ missing

/-- Every remaining vertex has at least one color absent from its colored
neighbors.

This is the local completion condition used by restoration arguments; it is
not a global extension or coloring theorem.
-/
def MissingValid {V : Type*} (G : SimpleGraph V) (colored remaining : V → Prop)
    (assignment : V → TrominoState) : Prop :=
  ∀ w, remaining w → MissingAt G colored assignment w

def RestorationContext.MissingValid
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (state : MutableCoordinates mutable) : Prop :=
  DkMath.Tromino.MissingValid G context.colored context.remaining
    (realize context state)

/-- The static restoration admissibility predicate.

An admissible mutable state is both proper on the already-colored graph and
Missing-valid at every remaining vertex.
-/
def RestorationAdmissible
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (state : MutableCoordinates mutable) : Prop :=
  context.Proper state ∧ context.MissingValid state

/-! ## One-coordinate restoration transitions -/

/-- Two coordinate states differ at exactly one mutable coordinate.

The predicate is symmetric, and it is independent of graph adjacency. Graph
constraints enter only through `AdmissibleRestorationStep`.
-/
def CoordinateOnePointStep {V : Type*} (mutable : V → Prop)
    (source target : MutableCoordinates mutable) : Prop :=
  ∃ v, source v ≠ target v ∧ ∀ u, u ≠ v → target u = source u

theorem coordinateOnePointStep_symmetric
    {V : Type*} {mutable : V → Prop} :
    Std.Symm (CoordinateOnePointStep mutable) := by
  constructor
  intro source target h
  rcases h with ⟨v, hne, haway⟩
  exact ⟨v, hne.symm, fun u hu => (haway u hu).symm⟩

/-- Admissible one-coordinate restoration transitions.

Both endpoints must satisfy `RestorationAdmissible`, and the underlying move
must change exactly one mutable coordinate.
-/
def AdmissibleRestorationStep
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable) :=
  Restricted (CoordinateOnePointStep mutable) (RestorationAdmissible context)

theorem admissibleRestorationStep_symmetric
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable) :
    Std.Symm (AdmissibleRestorationStep context) := by
  exact restricted_symmetric coordinateOnePointStep_symmetric

/-! ## The induced total-coloring bridge -/

/-- Mutable vertices viewed inside the colored induced graph. -/
def liftedMutable
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable) : ColoredVertex context → Prop :=
  fun v => mutable v.1

def mutableToColored
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (v : {x : V // mutable x}) : ColoredVertex context :=
  ⟨v.1, context.mutable_colored v.1 v.2⟩

@[simp] theorem mutableToColored_val
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (v : {x : V // mutable x}) :
    (mutableToColored context v).1 = v.1 :=
  rfl

@[simp] theorem liftedMutable_mutableToColored
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (v : {x : V // mutable x}) :
    liftedMutable context (mutableToColored context v) :=
  v.2

/-- A proper partial assignment becomes a proper coloring of the induced
colored graph.

The proof is a change of carrier: the values are still supplied by `realize`,
but the graph now contains only colored vertices.
-/
noncomputable def partialColoring
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (state : MutableCoordinates mutable)
    (hproper : context.Proper state) :
    (ColoredGraph context).Coloring TrominoState :=
  SimpleGraph.Coloring.mk
    (fun v => realize context state v.1)
    (by
      intro v w hAdj
      exact hproper hAdj v.2 w.2)

@[simp] theorem partialColoring_apply
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    (state : MutableCoordinates mutable)
    (hproper : context.Proper state) (v : ColoredVertex context) :
    partialColoring context state hproper v = realize context state v.1 :=
  rfl

theorem coordinateOnePointStep_onePointRecolor
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    {source target : MutableCoordinates mutable}
    (hstep : CoordinateOnePointStep mutable source target)
    (hsource : context.Proper source) (htarget : context.Proper target) :
    OnePointRecolor (ColoredGraph context) (liftedMutable context)
      (partialColoring context source hsource)
      (partialColoring context target htarget) := by
  rcases hstep with ⟨v, hne, haway⟩
  refine ⟨mutableToColored context v, liftedMutable_mutableToColored context v,
    ?_, ?_⟩
  · change realize context source v.1 ≠ realize context target v.1
    intro hcolor
    apply hne
    rw [realize_mutable context source v.2,
      realize_mutable context target v.2] at hcolor
    exact hcolor
  · intro u hu
    by_cases hmutable : mutable u.1
    · let uv : {x : V // mutable x} := ⟨u.1, hmutable⟩
      have huv : uv ≠ v := by
        intro huv
        apply hu
        apply Subtype.ext
        simpa [uv, mutableToColored] using congrArg Subtype.val huv
      have hcolor := haway uv huv
      simpa [partialColoring_apply, realize_mutable, uv, hmutable] using hcolor
    · simp [partialColoring_apply, realize_outside, hmutable]

theorem admissibleRestorationStep_onePointRecolor
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    {source target : MutableCoordinates mutable}
    (hstep : AdmissibleRestorationStep context source target) :
    OnePointRecolor (ColoredGraph context) (liftedMutable context)
      (partialColoring context source hstep.1.1)
      (partialColoring context target hstep.2.1.1) := by
  exact coordinateOnePointStep_onePointRecolor context hstep.2.2
    hstep.1.1 hstep.2.1.1

theorem admissibleRestorationStep_singletonKempeMove
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    (context : RestorationContext G mutable)
    {source target : MutableCoordinates mutable}
    (hstep : AdmissibleRestorationStep context source target) :
    SingletonKempeMove (ColoredGraph context) (liftedMutable context)
      (partialColoring context source hstep.1.1)
      (partialColoring context target hstep.2.1.1) :=
  onePointRecolor_singletonKempeMove
    (admissibleRestorationStep_onePointRecolor context hstep)

/-! ## Shared parent/child admissibility -/

/-- Shared admissibility for a parent/child pair of contexts. -/
def TransportAdmissible
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    (parentContext : RestorationContext GParent mutable)
    (childContext : RestorationContext GChild mutable)
    (state : MutableCoordinates mutable) : Prop :=
    RestorationAdmissible parentContext state ∧
    RestorationAdmissible childContext state

/-! Shared admissibility is the intersection of the parent and child local
conditions. It is the precise state predicate needed when a topology change
is compared on a common mutable carrier. -/
def TransportAdmissibleRestorationStep
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    (parentContext : RestorationContext GParent mutable)
    (childContext : RestorationContext GChild mutable) :=
  Restricted (CoordinateOnePointStep mutable)
    (TransportAdmissible parentContext childContext)

theorem transportAdmissibleRestorationStep_iff
    {V : Type*} {GParent GChild : SimpleGraph V} {mutable : V → Prop}
    (parentContext : RestorationContext GParent mutable)
    (childContext : RestorationContext GChild mutable)
    {source target : MutableCoordinates mutable} :
    TransportAdmissibleRestorationStep parentContext childContext source target ↔
      AdmissibleRestorationStep parentContext source target ∧
      RestorationAdmissible childContext source ∧
      RestorationAdmissible childContext target := by
  constructor
  · rintro ⟨⟨hps, hcs⟩, ⟨hpt, hct⟩, hstep⟩
    exact ⟨⟨hps, hpt, hstep⟩, hcs, hct⟩
  · rintro ⟨⟨hps, hpt, hstep⟩, hcs, hct⟩
    exact ⟨⟨hps, hcs⟩, ⟨hpt, hct⟩, hstep⟩

end DkMath.Tromino
