/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.StateSector
import DkMath.Tromino.Exchange
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

#print "file: DkMath.Tromino.KempeRepair"

namespace DkMath.Tromino

variable {V : Type*}

/-! ## One-point recoloring -/

/-- Two proper colorings differ at one mutable vertex and agree elsewhere. -/
def OnePointRecolor (G : SimpleGraph V) (mutable : V → Prop)
    (source target : G.Coloring TrominoState) : Prop :=
  ∃ v, mutable v ∧ source v ≠ target v ∧
    ∀ u, u ≠ v → target u = source u

theorem onePointRecolor_witness
    {G : SimpleGraph V} {mutable : V → Prop}
    {source target : G.Coloring TrominoState}
    (h : OnePointRecolor G mutable source target) :
    ∃ v, mutable v ∧ source v ≠ target v ∧
      ∀ u, u ≠ v → target u = source u :=
  h

theorem onePointRecolor_symm
    {G : SimpleGraph V} {mutable : V → Prop}
    {source target : G.Coloring TrominoState}
    (h : OnePointRecolor G mutable source target) :
    OnePointRecolor G mutable target source := by
  rcases h with ⟨v, hmutable, hne, haway⟩
  exact ⟨v, hmutable, hne.symm, fun u hu => (haway u hu).symm⟩

/-! ## Two-color support and reachability -/

/-- Membership in the two-color support of a coloring. -/
def TwoColorSupport {G : SimpleGraph V} (c : G.Coloring TrominoState)
    (a b : TrominoState) (x : V) : Prop :=
  c x = a ∨ c x = b

/-- One graph edge inside the two-color support. -/
def TwoColorStep (G : SimpleGraph V) (c : G.Coloring TrominoState)
    (a b : TrominoState) (x y : V) : Prop :=
  G.Adj x y ∧ TwoColorSupport c a b x ∧ TwoColorSupport c a b y

/-- Exact-path reachability in a two-color support. -/
def KempeReachable (G : SimpleGraph V) (c : G.Coloring TrominoState)
    (a b : TrominoState) (root x : V) : Prop :=
  Reachable (TwoColorStep G c a b) root x

theorem not_twoColorStep_at_onePoint
    {G : SimpleGraph V}
    {source target : G.Coloring TrominoState}
    {v u : V}
    (haway : ∀ u, u ≠ v → target u = source u)
    (hstep : TwoColorStep G source (source v) (target v) v u) :
    False := by
  rcases hstep with ⟨hadj, _, hu⟩
  have huv : u ≠ v := (G.ne_of_adj hadj).symm
  rcases hu with hua | hub
  · exact source.valid hadj hua.symm
  · have htarget : target u = target v := (haway u huv).trans hub
    exact target.valid hadj htarget.symm

theorem kempeReachable_singleton_of_onePointRecolor
    {G : SimpleGraph V} {mutable : V → Prop}
    {source target : G.Coloring TrominoState}
    (h : OnePointRecolor G mutable source target) :
    ∃ v, mutable v ∧ source v ≠ target v ∧
      ∀ u, KempeReachable G source (source v) (target v) v u ↔ u = v := by
  classical
  rcases h with ⟨v, hmutable, hne, haway⟩
  refine ⟨v, hmutable, hne, ?_⟩
  intro u
  constructor
  · intro hreach
    rcases hreach with ⟨n, hpath⟩
    cases hpath with
    | zero =>
        rfl
    | @prepend n x y z hstep hrest =>
        exact (not_twoColorStep_at_onePoint haway hstep).elim
  · intro huv
    subst u
    exact reachable_refl (TwoColorStep G source (source v) (target v)) v

/-! ## The V4 exchange bridge -/

theorem onePointRecolor_exchange_bridge
    {G : SimpleGraph V} {mutable : V → Prop}
    {source target : G.Coloring TrominoState}
    (h : OnePointRecolor G mutable source target) :
    ∃ v, mutable v ∧ source v ≠ target v ∧
      ∃! delta, delta ≠ 0 ∧ exchange delta (source v) = target v := by
  rcases h with ⟨v, hmutable, hne, haway⟩
  exact ⟨v, hmutable, hne,
    existsUnique_nonzero_exchange_to hne⟩

/-! ## A packaged singleton Kempe move -/

/-- A one-point recolor together with its singleton Kempe and V4 witnesses. -/
def SingletonKempeMove (G : SimpleGraph V) (mutable : V → Prop)
    (source target : G.Coloring TrominoState) : Prop :=
  ∃ v, mutable v ∧ source v ≠ target v ∧
    (∀ u, u ≠ v → target u = source u) ∧
    (∀ u, KempeReachable G source (source v) (target v) v u ↔ u = v) ∧
    ∃! delta, delta ≠ 0 ∧ exchange delta (source v) = target v

theorem onePointRecolor_singletonKempeMove
    {G : SimpleGraph V} {mutable : V → Prop}
    {source target : G.Coloring TrominoState}
    (h : OnePointRecolor G mutable source target) :
    SingletonKempeMove G mutable source target := by
  rcases h with ⟨v, hmutable, hne, haway⟩
  refine ⟨v, hmutable, hne, haway, ?_, ?_⟩
  · intro u
    constructor
    · intro hreach
      rcases hreach with ⟨n, hpath⟩
      cases hpath with
      | zero =>
          rfl
      | @prepend n x y z hstep hrest =>
          exact (not_twoColorStep_at_onePoint haway hstep).elim
    · intro huv
      subst u
      exact reachable_refl (TwoColorStep G source (source v) (target v)) v
  · exact existsUnique_nonzero_exchange_to hne

theorem singletonKempeMove_onePointRecolor
    {G : SimpleGraph V} {mutable : V → Prop}
    {source target : G.Coloring TrominoState}
    (h : SingletonKempeMove G mutable source target) :
    OnePointRecolor G mutable source target := by
  rcases h with ⟨v, hmutable, hne, haway, _, _⟩
  exact ⟨v, hmutable, hne, haway⟩

theorem singletonKempeMove_symm
    {G : SimpleGraph V} {mutable : V → Prop}
    {source target : G.Coloring TrominoState}
    (h : SingletonKempeMove G mutable source target) :
    SingletonKempeMove G mutable target source := by
  rcases h with ⟨v, hmutable, hne, haway, _, _⟩
  have hawayReverse : ∀ u, u ≠ v → source u = target u := by
    intro u hu
    exact (haway u hu).symm
  have hcomponent :
      ∀ u, KempeReachable G target (target v) (source v) v u ↔ u = v := by
    intro u
    constructor
    · intro hreach
      rcases hreach with ⟨n, hpath⟩
      cases hpath with
      | zero =>
          rfl
      | @prepend n x y z hstep hrest =>
          exact (not_twoColorStep_at_onePoint hawayReverse hstep).elim
    · intro huv
      subst u
      exact reachable_refl (TwoColorStep G target (target v) (source v)) v
  refine ⟨v, hmutable, hne.symm, ?_, hcomponent, ?_⟩
  · intro u hu
    exact hawayReverse u hu
  · exact existsUnique_nonzero_exchange_to hne.symm

theorem singletonKempeMove_symmetric
    {G : SimpleGraph V} {mutable : V → Prop} :
    Std.Symm (SingletonKempeMove G mutable) := by
  constructor
  intro source target h
  exact singletonKempeMove_symm h

/-! ## Repair-height instantiation -/

abbrev SingletonKempeStep (G : SimpleGraph V) (mutable : V → Prop) :
    G.Coloring TrominoState → G.Coloring TrominoState → Prop :=
  SingletonKempeMove G mutable

theorem singletonKempeStep_symmetric
    (G : SimpleGraph V) (mutable : V → Prop) :
    Std.Symm (SingletonKempeStep G mutable) :=
  singletonKempeMove_symmetric

theorem singletonKempe_repairHeight_unit_slope
    (G : SimpleGraph V) (mutable : V → Prop)
    (exit : G.Coloring TrominoState → Prop)
    {source target : G.Coloring TrominoState}
    (hstep : SingletonKempeStep G mutable source target)
    (hsource : ∃ n, CanExitAt (SingletonKempeStep G mutable) exit n source)
    (htarget : ∃ n, CanExitAt (SingletonKempeStep G mutable) exit n target) :
    repairHeight (SingletonKempeStep G mutable) exit source hsource ≤
        repairHeight (SingletonKempeStep G mutable) exit target htarget + 1 ∧
      repairHeight (SingletonKempeStep G mutable) exit target htarget ≤
        repairHeight (SingletonKempeStep G mutable) exit source hsource + 1 := by
  exact repairHeight_unit_slope (SingletonKempeStep G mutable) exit
    (singletonKempeStep_symmetric G mutable) hstep hsource htarget

end DkMath.Tromino
