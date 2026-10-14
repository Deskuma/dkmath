/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.KempeRepair

#print "file: DkMath.Tromino.RepairChamber"

namespace DkMath.Tromino

variable {State : Type*}

/-! # Admissible rooted chambers

An unrestricted path relation may leave the state space on which an
application-level invariant is meaningful. `AdmissibleChamber` therefore
records both admissibility of the root and reachability through the relation
restricted to admissible endpoints. This explicit root witness avoids the
zero-step ambiguity of bare `Reachable`.

The second half of the file specializes this pattern to singleton Kempe
moves and connects chamber edges to the generic repair-height estimate. -/

/-! ## Explicit admissible chambers -/

/-- Rooted reachability in the restricted relation, with an admissible root. -/
def AdmissibleChamber (R : State → State → Prop) (A : State → Prop)
    (root x : State) : Prop :=
  A root ∧ Reachable (Restricted R A) root x

theorem restricted_reachable_target_admissible
    {R : State → State → Prop} {A : State → Prop}
    {root x : State} (hroot : A root) :
    Reachable (Restricted R A) root x → A x := by
  rintro ⟨n, hpath⟩
  induction hpath with
  | zero =>
      exact hroot
  | prepend hstep hrest ih =>
      exact ih hstep.2.1

/-! At the root, the chamber condition reduces exactly to root admissibility;
the reachability half is supplied by the zero-step path. -/
theorem admissibleChamber_root_iff
    {R : State → State → Prop} {A : State → Prop} (root : State) :
    AdmissibleChamber R A root root ↔ A root := by
  constructor
  · intro h
    exact h.1
  · intro hroot
    exact ⟨hroot, reachable_refl (Restricted R A) root⟩

theorem admissibleChamber_target
    {R : State → State → Prop} {A : State → Prop}
    {root x : State} (h : AdmissibleChamber R A root x) :
    A x := by
  exact restricted_reachable_target_admissible h.1 h.2

theorem admissibleChamber_reachable
    {R : State → State → Prop} {A : State → Prop}
    {root x : State} (h : AdmissibleChamber R A root x) :
    Reachable (Restricted R A) root x :=
  h.2

/-! ## Concrete singleton-Kempe chamber -/

def AdmissibleSingletonKempeStep {V : Type*} (G : SimpleGraph V)
    (mutable : V → Prop) (admissible : G.Coloring TrominoState → Prop) :
    G.Coloring TrominoState → G.Coloring TrominoState → Prop :=
  Restricted (SingletonKempeStep G mutable) admissible

theorem admissibleSingletonKempeStep_symmetric
    {V : Type*} (G : SimpleGraph V) (mutable : V → Prop)
    (admissible : G.Coloring TrominoState → Prop) :
    Std.Symm (AdmissibleSingletonKempeStep G mutable admissible) := by
  exact restricted_symmetric (singletonKempeStep_symmetric G mutable)

theorem onePointRecolor_admissibleSingletonKempeStep
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    {admissible : G.Coloring TrominoState → Prop}
    {source target : G.Coloring TrominoState}
    (hrecolor : OnePointRecolor G mutable source target)
    (hsource : admissible source) (htarget : admissible target) :
    AdmissibleSingletonKempeStep G mutable admissible source target := by
  exact ⟨hsource, htarget, onePointRecolor_singletonKempeMove hrecolor⟩

def SingletonKempeRepairChamber {V : Type*} (G : SimpleGraph V)
    (mutable : V → Prop) (admissible : G.Coloring TrominoState → Prop)
    (root x : G.Coloring TrominoState) : Prop :=
  AdmissibleChamber (SingletonKempeStep G mutable) admissible root x

theorem singletonKempeRepairChamber_root_iff
    {V : Type*} (G : SimpleGraph V) (mutable : V → Prop)
    (admissible : G.Coloring TrominoState → Prop)
    (root : G.Coloring TrominoState) :
    SingletonKempeRepairChamber G mutable admissible root root ↔
      admissible root :=
  admissibleChamber_root_iff root

theorem singletonKempeRepairChamber_target
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    {admissible : G.Coloring TrominoState → Prop}
    {root x : G.Coloring TrominoState}
    (h : SingletonKempeRepairChamber G mutable admissible root x) :
    admissible x :=
  admissibleChamber_target h

theorem singletonKempeRepairChamber_reachable
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    {admissible : G.Coloring TrominoState → Prop}
    {root x : G.Coloring TrominoState}
    (h : SingletonKempeRepairChamber G mutable admissible root x) :
    Reachable (Restricted (SingletonKempeStep G mutable) admissible) root x :=
  admissibleChamber_reachable h

theorem childStep_reachable_iff_singletonKempeRepairChamber
    {V : Type*} {G : SimpleGraph V} {mutable : V → Prop}
    {admissible : G.Coloring TrominoState → Prop}
    {childStep : G.Coloring TrominoState → G.Coloring TrominoState → Prop}
    {root x : G.Coloring TrominoState}
    (hroot : admissible root)
    (hchild : ∀ source target,
      childStep source target ↔
        AdmissibleSingletonKempeStep G mutable admissible source target) :
    Reachable childStep root x ↔
      SingletonKempeRepairChamber G mutable admissible root x := by
  constructor
  · intro hreach
    refine ⟨hroot, ?_⟩
    exact (reachable_iff_restricted hchild).mp hreach
  · intro hchamber
    exact (reachable_iff_restricted hchild).mpr hchamber.2

/-! ## Full repair-distance unit slope across chamber edges -/

theorem admissibleSingletonKempeStep_repairHeight_unit_slope
    {V : Type*} (G : SimpleGraph V) (mutable : V → Prop)
    (admissible : G.Coloring TrominoState → Prop)
    (exit : G.Coloring TrominoState → Prop)
    {source target : G.Coloring TrominoState}
    (hchamber : AdmissibleSingletonKempeStep G mutable admissible source target)
    (hsource : ∃ n, CanExitAt (SingletonKempeStep G mutable) exit n source)
    (htarget : ∃ n, CanExitAt (SingletonKempeStep G mutable) exit n target) :
    repairHeight (SingletonKempeStep G mutable) exit source hsource ≤
        repairHeight (SingletonKempeStep G mutable) exit target htarget + 1 ∧
      repairHeight (SingletonKempeStep G mutable) exit target htarget ≤
        repairHeight (SingletonKempeStep G mutable) exit source hsource + 1 := by
  exact singletonKempe_repairHeight_unit_slope G mutable exit
    hchamber.2.2 hsource htarget

end DkMath.Tromino
