/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RepairDistance

#print "file: DkMath.Tromino.StateSector"

namespace DkMath.Tromino

variable {State : Type*}

/-! # Restricted relations and rooted sectors

This module is the abstract sectorization layer. Given a relation `R` and a
predicate `A`, `Restricted R A` keeps precisely those edges whose two
endpoints are admissible. A rooted sector is then represented by exact-length
reachability from a chosen root. The central theorem says that a child
relation which is pointwise equal to this restriction has exactly the same
rooted states.

No graph, finiteness assumption, or concrete coloring is used here. -/

/-- Restrict a relation to pairs of admissible states. -/
def Restricted (R : State → State → Prop) (A : State → Prop)
    (x y : State) : Prop :=
  A x ∧ A y ∧ R x y

/-! Symmetry is inherited by swapping both admissibility witnesses and the
underlying edge proof. -/
theorem restricted_symmetric {R : State → State → Prop} {A : State → Prop}
    (hR : Std.Symm R) : Std.Symm (Restricted R A) := by
  constructor
  intro x y hxy
  exact ⟨hxy.2.1, hxy.1, symm_of R hxy.2.2⟩

/-- Reachability by a finite exact-length path from a fixed root. -/
def Reachable (R : State → State → Prop) (root x : State) : Prop :=
  ∃ n, Steps R n root x

/-! The zero-length path makes every state reachable from itself. This is
why rooted chamber APIs carry root admissibility separately. -/
theorem reachable_refl (R : State → State → Prop) (root : State) :
    Reachable R root root :=
  ⟨0, Steps.zero root⟩

theorem reachable_trans (R : State → State → Prop)
    {root x y : State} :
    Reachable R root x → Reachable R x y → Reachable R root y := by
  rintro ⟨n, hrootx⟩ ⟨m, hxy⟩
  exact ⟨n + m, Steps.concat R hrootx hxy⟩

/-! Exact-length paths are invariant under pointwise replacement of the edge
relation. The induction is on the path length, not on the state space. -/
theorem steps_iff_of_iff {R S : State → State → Prop}
    (hRS : ∀ x y, R x y ↔ S x y) {n : Nat} {x y : State} :
    Steps R n x y ↔ Steps S n x y := by
  induction n generalizing x y with
  | zero =>
      constructor <;> intro h <;> cases h <;> exact Steps.zero _
  | succ n ih =>
      constructor
      · intro h
        cases h with
        | prepend hxy hrest =>
            exact Steps.prepend ((hRS _ _).mp hxy) (ih.mp hrest)
      · intro h
        cases h with
        | prepend hxy hrest =>
            exact Steps.prepend ((hRS _ _).mpr hxy) (ih.mpr hrest)

/-- A child relation that is pointwise the restricted parent relation has the
same rooted reachable states as that restricted relation. -/
theorem reachable_iff_restricted
    {childStep parentStep : State → State → Prop}
    {childAdmissible : State → Prop}
    (hchild : ∀ x y,
      childStep x y ↔ Restricted parentStep childAdmissible x y)
    {root x : State} :
    Reachable childStep root x ↔
      Reachable (Restricted parentStep childAdmissible) root x := by
  constructor
  · rintro ⟨n, hpath⟩
    exact ⟨n, (steps_iff_of_iff hchild).mp hpath⟩
  · rintro ⟨n, hpath⟩
    exact ⟨n, (steps_iff_of_iff hchild).mpr hpath⟩

/-! The named sectorization theorem is the same equivalence with the root
and target made explicit, which makes it convenient at application sites. -/
theorem chamber_sectorization
    {childStep parentStep : State → State → Prop}
    {childAdmissible : State → Prop}
    (hchild : ∀ x y,
      childStep x y ↔ Restricted parentStep childAdmissible x y)
    (root x : State) :
    Reachable childStep root x ↔
      Reachable (Restricted parentStep childAdmissible) root x :=
  reachable_iff_restricted hchild

end DkMath.Tromino
