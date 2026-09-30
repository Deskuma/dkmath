/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RepairDistance

#print "file: DkMath.Tromino.StateSector"

namespace DkMath.Tromino

variable {State : Type*}

/-- Restrict a relation to pairs of admissible states. -/
def Restricted (R : State → State → Prop) (A : State → Prop)
    (x y : State) : Prop :=
  A x ∧ A y ∧ R x y

theorem restricted_symmetric {R : State → State → Prop} {A : State → Prop}
    (hR : Symmetric R) : Symmetric (Restricted R A) := by
  intro x y hxy
  exact ⟨hxy.2.1, hxy.1, hR hxy.2.2⟩

/-- Reachability by a finite exact-length path from a fixed root. -/
def Reachable (R : State → State → Prop) (root x : State) : Prop :=
  ∃ n, Steps R n root x

theorem reachable_refl (R : State → State → Prop) (root : State) :
    Reachable R root root :=
  ⟨0, Steps.zero root⟩

theorem reachable_trans (R : State → State → Prop)
    {root x y : State} :
    Reachable R root x → Reachable R x y → Reachable R root y := by
  rintro ⟨n, hrootx⟩ ⟨m, hxy⟩
  exact ⟨n + m, Steps.concat R hrootx hxy⟩

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
