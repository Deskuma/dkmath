/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Tromino.RepairDistance"

namespace DkMath.Tromino

/-! # Exact-length paths and repair distance

This file contains the graph-independent kernel for distance to an exit
predicate.  In particular, no finiteness or concrete Tromino state is used.
-/

variable {State : Type*}

/-- An exact-length path in a binary relation. -/
inductive Steps (step : State → State → Prop) : Nat → State → State → Prop
  | zero (x : State) : Steps step 0 x x
  | prepend {n : Nat} {x y z : State} :
      step x y → Steps step n y z → Steps step (n + 1) x z

namespace Steps

theorem refl (step : State → State → Prop) (x : State) :
    Steps step 0 x x :=
  .zero x

theorem concat (step : State → State → Prop)
    {n m : Nat} {x y z : State} :
    Steps step n x y → Steps step m y z → Steps step (n + m) x z := by
  intro hxy hyz
  induction hxy with
  | zero =>
      simpa using hyz
  | @prepend n x y z hxy hrest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.prepend hxy (ih hyz)

theorem add (step : State → State → Prop)
    {n m : Nat} {x y z : State} :
    Steps step n x y → Steps step m y z → Steps step (n + m) x z :=
  concat step

theorem reverse_of_symmetric (step : State → State → Prop)
    (hsymm : Std.Symm step) {n : Nat} {x y : State} :
    Steps step n x y → Steps step n y x := by
  intro hxy
  induction hxy with
  | zero =>
      exact Steps.zero _
  | @prepend n x y z hxy hrest ih =>
      have hend : Steps step 1 y x := by
        exact Steps.prepend (symm_of step hxy) (Steps.zero x)
      simpa using Steps.concat step ih hend

end Steps

/-- Reaching an exit in exactly `n` repair steps. -/
def CanExitAt (step : State → State → Prop) (exit : State → Prop)
    (n : Nat) (x : State) : Prop :=
  ∃ y, exit y ∧ Steps step n x y

/-- The least exact path length to an exit, for a reachable state. -/
noncomputable def repairHeight (step : State → State → Prop) (exit : State → Prop)
    (x : State) (hreachable : ∃ n, CanExitAt step exit n x) : Nat :=
  by classical exact Nat.find hreachable

theorem repairHeight_spec (step : State → State → Prop) (exit : State → Prop)
    (x : State) (hreachable : ∃ n, CanExitAt step exit n x) :
    CanExitAt step exit (repairHeight step exit x hreachable) x := by
  classical
  exact Nat.find_spec hreachable

theorem repairHeight_minimal (step : State → State → Prop) (exit : State → Prop)
    (x : State) (hreachable : ∃ n, CanExitAt step exit n x)
    {n : Nat} (hn : CanExitAt step exit n x) :
    repairHeight step exit x hreachable ≤ n := by
  classical
  exact Nat.find_min' hreachable hn

theorem repairHeight_eq_zero_of_exit
    (step : State → State → Prop) (exit : State → Prop)
    (x : State) (hreachable : ∃ n, CanExitAt step exit n x)
    (hexit : exit x) :
    repairHeight step exit x hreachable = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply repairHeight_minimal step exit x hreachable
  exact ⟨x, hexit, Steps.zero x⟩

theorem repairHeight_le_succ_of_step
    (step : State → State → Prop) (exit : State → Prop)
    {x y : State}
    (hxy : step x y)
    (hx : ∃ n, CanExitAt step exit n x)
    (hy : ∃ n, CanExitAt step exit n y) :
    repairHeight step exit x hx ≤ repairHeight step exit y hy + 1 := by
  classical
  rcases repairHeight_spec step exit y hy with ⟨z, hzexit, hyz⟩
  apply repairHeight_minimal step exit x hx
  refine ⟨z, hzexit, ?_⟩
  exact Steps.prepend hxy hyz

theorem repairHeight_unit_slope
    (step : State → State → Prop) (exit : State → Prop)
    (hsymm : Std.Symm step) {x y : State}
    (hxy : step x y)
    (hx : ∃ n, CanExitAt step exit n x)
    (hy : ∃ n, CanExitAt step exit n y) :
    repairHeight step exit x hx ≤ repairHeight step exit y hy + 1 ∧
      repairHeight step exit y hy ≤ repairHeight step exit x hx + 1 := by
  classical
  constructor
  · exact repairHeight_le_succ_of_step step exit hxy hx hy
  · exact repairHeight_le_succ_of_step step exit (symm_of step hxy) hy hx

end DkMath.Tromino
