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
predicate. In particular, no finiteness or concrete Tromino state is used.

The mathematical order is deliberately elementary: `Steps` is the inductive
notion of a path with a prescribed length, `CanExitAt` says that such a path
ends in the exit set, and `repairHeight` is the least admissible length. The
last theorem is the usual graph-metric fact that adjacent reachable vertices
have repair heights differing by at most one.
-/

variable {State : Type*}

/-- An exact-length path in a binary relation.

`Steps step n x y` means that one can move from `x` to `y` in exactly `n`
applications of `step`. The zero constructor is the length-zero path, and
`prepend` adds one edge at the front of a path.
-/
inductive Steps (step : State → State → Prop) : Nat → State → State → Prop
  | zero (x : State) : Steps step 0 x x
  | prepend {n : Nat} {x y z : State} :
      step x y → Steps step n y z → Steps step (n + 1) x z

namespace Steps

/-- The canonical length-zero path. -/
theorem refl (step : State → State → Prop) (x : State) :
    Steps step 0 x x :=
  .zero x

/-- Concatenate two exact-length paths and add their lengths. -/
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

/-- Synonym for `concat`, convenient when reading a path as a sum of steps. -/
theorem add (step : State → State → Prop)
    {n m : Nat} {x y z : State} :
    Steps step n x y → Steps step m y z → Steps step (n + m) x z :=
  concat step

/-- Reverse a path when every edge of the relation can be reversed. -/
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

/-- Reaching an exit in exactly `n` repair steps.

The endpoint is existential because the exit predicate describes a set of
acceptable terminal states rather than one distinguished state.
-/
def CanExitAt (step : State → State → Prop) (exit : State → Prop)
    (n : Nat) (x : State) : Prop :=
  ∃ y, exit y ∧ Steps step n x y

/-- The least exact path length to an exit, for a reachable state.

The reachability witness is an explicit argument. This keeps the definition
constructive at its interface and makes the dependence on the nonempty set of
candidate lengths visible in every theorem about the height.
-/
noncomputable def repairHeight (step : State → State → Prop) (exit : State → Prop)
    (x : State) (hreachable : ∃ n, CanExitAt step exit n x) : Nat :=
  by classical exact Nat.find hreachable

/-- The defining path witnessing the chosen repair height. -/
theorem repairHeight_spec (step : State → State → Prop) (exit : State → Prop)
    (x : State) (hreachable : ∃ n, CanExitAt step exit n x) :
    CanExitAt step exit (repairHeight step exit x hreachable) x := by
  classical
  exact Nat.find_spec hreachable

/-- Minimality of `repairHeight` among all exit-reaching path lengths. -/
theorem repairHeight_minimal (step : State → State → Prop) (exit : State → Prop)
    (x : State) (hreachable : ∃ n, CanExitAt step exit n x)
    {n : Nat} (hn : CanExitAt step exit n x) :
    repairHeight step exit x hreachable ≤ n := by
  classical
  exact Nat.find_min' hreachable hn

/-- An already-exiting state has repair height zero. -/
theorem repairHeight_eq_zero_of_exit
    (step : State → State → Prop) (exit : State → Prop)
    (x : State) (hreachable : ∃ n, CanExitAt step exit n x)
    (hexit : exit x) :
    repairHeight step exit x hreachable = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply repairHeight_minimal step exit x hreachable
  exact ⟨x, hexit, Steps.zero x⟩

/-- Prepending one repair step increases an available exit path by one. -/
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

/-- Unit-slope repair height along a symmetric repair edge.

This is a local Lipschitz statement, not a claim that a global repair search
or an exit state exists for every state. Those hypotheses are supplied
explicitly as `hx` and `hy`.
-/
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
