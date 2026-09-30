/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RepairDistance

#print "file: DkMathTest.Tromino.RepairDistanceRegression"

namespace DkMathTest.Tromino

open DkMath.Tromino

inductive PathState
  | left
  | middle
  | right
  deriving DecidableEq

def pathStep : PathState → PathState → Prop
  | .left, .middle => True
  | .middle, .left => True
  | .middle, .right => True
  | .right, .middle => True
  | _, _ => False

def pathExit : PathState → Prop
  | .left => True
  | _ => False

theorem pathStep_symmetric : Symmetric pathStep := by
  intro x y h
  cases x <;> cases y <;> simp_all [pathStep]

theorem left_reachable :
    ∃ n, CanExitAt pathStep pathExit n .left := by
  exact ⟨0, .left, trivial, Steps.zero _⟩

theorem middle_reachable :
    ∃ n, CanExitAt pathStep pathExit n .middle := by
  refine ⟨1, .left, trivial, ?_⟩
  exact Steps.prepend (x := PathState.middle) (y := PathState.left)
    (z := PathState.left)
    (by simp [pathStep]) (Steps.zero _)

theorem right_reachable :
    ∃ n, CanExitAt pathStep pathExit n .right := by
  refine ⟨2, .left, trivial, ?_⟩
  exact Steps.prepend (x := PathState.right) (y := PathState.middle)
    (z := PathState.left)
    (by simp [pathStep])
    (Steps.prepend (x := PathState.middle) (y := PathState.left)
      (z := PathState.left)
      (by simp [pathStep]) (Steps.zero _))

theorem path_height_left :
    repairHeight pathStep pathExit .left left_reachable = 0 := by
  exact repairHeight_eq_zero_of_exit pathStep pathExit .left left_reachable trivial

theorem path_height_middle :
    repairHeight pathStep pathExit .middle middle_reachable = 1 := by
  have hle := repairHeight_minimal pathStep pathExit .middle middle_reachable
    (n := 1) (by
      refine ⟨.left, trivial, ?_⟩
      exact Steps.prepend (x := PathState.middle) (y := PathState.left)
        (z := PathState.left)
        (by simp [pathStep]) (Steps.zero _))
  have hnotzero : repairHeight pathStep pathExit .middle middle_reachable ≠ 0 := by
    intro hzero
    have hspec := repairHeight_spec pathStep pathExit .middle middle_reachable
    rw [hzero] at hspec
    rcases hspec with ⟨y, hy, hpath⟩
    cases hpath
    cases hy
  omega

theorem path_height_right :
    repairHeight pathStep pathExit .right right_reachable = 2 := by
  have hle := repairHeight_minimal pathStep pathExit .right right_reachable
    (n := 2) (by
      refine ⟨.left, trivial, ?_⟩
      exact Steps.prepend (x := PathState.right) (y := PathState.middle)
        (z := PathState.left)
        (by simp [pathStep])
        (Steps.prepend (x := PathState.middle) (y := PathState.left)
          (z := PathState.left)
          (by simp [pathStep]) (Steps.zero _)))
  have hnotzero : repairHeight pathStep pathExit .right right_reachable ≠ 0 := by
    intro hzero
    have hspec := repairHeight_spec pathStep pathExit .right right_reachable
    rw [hzero] at hspec
    rcases hspec with ⟨y, hy, hpath⟩
    cases hpath
    cases hy
  have hnotone : repairHeight pathStep pathExit .right right_reachable ≠ 1 := by
    intro hone
    have hspec := repairHeight_spec pathStep pathExit .right right_reachable
    rw [hone] at hspec
    rcases hspec with ⟨y, hy, hpath⟩
    cases hpath with
    | prepend hstep hrest =>
        cases hrest
        cases y <;> simp [pathStep, pathExit] at *
  omega

theorem path_unit_slope_middle_right :
    repairHeight pathStep pathExit .middle middle_reachable ≤
        repairHeight pathStep pathExit .right right_reachable + 1 ∧
      repairHeight pathStep pathExit .right right_reachable ≤
        repairHeight pathStep pathExit .middle middle_reachable + 1 := by
  exact repairHeight_unit_slope pathStep pathExit pathStep_symmetric
    (by simp [pathStep]) middle_reachable right_reachable

end DkMathTest.Tromino
