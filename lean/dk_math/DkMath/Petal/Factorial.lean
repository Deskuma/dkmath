/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Counting

#print "file: DkMath.Petal.Factorial"

/-!
# Petal factorial

This module builds factorial from the canonical Petal orbit.  The initial
core is the least valid core `1`, and the lap bases are `1, 2, 3, ...`.
Consequently `factorialPetal 0 = 1` means zero laps from the unit core; it is
not the value of the degenerate zero core.

The `Nat.factorial` theorem below is a compatibility boundary.  The primary
zero and successor laws are proved from the Petal orbit API first.
-/

namespace DkMath
namespace Petal

/-- Factorial as a Petal orbit from the least valid core. -/
def factorialPetal (n : Nat) : Nat :=
  petalOrbitTotal unitPetalCore.1 (fun i => i + 1) n

/-- The zero-lap factorial Petal preserves its unit core. -/
@[simp]
theorem factorialPetal_zero :
    factorialPetal 0 = 1 := by
  simp [factorialPetal, petalOrbitTotal, dynamicOrbitTotal_zero, unitPetalCore]

/-- One more factorial Petal lap uses the next successor base. -/
theorem factorialPetal_succ (n : Nat) :
    factorialPetal (n + 1) = factorialPetal n * (n + 1) := by
  simpa [factorialPetal, unitPetalCore] using
    (petalOrbitTotal_succ unitPetalCore.1 (fun i => i + 1) n)

/-- The factorial Petal is positive at every lap. -/
theorem factorialPetal_pos (n : Nat) :
    0 < factorialPetal n := by
  unfold factorialPetal
  apply petalOrbitTotal_pos
  · simp [unitPetalCore]
  · intro i
    omega

/-- The factorial Petal is the successor-base orbit with unit initial factor. -/
theorem factorialPetal_eq_dynamicOrbitTotal (n : Nat) :
    factorialPetal n = dynamicOrbitTotal (fun i => i + 1) n := by
  simp [factorialPetal, petalOrbitTotal, unitPetalCore]

/-- Compatibility of the Petal factorial with Mathlib's natural factorial. -/
theorem factorialPetal_eq_factorial (n : Nat) :
    factorialPetal n = Nat.factorial n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [factorialPetal_succ, ih, Nat.factorial_succ]
      exact Nat.mul_comm _ _

/-- Compatibility alias for the successor-base raw orbit. -/
theorem dynamicOrbitTotal_succIndex_eq_factorial (k : Nat) :
    dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k := by
  calc
    dynamicOrbitTotal (fun i => i + 1) k = factorialPetal k :=
      (factorialPetal_eq_dynamicOrbitTotal k).symm
    _ = Nat.factorial k := factorialPetal_eq_factorial k

/-! Small values make the successor-base indexing convention explicit. -/

example : factorialPetal 0 = 1 := by
  decide

example : factorialPetal 1 = 1 := by
  decide

example : factorialPetal 2 = 2 := by
  decide

example : factorialPetal 3 = 6 := by
  decide

example : factorialPetal 4 = 24 := by
  decide

end Petal
end DkMath
