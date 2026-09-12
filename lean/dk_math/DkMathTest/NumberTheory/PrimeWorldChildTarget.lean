/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Primitive.PHZ30
import DkMath.NumberTheory.Primitive.PrimeWorldRefinement

#print "file: DkMathTest.NumberTheory.PrimeWorldChildTarget"

/-!
# Target-congruence child regressions

These examples exercise the arbitrary-`ZMod q` target form of the bounded
child observer.  The children remain candidate seats; no primality conclusion
is drawn from the congruence.
-/

namespace DkMathTest.NumberTheory.PrimeWorldChildTarget

open DkMath.NumberTheory
open DkMath.NumberTheory.Primitive

private theorem fresh_seven : 7 ∉ primeWorld235 := by
  simp [primeWorld235]

example : ∃! j : ℕ,
    j < 7 ∧
    (primeWorldChild primeWorld235 1 j : ZMod 7) = (0 : ZMod 7) := by
  exact existsUnique_child_eq_target knownPrimeScales_primeWorld235
    (hq := by norm_num) (hqS := fresh_seven) (hr := by norm_num)
    (0 : ZMod 7)

example : ∃! j : ℕ,
    j < 7 ∧
    (primeWorldChild primeWorld235 1 j : ZMod 7) = (3 : ZMod 7) := by
  exact existsUnique_child_eq_target knownPrimeScales_primeWorld235
    (hq := by norm_num) (hqS := fresh_seven) (hr := by norm_num)
    (3 : ZMod 7)

example : ∃! j : ℕ,
    j < 7 ∧
    (primeWorldChild primeWorld235 1 j : ZMod 7) = (6 : ZMod 7) := by
  exact existsUnique_child_eq_target knownPrimeScales_primeWorld235
    (hq := by norm_num) (hqS := fresh_seven) (hr := by norm_num)
    (6 : ZMod 7)

example : ∃ j : ℕ,
    j < 7 ∧
    (primeWorldChild primeWorld235 1 j : ZMod 7) = (3 : ZMod 7) ∧ j = 1 := by
  obtain ⟨j, hj, hju⟩ := existsUnique_child_eq_target
    knownPrimeScales_primeWorld235
    (q := 7) (r := 1) (hq := by norm_num) (hqS := fresh_seven)
    (hr := by norm_num)
    (3 : ZMod 7)
  refine ⟨j, hj.1, hj.2, ?_⟩
  symm
  apply hju 1
  constructor
  · norm_num
  · norm_num [primeWorldChild, primeWorldModulus, primeWorld235]
    decide

#print axioms DkMath.NumberTheory.Primitive.existsUnique_child_eq_target

end DkMathTest.NumberTheory.PrimeWorldChildTarget
