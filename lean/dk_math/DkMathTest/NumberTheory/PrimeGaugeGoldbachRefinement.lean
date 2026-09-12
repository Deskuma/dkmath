/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Primitive.PHZ30
import DkMath.NumberTheory.PrimeGauge.GoldbachRefinement

#print "file: DkMathTest.NumberTheory.PrimeGaugeGoldbachRefinement"

/-!
# Paired Goldbach child regressions

The examples use the finite world `{2, 3, 5}`, fresh `q = 7`, parent `r = 1`,
and center `n = 10`.  They check the two raw phase targets and the resulting
`q - 2` surviving child count.
-/

namespace DkMathTest.NumberTheory.PrimeGaugeGoldbachRefinement

open DkMath.NumberTheory
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimeGauge

private theorem fresh_seven : 7 ∉ primeWorld235 := by
  simp [primeWorld235]

example : ∃! j : ℕ,
    j < 7 ∧
    (primeWorldChild primeWorld235 1 j : ZMod 7) = (10 : ZMod 7) := by
  exact existsUnique_leftReservedChild knownPrimeScales_primeWorld235
    (hq := by norm_num) (hqS := fresh_seven) (hr := by norm_num) 10

example : ∃! j : ℕ,
    j < 7 ∧
    (primeWorldChild primeWorld235 1 j : ZMod 7) = -(10 : ZMod 7) := by
  exact existsUnique_rightReservedChild knownPrimeScales_primeWorld235
    (hq := by norm_num) (hqS := fresh_seven) (hr := by norm_num) 10

example : ¬ (7 : ℕ) ∣ 2 * 10 := by
  norm_num

example :
    (pairedReservedChildIndices 10 primeWorld235 7 1).card = 2 := by
  apply pairedReservedChildIndices_card_eq_two
    knownPrimeScales_primeWorld235
  · norm_num
  · exact fresh_seven
  · norm_num
  · norm_num

example :
    (pairedSurvivingChildIndices 10 primeWorld235 7 1).card = 7 - 2 := by
  apply pairedSurvivingChildIndices_card_eq_q_sub_two
    knownPrimeScales_primeWorld235
  · norm_num
  · exact fresh_seven
  · norm_num
  · norm_num

#print axioms pairedReservedChildIndices_card_eq_two
#print axioms pairedSurvivingChildIndices_card_eq_q_sub_two

end DkMathTest.NumberTheory.PrimeGaugeGoldbachRefinement

