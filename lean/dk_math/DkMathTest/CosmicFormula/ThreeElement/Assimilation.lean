/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.ThreeElement.Assimilation
import DkMathTest.CosmicFormula.ThreeElement.Collision
import DkMathTest.CosmicFormula.Rotation.CF2D.ThreeElementBridge
import DkMathTest.CosmicFormula.ThreeElement.Regression

#print "file: DkMathTest.CosmicFormula.ThreeElement.Assimilation"

namespace DkMathTest
namespace CosmicFormula
namespace ThreeElement

open DkMath.CosmicFormula.ThreeElement

private def constantPairFlow (B : ℝ) : ThreeElementFlow ℕ where
  core := fun _ => B
  interaction := fun _ => 0
  gap := fun _ => 0
  squareMass := fun _ => B
  plusWhole := fun _ => B
  minusWhole := fun _ => B
  squareMass_eq := by
    intro i
    simp
  plusWhole_eq := by
    intro i
    simp
  minusWhole_eq := by
    intro i
    simp

private theorem constantPairAssimilation (B : ℝ) :
    PairWholeAssimilation
      (constantPairFlow B) Filter.atTop B where
  plus_tendsto := tendsto_const_nhds
  minus_tendsto := tendsto_const_nhds

example {ι : Type*} (F : ThreeElementFlow ι) (i : ι) :
    F.plusWhole i - F.minusWhole i =
      2 * F.interaction i :=
  plusWhole_sub_minusWhole_eq_two_mul_interaction F i

example (x u : ℕ → ℝ) (i : ℕ) :
    (quadraticFlow x u).interaction i =
      interactionBeam (x i) (u i) :=
  rfl

example (B : ℝ) :
    Filter.Tendsto
      (constantPairFlow B).interaction
      Filter.atTop
      (nhds 0) :=
  interaction_tendsto_zero_of_pairWholeAssimilation
    (constantPairAssimilation B)

example (B : ℝ) :
    Filter.Tendsto
      (constantPairFlow B).core
      Filter.atTop
      (nhds B) := by
  apply core_tendsto_big_of_squareMass_and_gap_zero
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds

#print axioms quadraticFlow
#print axioms plusWhole_sub_minusWhole_eq_two_mul_interaction
#print axioms squareMass_tendsto_of_core_gap
#print axioms plusWhole_tendsto_of_squareMass_interaction
#print axioms minusWhole_tendsto_of_squareMass_interaction
#print axioms core_tendsto_big_of_squareMass_and_gap_zero
#print axioms gap_tendsto_big_of_squareMass_and_core_zero
#print axioms interaction_tendsto_zero_of_pairWholeAssimilation

end ThreeElement
end CosmicFormula
end DkMathTest
