/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.ThreeElement.Collision

#print "file: DkMathTest.CosmicFormula.ThreeElement.Collision"

namespace DkMathTest
namespace CosmicFormula
namespace ThreeElement

open DkMath.CosmicFormula.ThreeElement

private def constantZeroFlow : ThreeElementFlow ℕ where
  core := fun _ => 0
  interaction := fun _ => 0
  gap := fun _ => 0
  squareMass := fun _ => 0
  plusWhole := fun _ => 0
  minusWhole := fun _ => 0
  squareMass_eq := by
    intro i
    simp
  plusWhole_eq := by
    intro i
    simp
  minusWhole_eq := by
    intro i
    simp

private theorem constantZeroPairAssimilation :
    PairWholeAssimilation constantZeroFlow Filter.atTop 0 where
  plus_tendsto := tendsto_const_nhds
  minus_tendsto := tendsto_const_nhds

private theorem constantZeroInteractionAssimilation :
    InteractionAssimilation constantZeroFlow Filter.atTop 0 where
  interaction_tendsto := tendsto_const_nhds

example : (0 : ℝ) = 0 :=
  target_eq_zero_of_pairWhole_and_interaction_assimilation
    constantZeroPairAssimilation
    constantZeroInteractionAssimilation

example
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    [Filter.NeBot l]
    {B : ℝ}
    (hpair : PairWholeAssimilation F l B)
    (hint : InteractionAssimilation F l B)
    (hB : B ≠ 0) :
    False :=
  false_of_nonzero_pairWhole_and_interaction_assimilation hpair hint hB

example
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    [Filter.NeBot l]
    {B : ℝ}
    (h : SameObjectCollisionObstruction F l B) :
    False :=
  false_of_sameObjectCollisionObstruction h

#print axioms target_eq_zero_of_pairWhole_and_interaction_assimilation
#print axioms false_of_nonzero_pairWhole_and_interaction_assimilation
#print axioms false_of_sameObjectCollisionObstruction

end ThreeElement
end CosmicFormula
end DkMathTest
