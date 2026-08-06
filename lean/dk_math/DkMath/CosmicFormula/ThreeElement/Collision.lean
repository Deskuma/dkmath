/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.ThreeElement.Assimilation

#print "file: DkMath.CosmicFormula.ThreeElement.Collision"

/-!
# Same-object collision for three-element assimilation

This module closes the collision step for one interaction observation.

Pair-whole assimilation forces the interaction of a fixed flow to converge to
zero. If that same interaction, along the same filter, also assimilates to the
same target `B`, uniqueness of limits forces `B = 0`. A separately supplied
nonzero-target hypothesis then yields the collision obstruction.

The theorem does not compare different flows, different interaction functions,
different filters, or different targets.
-/

namespace DkMath
namespace CosmicFormula
namespace ThreeElement

/--
The common target must be zero when pair-whole assimilation and interaction
assimilation concern the same flow, filter, and target.
-/
theorem target_eq_zero_of_pairWhole_and_interaction_assimilation
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    [NeBot l]
    {B : ℝ}
    (hpair : PairWholeAssimilation F l B)
    (hint : InteractionAssimilation F l B) :
    B = 0 := by
  exact tendsto_nhds_unique
    hint.interaction_tendsto
    (interaction_tendsto_zero_of_pairWholeAssimilation hpair)

/--
A nonzero common target is impossible for same-object pair-whole and
interaction assimilation.
-/
theorem false_of_nonzero_pairWhole_and_interaction_assimilation
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    [NeBot l]
    {B : ℝ}
    (hpair : PairWholeAssimilation F l B)
    (hint : InteractionAssimilation F l B)
    (hB : B ≠ 0) :
    False :=
  hB (target_eq_zero_of_pairWhole_and_interaction_assimilation hpair hint)

/--
Named audit package for a forbidden same-object collision at a nonzero target.

The package keeps the three independent obligations visible: pair-whole
assimilation, interaction assimilation, and nonzeroness of the target.
-/
structure SameObjectCollisionObstruction
    {ι : Type*} (F : ThreeElementFlow ι)
    (l : Filter ι) (B : ℝ) : Prop where
  pair_assimilation :
    PairWholeAssimilation F l B
  interaction_assimilation :
    InteractionAssimilation F l B
  target_ne_zero :
    B ≠ 0

/-- Every certified same-object nonzero collision obstruction is contradictory. -/
theorem false_of_sameObjectCollisionObstruction
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    [NeBot l]
    {B : ℝ}
    (h : SameObjectCollisionObstruction F l B) :
    False :=
  false_of_nonzero_pairWhole_and_interaction_assimilation
    h.pair_assimilation h.interaction_assimilation h.target_ne_zero

end ThreeElement
end CosmicFormula
end DkMath
