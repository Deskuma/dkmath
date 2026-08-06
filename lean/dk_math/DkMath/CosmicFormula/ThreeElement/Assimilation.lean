/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.ThreeElement.Basic

#print "file: DkMath.CosmicFormula.ThreeElement.Assimilation"

/-!
# Dynamic assimilation limits for three-element states

This module separates dynamic limit data from the static square-root witnesses
in `ThreeElement.MagicCore`.

A `ThreeElementFlow` records six real-valued observations together with their
three exact relations. `PairWholeAssimilation` then requires the plus and minus
wholes of the same flow, along the same filter, to converge to the same target.
Under precisely that same-object/same-filter/same-target hypothesis, the
interaction component converges to zero.

No RH-, zeta-, complex-phase-, angle-, or trigonometric-specific assumption is
used here.
-/

namespace DkMath
namespace CosmicFormula
namespace ThreeElement

/--
A dynamic three-element state indexed by `ι`.

The fields `squareMass`, `plusWhole`, and `minusWhole` remain separate
observations. Their exact relations are carried explicitly and are not replaced
by an overloaded notion of `Big`.
-/
structure ThreeElementFlow (ι : Type*) where
  core : ι → ℝ
  interaction : ι → ℝ
  gap : ι → ℝ
  squareMass : ι → ℝ
  plusWhole : ι → ℝ
  minusWhole : ι → ℝ
  squareMass_eq :
    ∀ i, squareMass i = core i + gap i
  plusWhole_eq :
    ∀ i, plusWhole i = squareMass i + interaction i
  minusWhole_eq :
    ∀ i, minusWhole i = squareMass i - interaction i

/-- Build a dynamic flow from two real-valued quadratic coordinates. -/
def quadraticFlow
    {ι : Type*} (x u : ι → ℝ) :
    ThreeElementFlow ι where
  core := fun i => coreTerm (x i)
  interaction := fun i => interactionBeam (x i) (u i)
  gap := fun i => gapTerm (u i)
  squareMass := fun i =>
    DkMath.CosmicFormula.ThreeElement.squareMass (x i) (u i)
  plusWhole := fun i =>
    DkMath.CosmicFormula.ThreeElement.plusWhole (x i) (u i)
  minusWhole := fun i =>
    DkMath.CosmicFormula.ThreeElement.minusWhole (x i) (u i)
  squareMass_eq := by
    intro i
    rfl
  plusWhole_eq := by
    intro i
    simp only [DkMath.CosmicFormula.ThreeElement.plusWhole,
      DkMath.CosmicFormula.ThreeElement.squareMass,
      coreTerm, interactionBeam, gapTerm]
    ring
  minusWhole_eq := by
    intro i
    simp only [DkMath.CosmicFormula.ThreeElement.minusWhole,
      DkMath.CosmicFormula.ThreeElement.squareMass,
      coreTerm, interactionBeam, gapTerm]
    ring

/-- The exact difference of the two whole observations extracts interaction. -/
theorem plusWhole_sub_minusWhole_eq_two_mul_interaction
    {ι : Type*} (F : ThreeElementFlow ι) (i : ι) :
    F.plusWhole i - F.minusWhole i =
      2 * F.interaction i := by
  rw [F.plusWhole_eq i, F.minusWhole_eq i]
  ring

/--
The plus and minus wholes of one flow converge along one filter to one target.
-/
structure PairWholeAssimilation
    {ι : Type*} (F : ThreeElementFlow ι)
    (l : Filter ι) (B : ℝ) : Prop where
  plus_tendsto :
    Filter.Tendsto F.plusWhole l (nhds B)
  minus_tendsto :
    Filter.Tendsto F.minusWhole l (nhds B)

/--
The interaction observation of one flow converges along one filter to one
target. This provider is kept separate from pair-whole assimilation.
-/
structure InteractionAssimilation
    {ι : Type*} (F : ThreeElementFlow ι)
    (l : Filter ι) (B : ℝ) : Prop where
  interaction_tendsto :
    Filter.Tendsto F.interaction l (nhds B)

/-- Core and Gap limits combine into the square-mass limit. -/
theorem squareMass_tendsto_of_core_gap
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    {C G : ℝ}
    (hcore : Filter.Tendsto F.core l (nhds C))
    (hgap : Filter.Tendsto F.gap l (nhds G)) :
    Filter.Tendsto F.squareMass l (nhds (C + G)) := by
  simpa only [F.squareMass_eq] using hcore.add hgap

/-- Square mass and interaction limits combine into the plus-whole limit. -/
theorem plusWhole_tendsto_of_squareMass_interaction
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    {M I : ℝ}
    (hmass : Filter.Tendsto F.squareMass l (nhds M))
    (hinteraction : Filter.Tendsto F.interaction l (nhds I)) :
    Filter.Tendsto F.plusWhole l (nhds (M + I)) := by
  simpa only [F.plusWhole_eq] using hmass.add hinteraction

/-- Square mass and interaction limits combine into the minus-whole limit. -/
theorem minusWhole_tendsto_of_squareMass_interaction
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    {M I : ℝ}
    (hmass : Filter.Tendsto F.squareMass l (nhds M))
    (hinteraction : Filter.Tendsto F.interaction l (nhds I)) :
    Filter.Tendsto F.minusWhole l (nhds (M - I)) := by
  simpa only [F.minusWhole_eq] using hmass.sub hinteraction

/-- If square mass tends to `B` and Gap collapses, Core assimilates to `B`. -/
theorem core_tendsto_big_of_squareMass_and_gap_zero
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    {B : ℝ}
    (hmass : Filter.Tendsto F.squareMass l (nhds B))
    (hgap : Filter.Tendsto F.gap l (nhds 0)) :
    Filter.Tendsto F.core l (nhds B) := by
  simpa only [F.squareMass_eq, add_sub_cancel_right, sub_zero] using
    hmass.sub hgap

/-- If square mass tends to `B` and Core collapses, Gap assimilates to `B`. -/
theorem gap_tendsto_big_of_squareMass_and_core_zero
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    {B : ℝ}
    (hmass : Filter.Tendsto F.squareMass l (nhds B))
    (hcore : Filter.Tendsto F.core l (nhds 0)) :
    Filter.Tendsto F.gap l (nhds B) := by
  simpa only [F.squareMass_eq, add_sub_cancel_left, sub_zero] using
    hmass.sub hcore

/--
Same-flow, same-filter, same-target pair-whole assimilation forces the
interaction observation to converge to zero.
-/
theorem interaction_tendsto_zero_of_pairWholeAssimilation
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    {B : ℝ}
    (h : PairWholeAssimilation F l B) :
    Filter.Tendsto F.interaction l (nhds 0) := by
  have htwice :
      Filter.Tendsto (fun i => 2 * F.interaction i) l (nhds 0) := by
    simpa only [plusWhole_sub_minusWhole_eq_two_mul_interaction, sub_self] using
      h.plus_tendsto.sub h.minus_tendsto
  convert htwice.const_mul (1 / 2 : ℝ) using 1
  · funext i
    ring
  · ring

end ThreeElement
end CosmicFormula
end DkMath
