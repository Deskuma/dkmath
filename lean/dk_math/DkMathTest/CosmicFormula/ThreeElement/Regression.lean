/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.ThreeElement.MagicCore
import DkMath.CosmicFormula.ThreeElement.Collision
import DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge

#print "file: DkMathTest.CosmicFormula.ThreeElement.Regression"

/-!
# Three-element assimilation integration regression

This final test module checks the full route from static realizations through
explicit dynamic flows to the same-object collision theorem and the CF2D
square-mass bridge.

The constant schedules below are explicit providers. They do not infer a
`Tendsto` statement from a static square-root witness alone.
-/

namespace DkMathTest.CosmicFormula.ThreeElement.Regression

open DkMath.CosmicFormula.ThreeElement
open DkMath.CosmicFormula.Rotation.CF2D

/-- A numerical regression for the symmetric interaction realization. -/
private theorem sqrtTwo_interaction_eq_four :
    interactionBeam (Real.sqrt 2) (Real.sqrt 2) = 4 := by
  calc
    interactionBeam (Real.sqrt 2) (Real.sqrt 2) =
        2 * (Real.sqrt 2) ^ 2 := by
      simp only [interactionBeam, pow_two]
      ring
    _ = 2 * 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ = 4 := by norm_num

example : interactionBeam (Real.sqrt 2) (Real.sqrt 2) = 4 :=
  sqrtTwo_interaction_eq_four

/--
An explicit Core chart: the first coordinate is constantly `sqrt B` and the
second coordinate is constantly zero.
-/
private def coreChartFlow (B : ℝ) : ThreeElementFlow ℕ :=
  quadraticFlow
    (fun _ => Real.sqrt B)
    (fun _ => 0)

private theorem coreChart_core_tendsto
    {B : ℝ} (hB : 0 ≤ B) :
    Filter.Tendsto
      (coreChartFlow B).core
      Filter.atTop
      (nhds B) := by
  simpa [coreChartFlow, quadraticFlow, coreTerm,
    Real.sq_sqrt hB] using
    (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => B) Filter.atTop (nhds B))

private theorem coreChart_interaction_tendsto_zero
    (B : ℝ) :
    Filter.Tendsto
      (coreChartFlow B).interaction
      Filter.atTop
      (nhds 0) := by
  simpa [coreChartFlow, quadraticFlow, interactionBeam] using
    (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))

private theorem coreChart_gap_tendsto_zero
    (B : ℝ) :
    Filter.Tendsto
      (coreChartFlow B).gap
      Filter.atTop
      (nhds 0) := by
  simpa [coreChartFlow, quadraticFlow, gapTerm] using
    (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))

private theorem coreChart_squareMass_tendsto
    {B : ℝ} (hB : 0 ≤ B) :
    Filter.Tendsto
      (coreChartFlow B).squareMass
      Filter.atTop
      (nhds B) := by
  simpa [coreChartFlow, quadraticFlow, squareMass, coreTerm, gapTerm,
    Real.sq_sqrt hB] using
    (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => B) Filter.atTop (nhds B))

private theorem coreChart_pairWholeAssimilation
    {B : ℝ} (hB : 0 ≤ B) :
    PairWholeAssimilation (coreChartFlow B) Filter.atTop B where
  plus_tendsto := by
    simpa [coreChartFlow, quadraticFlow, plusWhole,
      Real.sq_sqrt hB] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => B) Filter.atTop (nhds B))
  minus_tendsto := by
    simpa [coreChartFlow, quadraticFlow, minusWhole,
      Real.sq_sqrt hB] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => B) Filter.atTop (nhds B))

example {B : ℝ} (hB : 0 ≤ B) :
    Filter.Tendsto
      (coreChartFlow B).core
      Filter.atTop
      (nhds B) :=
  coreChart_core_tendsto hB

example (B : ℝ) :
    Filter.Tendsto
      (coreChartFlow B).interaction
      Filter.atTop
      (nhds 0) :=
  coreChart_interaction_tendsto_zero B

example (B : ℝ) :
    Filter.Tendsto
      (coreChartFlow B).gap
      Filter.atTop
      (nhds 0) :=
  coreChart_gap_tendsto_zero B

example {B : ℝ} (hB : 0 ≤ B) :
    Filter.Tendsto
      (coreChartFlow B).squareMass
      Filter.atTop
      (nhds B) :=
  coreChart_squareMass_tendsto hB

example {B : ℝ} (hB : 0 ≤ B) :
    PairWholeAssimilation (coreChartFlow B) Filter.atTop B :=
  coreChart_pairWholeAssimilation hB

/--
A static symmetric interaction realization equipped with an explicit constant
schedule. Its interaction tends to `4`, but it cannot also provide pair-whole
assimilation to the same nonzero target.
-/
private def symmetricInteractionChartFlow : ThreeElementFlow ℕ :=
  quadraticFlow
    (fun _ => Real.sqrt 2)
    (fun _ => Real.sqrt 2)

private theorem symmetricInteractionChartAssimilation :
    InteractionAssimilation
      symmetricInteractionChartFlow
      Filter.atTop
      4 where
  interaction_tendsto := by
    simpa [symmetricInteractionChartFlow, quadraticFlow,
      sqrtTwo_interaction_eq_four] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (4 : ℝ)) Filter.atTop (nhds 4))

example :
    InteractionAssimilation
      symmetricInteractionChartFlow
      Filter.atTop
      4 :=
  symmetricInteractionChartAssimilation

example :
    ¬ PairWholeAssimilation
      symmetricInteractionChartFlow
      Filter.atTop
      4 := by
  intro hpair
  exact false_of_nonzero_pairWhole_and_interaction_assimilation
    hpair
    symmetricInteractionChartAssimilation
    (by norm_num)

/-- The integrated CF2D route preserves square mass under every unit action. -/
example (r : UnitKernel ℝ) (z : Vec ℝ) :
    squareMass
        (UnitKernel.act r z).core
        (UnitKernel.act r z).beam =
      squareMass z.core z.beam :=
  cf2d_q2_act_preserved r z

example (z : Vec ℝ) :
    cf2dInteractionBeam (Vec.conj z) =
      -cf2dInteractionBeam z := by
  simp

example (z : Vec ℝ) :
    cf2dPlusWhole (Vec.conj z) =
      cf2dMinusWhole z := by
  simp

#print axioms DkMath.CosmicFormula.ThreeElement.interaction_tendsto_zero_of_pairWholeAssimilation
#print axioms DkMath.CosmicFormula.ThreeElement.target_eq_zero_of_pairWhole_and_interaction_assimilation
#print axioms DkMath.CosmicFormula.ThreeElement.false_of_nonzero_pairWhole_and_interaction_assimilation
#print axioms DkMath.CosmicFormula.Rotation.CF2D.cf2d_q2_act_preserved

end DkMathTest.CosmicFormula.ThreeElement.Regression
