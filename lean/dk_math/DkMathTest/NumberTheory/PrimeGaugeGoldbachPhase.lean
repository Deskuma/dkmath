/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimeGauge.GoldbachPhase

#print "file: DkMathTest.NumberTheory.PrimeGaugeGoldbachPhase"

/-!
# Goldbach conjugate gauge regressions

These examples check the raw left/right bridges at a positive modulus.  Proper
endpoint filtering is intentionally outside this checkpoint.
-/

namespace DkMathTest.NumberTheory.PrimeGaugeGoldbachPhase

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimeGauge
open DkMath.CosmicFormula.Rotation.CF2D

example : GoldbachLeftObstructed 11 5 1 := by
  norm_num [GoldbachLeftObstructed]

example : goldbachGaugeMarker 5 1 = goldbachGaugeMarker 5 11 := by
  apply (goldbachLeftObstructed_iff_gauge_eq
    (n := 11) (r := 5) (u := 1) (by decide) (by decide)).1
  norm_num [GoldbachLeftObstructed]

example : ¬ GoldbachLeftObstructed 11 5 2 := by
  norm_num [GoldbachLeftObstructed]

example : goldbachGaugeMarker 5 2 ≠ goldbachGaugeMarker 5 11 := by
  intro h
  have ho : GoldbachLeftObstructed 11 5 2 :=
    (goldbachLeftObstructed_iff_gauge_eq
      (n := 11) (r := 5) (u := 2) (by decide) (by decide)).2 h
  exact (by norm_num [GoldbachLeftObstructed] :
    ¬ GoldbachLeftObstructed 11 5 2) ho

example : GoldbachRightObstructed 11 5 4 := by
  norm_num [GoldbachRightObstructed]

example : goldbachGaugeMarker 5 4 = goldbachGaugeConjugateMarker 5 11 := by
  apply (goldbachRightObstructed_iff_gauge_eq_inv
    (n := 11) (r := 5) (u := 4) (by decide)).1
  norm_num [GoldbachRightObstructed]

example : ¬ GoldbachRightObstructed 11 5 1 := by
  norm_num [GoldbachRightObstructed]

example : goldbachGaugeMarker 5 1 ≠ goldbachGaugeConjugateMarker 5 11 := by
  intro h
  have ho : GoldbachRightObstructed 11 5 1 :=
    (goldbachRightObstructed_iff_gauge_eq_inv
      (n := 11) (r := 5) (u := 1) (by decide)).2 h
  exact (by norm_num [GoldbachRightObstructed] :
    ¬ GoldbachRightObstructed 11 5 1) ho

example : goldbachGaugeMarker 5 (3 + 1) = regularKernel 5 * goldbachGaugeMarker 5 3 ∧
    goldbachGaugeConjugateMarker 5 (3 + 1) =
      (regularKernel 5)⁻¹ * goldbachGaugeConjugateMarker 5 3 := by
  exact goldbachGaugeMarkers_succ 5 3

example : goldbachGaugeRelativePhase 5 3 = regularKernel 5 ^ (2 * 3) := by
  exact goldbachGaugeRelativePhase_eq_pow_two_mul 5 3

example : goldbachGaugeRelativePhase 5 3 ≠ 1 := by
  intro h
  have hd : 5 ∣ 2 * 3 :=
    (goldbachGaugeRelativePhase_eq_one_iff_dvd_two_center
      (r := 5) (n := 3) (by decide)).1 h
  norm_num at hd

example : goldbachGaugeRelativePhase 5 (3 + 1) =
    regularKernel 5 ^ 2 * goldbachGaugeRelativePhase 5 3 := by
  exact goldbachGaugeRelativePhase_succ 5 3

#print axioms goldbachLeftObstructed_iff_gauge_eq
#print axioms goldbachRightObstructed_iff_gauge_eq_inv
#print axioms goldbachGaugeRelativePhase_eq_one_iff_dvd_two_center
#print axioms goldbachGaugeRelativePhase_succ

end DkMathTest.NumberTheory.PrimeGaugeGoldbachPhase
