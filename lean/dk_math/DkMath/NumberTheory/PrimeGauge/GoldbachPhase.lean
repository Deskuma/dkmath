/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Goldbach.PrimeWorld
import DkMath.NumberTheory.PrimeGauge.Return

#print "file: DkMath.NumberTheory.PrimeGauge.GoldbachPhase"

/-!
# Goldbach conjugate prime gauges

This module translates the existing finite `ZMod` obstruction observer into
the CF2D regular-kernel phase observer.  The result is intentionally raw:
proper endpoint exceptions remain in `GoldbachProperObstructed` and are not
identified with phase obstruction without extra endpoint hypotheses.
-/

namespace DkMath.NumberTheory.PrimeGauge

open DkMath.CosmicFormula.Rotation.CF2D
open DkMath.NumberTheory

noncomputable section

/-- The CF2D phase marker attached to an obstruction modulus and center. -/
def goldbachGaugeMarker (r n : ℕ) : UnitKernel ℝ :=
  regularKernel r ^ n

/-- The conjugate CF2D phase marker attached to an obstruction modulus/center. -/
def goldbachGaugeConjugateMarker (r n : ℕ) : UnitKernel ℝ :=
  (goldbachGaugeMarker r n)⁻¹

/-- The two Goldbach markers advance by one CF2D step when the center advances. -/
theorem goldbachGaugeMarkers_succ (r n : ℕ) :
    goldbachGaugeMarker r (n + 1) =
        regularKernel r * goldbachGaugeMarker r n ∧
      goldbachGaugeConjugateMarker r (n + 1) =
        (regularKernel r)⁻¹ * goldbachGaugeConjugateMarker r n := by
  constructor
  · simp [goldbachGaugeMarker, pow_succ, mul_comm]
  · unfold goldbachGaugeConjugateMarker goldbachGaugeMarker
    rw [pow_succ]
    rw [mul_inv_rev]

/-- The relative left/right phase of a Goldbach center. -/
def goldbachGaugeRelativePhase (r n : ℕ) : UnitKernel ℝ :=
  goldbachGaugeMarker r n * (goldbachGaugeConjugateMarker r n)⁻¹

/-- The relative phase is the double center phase. -/
theorem goldbachGaugeRelativePhase_eq_pow_two_mul (r n : ℕ) :
    goldbachGaugeRelativePhase r n = regularKernel r ^ (2 * n) := by
  change (regularKernel r ^ n) * ((regularKernel r ^ n)⁻¹)⁻¹ =
    regularKernel r ^ (2 * n)
  rw [inv_inv, ← pow_two, ← pow_mul]
  simp [Nat.mul_comm]

/-- Relative phase return is exactly divisibility of twice the center. -/
theorem goldbachGaugeRelativePhase_eq_one_iff_dvd_two_center
    {r n : ℕ} (hr : 0 < r) :
    goldbachGaugeRelativePhase r n = 1 ↔ r ∣ 2 * n := by
  rw [goldbachGaugeRelativePhase_eq_pow_two_mul,
    regularKernel_pow_eq_one_iff_dvd hr]

/-- Center motion advances relative phase by the fixed two-step marker. -/
theorem goldbachGaugeRelativePhase_succ (r n : ℕ) :
    goldbachGaugeRelativePhase r (n + 1) =
      regularKernel r ^ 2 * goldbachGaugeRelativePhase r n := by
  rw [goldbachGaugeRelativePhase_eq_pow_two_mul,
    goldbachGaugeRelativePhase_eq_pow_two_mul]
  rw [Nat.mul_add, pow_add]
  exact mul_comm _ _

private theorem regularKernel_pow_eq_inv_iff_modEq_zero
    {r u n : ℕ} (hr : 0 < r) :
    regularKernel r ^ u = (regularKernel r ^ n)⁻¹ ↔
      Nat.ModEq r (u + n) 0 := by
  constructor
  · intro h
    apply Nat.modEq_zero_iff_dvd.mpr
    have hpow : regularKernel r ^ (u + n) = 1 := by
      rw [pow_add]
      exact (eq_inv_iff_mul_eq_one.mp h)
    exact (regularKernel_pow_eq_one_iff_dvd hr).mp hpow
  · intro h
    have hpow : regularKernel r ^ (u + n) = 1 :=
      (regularKernel_pow_eq_one_iff_dvd hr).2
        (Nat.modEq_zero_iff_dvd.mp h)
    apply (eq_inv_iff_mul_eq_one).mpr
    rw [← pow_add]
    exact hpow

/--
Raw left Goldbach divisibility is equality of the corresponding CF2D phases.
The bound is required because `n - u` is natural-number subtraction.
-/
theorem goldbachLeftObstructed_iff_gauge_eq
    {n r u : ℕ} (hr : 0 < r) (hu : u ≤ n) :
    GoldbachLeftObstructed n r u ↔
      goldbachGaugeMarker r u = goldbachGaugeMarker r n := by
  unfold goldbachGaugeMarker
  calc
    GoldbachLeftObstructed n r u ↔
        (u : ZMod r) = (n : ZMod r) :=
      goldbach_left_obstructed_iff hu
    _ ↔ Nat.ModEq r u n := ZMod.natCast_eq_natCast_iff u n r
    _ ↔ regularKernel r ^ u = regularKernel r ^ n :=
      (regularKernel_pow_eq_pow_iff_modEq hr).symm

/--
Raw right Goldbach divisibility is equality of the left phase with the
conjugate (inverse) center phase.  No proper-endpoint condition is included.
-/
theorem goldbachRightObstructed_iff_gauge_eq_inv
    {n r u : ℕ} (hr : 0 < r) :
    GoldbachRightObstructed n r u ↔
      goldbachGaugeMarker r u = goldbachGaugeConjugateMarker r n := by
  unfold goldbachGaugeMarker goldbachGaugeConjugateMarker
  calc
    GoldbachRightObstructed n r u ↔
        (u : ZMod r) = -(n : ZMod r) :=
      goldbach_right_obstructed_iff n r u
    _ ↔ Nat.ModEq r (u + n) 0 := by
      rw [← ZMod.natCast_eq_natCast_iff (u + n) 0 r]
      constructor
      · intro h
        rw [Nat.cast_add, h]
        simp
      · intro h
        have hsum : (u : ZMod r) + (n : ZMod r) = 0 := by
          simpa [Nat.cast_add] using h
        exact add_eq_zero_iff_eq_neg.mp hsum
    _ ↔ regularKernel r ^ u = (regularKernel r ^ n)⁻¹ :=
      (regularKernel_pow_eq_inv_iff_modEq_zero hr).symm

end

end DkMath.NumberTheory.PrimeGauge
