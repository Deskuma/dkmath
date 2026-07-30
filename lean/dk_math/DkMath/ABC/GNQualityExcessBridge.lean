/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNValuationExcess
import DkMath.ABC.AdjacentDiagonalBasic
import DkMath.ABC.TailRadicalBasic

#print "file: DkMath.ABC.GNQualityExcessBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# The quality-to-GN-excess interface

This module records the exact deterministic interface needed to turn high ABC
quality into GN valuation excess.  Two estimates are visible in the generic
interface:

* a return lower bound comparing `log GN` with `log c`;
* a support budget comparing `log (rad GN)` with the ABC radical.

The GN return estimate is discharged unconditionally below with coefficient
`n - 1`.  Thus the specialized public bridge leaves only the GN support
budget as a global input.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- The GN kernel returns at least `κ` copies of the logarithmic ABC height. -/
def GNReturnLowerBound (T : Triple) (n : ℕ) (κ : ℝ) : Prop :=
  κ * Real.log (T.c : ℝ) ≤ Real.log ((GN n T.a T.b : ℕ) : ℝ)

/-- The radical support of GN consumes at most `σ` ABC-radical log units. -/
def GNSupportBudget (T : Triple) (n : ℕ) (σ : ℝ) : Prop :=
  Real.log (rad (GN n T.a T.b) : ℝ) ≤
    σ * Real.log (rad (T.a * T.b * T.c) : ℝ)

/-- Affine GN-support budget, allowing an additive finite-exception constant. -/
def GNSupportBudgetAffine
    (T : Triple) (n : ℕ) (σ C : ℝ) : Prop :=
  Real.log (rad (GN n T.a T.b) : ℝ) ≤
    σ * Real.log (rad (T.a * T.b * T.c) : ℝ) + C

/-- The pure support budget is the zero-constant affine budget. -/
theorem GNSupportBudget.toAffine
    {T : Triple} {n : ℕ} {σ : ℝ}
    (h : GNSupportBudget T n σ) :
    GNSupportBudgetAffine T n σ 0 := by
  simpa [GNSupportBudget, GNSupportBudgetAffine] using h

/-- Positive ABC coordinates make the ABC radical logarithm strictly positive. -/
theorem Triple.log_rad_abc_pos
    (T : Triple) (ha : 0 < T.a) (hb : 0 < T.b) :
    0 < Real.log (rad (T.a * T.b * T.c) : ℝ) := by
  have hprod : 2 ≤ T.a * T.b * T.c := by
    have hab : 1 ≤ T.a * T.b := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt hb))
    have hc : 2 ≤ T.c := by
      rw [← T.hsum]
      omega
    nlinarith
  exact log_rad_pos_of_two_le hprod

/-- The natural GN endpoint bound gives the unconditional logarithmic return. -/
theorem Triple.log_c_mul_pred_le_log_GN
    (T : Triple) {n : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) :
    (((n - 1 : ℕ) : ℝ) * Real.log (T.c : ℝ)) ≤
      Real.log ((GN n T.a T.b : ℕ) : ℝ) := by
  have hnat := T.pow_pred_c_le_GN (Nat.one_le_of_lt hn) ha
  have hc : 0 < (T.c : ℝ) := by
    exact_mod_cast (by rw [← T.hsum]; omega : 0 < T.c)
  have hcast :
      ((T.c ^ (n - 1) : ℕ) : ℝ) ≤
        ((GN n T.a T.b : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_pow] at hcast
  have hlog := Real.log_le_log (pow_pos hc _) hcast
  simpa [Nat.cast_pow, Real.log_pow] using hlog

/-- `κ = n-1` discharges the return predicate without a global hypothesis. -/
theorem Triple.gnReturnLowerBound_pred
    (T : Triple) {n : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) :
    GNReturnLowerBound T n ((n - 1 : ℕ) : ℝ) := by
  exact T.log_c_mul_pred_le_log_GN hn ha hb

/-- High quality is exactly a strict lower bound for `log c` when the denominator is positive. -/
theorem log_c_gt_of_quality_gt
    (T : Triple) {Q : ℝ}
    (hrad : 0 < Real.log (rad (T.a * T.b * T.c) : ℝ))
    (hquality : Q < quality T) :
    Q * Real.log (rad (T.a * T.b * T.c) : ℝ) <
      Real.log (T.c : ℝ) := by
  rw [quality] at hquality
  exact (lt_div_iff₀ hrad).mp hquality

/--
The deterministic high-quality-to-excess bridge.

The theorem deliberately exposes the two estimates that a global argument
must establish.  Its conclusion is unconditional once those estimates and
the finite GN identity are available.
-/
theorem Triple.GNValuationExcess_gt_of_quality_gt
    (T : Triple) {n : ℕ} {ε κ σ : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hrad : 0 < Real.log (rad (T.a * T.b * T.c) : ℝ))
    (hκ : 0 < κ)
    (hquality : 1 + ε < quality T)
    (hreturn : GNReturnLowerBound T n κ)
    (hsupport : GNSupportBudget T n σ) :
    (κ * (1 + ε) - σ) *
        Real.log (rad (T.a * T.b * T.c) : ℝ) <
      GNValuationExcess n T.a T.b := by
  have hheight := log_c_gt_of_quality_gt T hrad hquality
  have hscaled :
      κ * ((1 + ε) * Real.log (rad (T.a * T.b * T.c) : ℝ)) <
        κ * Real.log (T.c : ℝ) := by
    exact mul_lt_mul_of_pos_left hheight hκ
  have hidentity := T.log_GN_eq_log_rad_add_GNValuationExcess hn ha hb
  change κ * Real.log (T.c : ℝ) ≤
    Real.log ((GN n T.a T.b : ℕ) : ℝ) at hreturn
  change Real.log (rad (GN n T.a T.b) : ℝ) ≤
    σ * Real.log (rad (T.a * T.b * T.c) : ℝ) at hsupport
  nlinarith

/-- Affine version of the deterministic high-quality-to-excess bridge. -/
theorem Triple.GNValuationExcess_gt_of_quality_gt_affine
    (T : Triple) {n : ℕ} {ε κ σ C : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hκ : 0 < κ)
    (hquality : 1 + ε < quality T)
    (hreturn : GNReturnLowerBound T n κ)
    (hsupport : GNSupportBudgetAffine T n σ C) :
    (κ * (1 + ε) - σ) *
          Real.log (rad (T.a * T.b * T.c) : ℝ) - C <
      GNValuationExcess n T.a T.b := by
  have hrad := T.log_rad_abc_pos ha hb
  have hheight := log_c_gt_of_quality_gt T hrad hquality
  have hscaled :
      κ * ((1 + ε) * Real.log (rad (T.a * T.b * T.c) : ℝ)) <
        κ * Real.log (T.c : ℝ) :=
    mul_lt_mul_of_pos_left hheight hκ
  have hidentity := T.log_GN_eq_log_rad_add_GNValuationExcess hn ha hb
  change κ * Real.log (T.c : ℝ) ≤
    Real.log ((GN n T.a T.b : ℕ) : ℝ) at hreturn
  change Real.log (rad (GN n T.a T.b) : ℝ) ≤
    σ * Real.log (rad (T.a * T.b * T.c) : ℝ) + C at hsupport
  nlinarith

/-- High quality forces GN excess assuming only an affine support budget. -/
theorem Triple.GNValuationExcess_gt_of_quality_gt_pred_affine
    (T : Triple) {n : ℕ} {ε σ C : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hquality : 1 + ε < quality T)
    (hsupport : GNSupportBudgetAffine T n σ C) :
    ((((n - 1 : ℕ) : ℝ) * (1 + ε) - σ) *
          Real.log (rad (T.a * T.b * T.c) : ℝ)) - C <
      GNValuationExcess n T.a T.b := by
  exact T.GNValuationExcess_gt_of_quality_gt_affine hn ha hb
    (by exact_mod_cast (show 0 < n - 1 by omega))
    hquality (T.gnReturnLowerBound_pred hn ha hb) hsupport

/-- Pure-budget specialization of the unconditional GN return bridge. -/
theorem Triple.GNValuationExcess_gt_of_quality_gt_pred
    (T : Triple) {n : ℕ} {ε σ : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hquality : 1 + ε < quality T)
    (hsupport : GNSupportBudget T n σ) :
    (((n - 1 : ℕ) : ℝ) * (1 + ε) - σ) *
        Real.log (rad (T.a * T.b * T.c) : ℝ) <
      GNValuationExcess n T.a T.b := by
  simpa using T.GNValuationExcess_gt_of_quality_gt_pred_affine
    hn ha hb hquality hsupport.toAffine

end DkMath.ABC
