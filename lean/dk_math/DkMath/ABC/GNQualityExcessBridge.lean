/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNValuationExcess
import DkMath.ABC.AdjacentDiagonalBasic

#print "file: DkMath.ABC.GNQualityExcessBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# The quality-to-GN-excess interface

This module records the exact deterministic interface needed to turn high ABC
quality into GN valuation excess.  Two estimates remain visible:

* a return lower bound comparing `log GN` with `log c`;
* a support budget comparing `log (rad GN)` with the ABC radical.

Neither estimate is asserted globally here.  Once supplied, the finite
factorization identity forces the claimed excess.
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

end DkMath.ABC
