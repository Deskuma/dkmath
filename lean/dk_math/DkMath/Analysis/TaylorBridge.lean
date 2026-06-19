/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.GapGN
import DkMath.CosmicFormula.CosmicDerivativePowerLimit

#print "file: DkMath.Analysis.TaylorBridge"

/-!
# Taylor and derivative bridge for `gapGN`

The exact kernel `gapGN` contains the complete finite power increment. At zero
increment its value is the first-order coefficient of the power map.

This file does not define `gapGN` by differentiation. Instead, it connects the
exact algebraic kernel to Mathlib's derivative API after the algebraic
factorization has already been established.

The local `noncomputable` definition below belongs to the semantic real-analysis
route. It does not affect the computability of rational interval operations,
`DkReal`, or `DkNNRealQ`.
-/

namespace DkMath.Analysis

/--
At zero increment, `gapGN` is the formal derivative coefficient of a natural
power.
-/
theorem gapGN_zero
    {R : Type*} [CommSemiring R] (d : ℕ) (base : R) :
    gapGN d base 0 = (d : R) * base ^ (d - 1) := by
  simpa [gapGN, DkMath.CosmicFormulaBinom.GN] using
    (DkMath.CosmicFormula.GN_zero_eval (R := R) d base)

/--
Successor form of the zero-increment theorem, avoiding truncated subtraction in
the exponent.
-/
theorem gapGN_succ_zero
    {R : Type*} [CommSemiring R] (d : ℕ) (base : R) :
    gapGN (d + 1) base 0 = ((d + 1 : ℕ) : R) * base ^ d := by
  simpa using (gapGN_zero (R := R) (d + 1) base)

/-- Difference quotient of the natural power map at `base` with increment `delta`. -/
noncomputable def powerDifferenceQuotient (d : ℕ) (base delta : ℝ) : ℝ :=
  ((base + delta) ^ d - base ^ d) / delta

/-- Away from zero increment, the power difference quotient is exactly `gapGN`. -/
theorem powerDifferenceQuotient_eq_gapGN_of_ne_zero
    (d : ℕ) (base delta : ℝ) (hdelta : delta ≠ 0) :
    powerDifferenceQuotient d base delta = gapGN d base delta := by
  rw [powerDifferenceQuotient, pow_add_sub_pow_eq_delta_mul_gapGN]
  exact mul_div_cancel_left₀ (gapGN d base delta) hdelta

/--
Over the reals, the analysis-facing `gapGN` is the existing cosmic
`powerKernel`.
-/
theorem real_gapGN_eq_powerKernel (d : ℕ) (base delta : ℝ) :
    gapGN d base delta = DkMath.CosmicFormula.powerKernel d base delta := by
  exact (DkMath.CosmicFormula.powerKernel_eq_GN_swap d base delta).symm

/-- The exact real gap kernel is continuous in the increment variable. -/
theorem continuous_gapGN (d : ℕ) (base : ℝ) :
    Continuous (fun delta : ℝ => gapGN d base delta) := by
  simpa only [real_gapGN_eq_powerKernel] using
    DkMath.CosmicFormula.continuous_powerKernel d base

/--
As the increment tends to zero, `gapGN` tends to the derivative coefficient of
the natural power map.
-/
theorem tendsto_gapGN_zero (d : ℕ) (base : ℝ) :
    Filter.Tendsto (fun delta : ℝ => gapGN d base delta)
      (nhds (0 : ℝ))
      (nhds ((d : ℝ) * base ^ (d - 1))) := by
  simpa only [real_gapGN_eq_powerKernel] using
    DkMath.CosmicFormula.tendsto_powerKernel_zero d base

/--
The punctured power difference quotient tends to the same value as the full
exact gap kernel.
-/
theorem tendsto_powerDifferenceQuotient_zero
    (d : ℕ) (base : ℝ) :
    Filter.Tendsto (fun delta : ℝ => powerDifferenceQuotient d base delta)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds ((d : ℝ) * base ^ (d - 1))) := by
  have hgap :
      Filter.Tendsto (fun delta : ℝ => gapGN d base delta)
        (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
        (nhds ((d : ℝ) * base ^ (d - 1))) :=
    (tendsto_gapGN_zero d base).mono_left
      nhdsWithin_le_nhds
  refine Filter.Tendsto.congr' ?_ hgap
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  have hdelta_ne : delta ≠ 0 := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hdelta
  exact (powerDifferenceQuotient_eq_gapGN_of_ne_zero d base delta hdelta_ne).symm

/--
Derivative theorem obtained directly from the `gapGN` difference-quotient
limit.

Unlike `hasDerivAt_pow_via_gapGN`, this proof does not delegate to an existing
power derivative theorem. It feeds `tendsto_powerDifferenceQuotient_zero`
directly into the general punctured difference-kernel criterion.
-/
theorem hasDerivAt_pow_from_gapGN_limit (d : ℕ) (base : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ d) ((d : ℝ) * base ^ (d - 1)) base := by
  apply DkMath.CosmicFormula.hasDerivAt_of_tendsto_cosmicKernel
  simpa [DkMath.CosmicFormula.cosmicKernel, DkMath.CosmicFormula.delta,
    powerDifferenceQuotient] using
    (tendsto_powerDifferenceQuotient_zero d base)

/--
Canonical public derivative theorem for powers through the Analysis `gapGN`
flow.
-/
theorem hasDerivAt_pow_via_gapGN (d : ℕ) (base : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ d) ((d : ℝ) * base ^ (d - 1)) base :=
  hasDerivAt_pow_from_gapGN_limit d base

end DkMath.Analysis
