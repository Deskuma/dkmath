/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkLimit
import DkMath.Analysis.DkReal.SemanticCF2DLogComposition

#print "file: DkMath.Analysis.DkReal.SemanticCF2DLogLimit"

/-!
# Limit layer for finite dyadic logarithmic phase estimates

`SemanticCF2DLogComposition` proves finite identities and finite bounds. This
module is the first limit layer over those finite facts.

The limit statements are intentionally thin. They use Mathlib filters through
the DkMath `DkTendstoAtTop` vocabulary and only prove that the finite
quadratic control tends to `1 / 3`. No statement is made here that the
centered log-depth observable itself converges to `1 / 3`; that would require
a matching lower estimate.
-/

namespace DkMath.Analysis.DkNNRealQ

/--
The closed finite quadratic bound tends to `1 / 3`.

Since `dyadicPhaseDenom n = 2^n`, the correction term is a constant multiple
of `(1 / 4)^n`, hence vanishes at refinement depth infinity.
-/
theorem dkTendsto_dyadicPhaseClosedQuadraticBound_one_third :
    DkMath.Analysis.DkTendstoAtTop
      (fun n : ℕ =>
        1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2))
      (1 / 3 : ℝ) := by
  have hpow :
      Filter.Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaled :
      Filter.Tendsto (fun n : ℕ => (2 / 3 : ℝ) * (1 / 4 : ℝ) ^ n)
        Filter.atTop (nhds 0) := by
    simpa using hpow.const_mul (2 / 3 : ℝ)
  have hsum :
      Filter.Tendsto
        (fun n : ℕ => (1 / 3 : ℝ) + (2 / 3 : ℝ) * (1 / 4 : ℝ) ^ n)
        Filter.atTop (nhds ((1 / 3 : ℝ) + 0)) :=
    tendsto_const_nhds.add hscaled
  convert hsum using 1
  · funext n
    have h2n : ((2 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
    have h4n : ((4 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
    simp [dyadicPhaseDenom]
    field_simp [h2n, h4n]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul,
      Nat.mul_comm]
  · norm_num

/-- Mathlib `Tendsto` spelling of the DkMath closed-bound convergence theorem. -/
theorem tendsto_dyadicPhaseClosedQuadraticBound_one_third :
    Filter.Tendsto
      (fun n : ℕ =>
        1 / 3 + 2 / (3 * (dyadicPhaseDenom n : ℝ) ^ 2))
      Filter.atTop
      (nhds (1 / 3 : ℝ)) :=
  dkTendsto_dyadicPhaseClosedQuadraticBound_one_third

/--
The trapezoidal centered quadratic moment tends to `1 / 3`.

This is only the quadratic control moment. It does not identify the limit of
the centered log-depth sum.
-/
theorem dkTendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
    DkMath.Analysis.DkTendstoAtTop
      dyadicPhaseTrapezoidCenteredQuadraticSum
      (1 / 3 : ℝ) := by
  refine Filter.Tendsto.congr' ?_ tendsto_dyadicPhaseClosedQuadraticBound_one_third
  exact Filter.Eventually.of_forall fun n =>
    (dyadicPhaseTrapezoidCenteredQuadraticSum_eq n).symm

/--
Mathlib `Tendsto` spelling of the trapezoidal centered quadratic moment
convergence theorem.
-/
theorem tendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third :
    Filter.Tendsto
      dyadicPhaseTrapezoidCenteredQuadraticSum
      Filter.atTop
      (nhds (1 / 3 : ℝ)) :=
  dkTendsto_dyadicPhaseTrapezoidCenteredQuadraticSum_one_third

end DkMath.Analysis.DkNNRealQ
