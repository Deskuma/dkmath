/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairDerivative
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaPairIntegral"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open DkMath.RH.CFBRCProjection
open MeasureTheory

/--
The positive-orientation derivative kernel for one eta pair.
It is the derivative of `x ↦ -x⁻ˢ` on the positive real axis.
-/
def etaPairIntegralKernel (s : ℂ) (x : ℝ) : ℂ :=
  s * (x : ℂ) ^ (-s - 1)

/-- The negative eta real kernel has derivative `etaPairIntegralKernel`. -/
theorem hasDerivAt_neg_etaRealKernel
    {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -etaRealKernel s y)
      (etaPairIntegralKernel s x) x := by
  convert
    (hasDerivAt_ofReal_cpow_const
      (x := x) hx.ne' (r := -s) (neg_ne_zero.mpr hs)).neg using 1 <;>
    simp [etaRealKernel, etaPairIntegralKernel]

/-- The eta pair integral kernel is integrable on every positive interval. -/
theorem etaPairIntegralKernel_intervalIntegrable
    (s : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (etaPairIntegralKernel s) volume a b := by
  have hzero : 0 ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h0
    exact (not_lt_of_ge h0.1) ha
  have hpow :
      IntervalIntegrable
        (fun x : ℝ => (x : ℂ) ^ (-s - 1)) volume a b :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hzero)
  change
    IntervalIntegrable
      (fun x : ℝ => s * (x : ℂ) ^ (-s - 1)) volume a b
  exact hpow.const_mul s

/--
Exact integral representation of one natural eta pair:

`(2k+1)⁻ˢ - (2k+2)⁻ˢ = ∫ s x⁻ˢ⁻¹ dx` on `[2k+1, 2k+2]`.

Unlike the mean-value norm estimate, this identity keeps the complete complex
phase information inside the integral.
-/
theorem etaPairTerm_eq_intervalIntegral
    {s : ℂ} (hs : s ≠ 0) (k : ℕ) :
    etaPairTerm s k =
      ∫ x : ℝ in (((2 * k + 1 : ℕ) : ℝ))..
          (((2 * k + 2 : ℕ) : ℝ)),
        etaPairIntegralKernel s x := by
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * k + 2 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)
  have hcont :
      ContinuousOn (fun x : ℝ => -etaRealKernel s x) (Set.Icc a b) := by
    intro x hx
    exact
      (hasDerivAt_neg_etaRealKernel hs (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.Ioo a b,
        HasDerivAt (fun y : ℝ => -etaRealKernel s y)
          (etaPairIntegralKernel s x) x := by
    intro x hx
    exact hasDerivAt_neg_etaRealKernel hs (ha.trans hx.1)
  have hint :
      IntervalIntegrable (etaPairIntegralKernel s) volume a b :=
    etaPairIntegralKernel_intervalIntegrable s ha hab
  have hFTC :
      (∫ x : ℝ in a..b, etaPairIntegralKernel s x) =
        (-etaRealKernel s b) - (-etaRealKernel s a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hab hcont hderiv hint
  have hA : etaRealKernel s a = etaUnsignedVector s (2 * k) := by
    dsimp [a]
    simpa using etaRealKernel_nat s (2 * k)
  have hB : etaRealKernel s b = etaUnsignedVector s (2 * k + 1) := by
    dsimp [b]
    simpa [Nat.add_assoc] using etaRealKernel_nat s (2 * k + 1)
  change etaUnsignedVector s (2 * k) - etaUnsignedVector s (2 * k + 1) = _
  change etaUnsignedVector s (2 * k) - etaUnsignedVector s (2 * k + 1) =
    ∫ x : ℝ in a..b, etaPairIntegralKernel s x
  rw [hFTC, hA, hB]
  ring

end DkMath.RH.Weave.Analytic
