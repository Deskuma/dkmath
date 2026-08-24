/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit
import Mathlib.Tactic

/-!
# GWSS-003D: surviving-provider decision audit

This module contains only small certificates needed to compare the three
provider classes left after GWSS-003C.  A fixed nonzero endpoint cannot also
be the limit of the same net at zero; a conjugate two-orbit imaginary detector
cancels when the two masses are equal; and a quadratic norm observable scales
by the square of the scalar norm.

These facts do not manufacture a vanishing-scale theorem, a real-structure
bridge for the actual zero carrier, or a positivity bridge to the current
target-dependent Mellin witness.  The associated provider decision is kept in
the accompanying audit report.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped ComplexConjugate Topology

/-! ## GWSS-003D-A: independent vanishing-scale certificate -/

/-- A nonzero fixed endpoint cannot be both the limit of a net and a zero
limit along the same nontrivial filter.  This is the minimal contradiction
shape required by an independent vanishing-scale provider. -/
theorem false_of_tendsto_zero_and_tendsto_fixed_nonzero
    {ι : Type*} {l : Filter ι} [NeBot l]
  {f : ι → ℂ} {a : ℂ} (ha : a ≠ 0)
    (hzero : Tendsto f l (𝓝 0))
    (hfixed : Tendsto f l (𝓝 a)) :
    False := by
  exact ha (tendsto_nhds_unique hfixed hzero)

/-! ## GWSS-003D-B: finite conjugation model -/

/-- Squaring commutes with complex conjugation. -/
theorem complex_sq_conj_eq_conj_sq (q : ℂ) :
    (starRingEnd ℂ q) ^ 2 = starRingEnd ℂ (q ^ 2) := by
  simp only [map_pow]

/-- In a two-orbit model with equal masses, the imaginary detector cancels
between `q` and its conjugate.  This is an abstract compatibility certificate;
it does not assert that the current finite zero carrier has the required
conjugate-pair API. -/
theorem conjugation_pair_imaginary_detector_cancel (q m : ℂ) :
    ((q.im : ℂ) * m) +
        (((starRingEnd ℂ q).im : ℂ) * m) = 0 := by
  change (q.im : ℂ) * m + ((-q.im : ℝ) : ℂ) * m = 0
  simp only [Complex.ofReal_neg]
  ring

/-! ## GWSS-003D-C: quadratic scaling certificate -/

/-- A norm-square observable is genuinely nonlinear, but its bare scaling is
still homogeneous of degree two.  Positivity alone therefore does not give an
asymmetric comparison with the current scalar-rescaled detector. -/
theorem complex_normSq_mul_eq_normSq_mul_normSq (a w : ℂ) :
    Complex.normSq (a * w) = Complex.normSq a * Complex.normSq w := by
  exact Complex.normSq_mul a w

end DkMath.RH.CFBRCProjection
