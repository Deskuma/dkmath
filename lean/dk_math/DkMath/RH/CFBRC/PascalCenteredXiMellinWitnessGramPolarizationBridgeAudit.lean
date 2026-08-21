/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit
import Mathlib.Tactic

/-!
# GWSS-003E: Gram/polarization bridge decision audit

The existing source-side quadraticization has vertical and whole-surface
polarization identities for the fixed `τ = 0` box feature.  This module keeps
the only small algebraic facts needed for the bridge decision: a fixed
reference produces a term linear in a real scalar, while nonnegativity of the
two shifted energies does not determine their order.

The module deliberately does not identify the fixed `τ = 0` source feature
with a target-dependent synthesized Mellin witness.  That missing interface is
the load-bearing result of GWSS-003E.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-! ## GWSS-003E-2: fixed-reference polarization -/

/-- A conjugation-real feature retains a term linear in a real scalar after
fixed-reference polarization.  This is different from bare norm-square
scaling, but it is only an algebraic identity and supplies no energy order. -/
theorem normSq_shifted_difference_real_scale
    (q : ℝ) {F : ℂ} (hF : F = starRingEnd ℂ F) :
    (Complex.normSq (((q : ℂ) * F) + 1) : ℂ) -
        (Complex.normSq (((q : ℂ) * F) - 1) : ℂ) =
      (4 : ℂ) * (q : ℂ) * F := by
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self,
    map_add, map_sub, map_one, map_mul, ← hF]
  have hq : starRingEnd ℂ (q : ℂ) = (q : ℂ) := by
    simp
  rw [hq]
  ring

/-! ## GWSS-003E-4: positivity-only order no-go -/

/-- The two shifted norm squares are nonnegative in both examples, while the
opposite energy orderings occur for the real features `1` and `-1`.  Hence
positivity alone is not shifted-energy dominance. -/
theorem shifted_energy_nonneg_does_not_determine_order :
    Complex.normSq (((1 : ℂ) - 1)) ≤ Complex.normSq (((1 : ℂ) + 1)) ∧
      Complex.normSq (((-1 : ℂ) + 1)) ≤ Complex.normSq (((-1 : ℂ) - 1)) := by
  norm_num [Complex.normSq]

end DkMath.RH.CFBRCProjection
