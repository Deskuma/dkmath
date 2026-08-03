/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPoleAudit
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaContinuationDomains"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open Set

/-- A convex combination of two positive real numbers remains positive. -/
private theorem positive_convexCombination
    {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : 0 < x) (hy : 0 < y) :
    0 < a * x + b * y := by
  rcases ha.eq_or_lt with rfl | ha_pos
  · have hb_one : b = 1 := by linarith
    simpa [hb_one] using hy
  · have hax : 0 < a * x := mul_pos ha_pos hx
    have hby : 0 ≤ b * y := mul_nonneg hb hy.le
    linarith

/-- A convex combination of two negative real numbers remains negative. -/
private theorem convexCombination_neg
    {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : x < 0) (hy : y < 0) :
    a * x + b * y < 0 := by
  rcases ha.eq_or_lt with rfl | ha_pos
  · have hb_one : b = 1 := by linarith
    simpa [hb_one] using hy
  · have hax : a * x < 0 := mul_neg_of_pos_of_neg ha_pos hx
    have hby : b * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy.le
    linarith

/-- The nonreal upper part of the open right half-plane. -/
def etaUpperRightHalfPlane : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ 0 < s.im}

/-- The nonreal lower part of the open right half-plane. -/
def etaLowerRightHalfPlane : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.im < 0}

/-- The upper-right continuation domain is open. -/
theorem isOpen_etaUpperRightHalfPlane :
    IsOpen etaUpperRightHalfPlane := by
  exact
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)

/-- The lower-right continuation domain is open. -/
theorem isOpen_etaLowerRightHalfPlane :
    IsOpen etaLowerRightHalfPlane := by
  exact
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)

/-- The upper-right continuation domain is convex. -/
theorem convex_etaUpperRightHalfPlane :
    Convex ℝ etaUpperRightHalfPlane := by
  intro x hx y hy a b ha hb hab
  change 0 < x.re ∧ 0 < x.im at hx
  change 0 < y.re ∧ 0 < y.im at hy
  change 0 < (a • x + b • y).re ∧ 0 < (a • x + b • y).im
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  exact ⟨
    positive_convexCombination ha hb hab hx.1 hy.1,
    positive_convexCombination ha hb hab hx.2 hy.2⟩

/-- The lower-right continuation domain is convex. -/
theorem convex_etaLowerRightHalfPlane :
    Convex ℝ etaLowerRightHalfPlane := by
  intro x hx y hy a b ha hb hab
  change 0 < x.re ∧ x.im < 0 at hx
  change 0 < y.re ∧ y.im < 0 at hy
  change 0 < (a • x + b • y).re ∧ (a • x + b • y).im < 0
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  exact ⟨
    positive_convexCombination ha hb hab hx.1 hy.1,
    convexCombination_neg ha hb hab hx.2 hy.2⟩

/-- The upper-right continuation domain is preconnected. -/
theorem isPreconnected_etaUpperRightHalfPlane :
    IsPreconnected etaUpperRightHalfPlane :=
  convex_etaUpperRightHalfPlane.isPreconnected

/-- The lower-right continuation domain is preconnected. -/
theorem isPreconnected_etaLowerRightHalfPlane :
    IsPreconnected etaLowerRightHalfPlane :=
  convex_etaLowerRightHalfPlane.isPreconnected

/-- The paired eta value is holomorphic on the upper-right domain. -/
theorem etaPairedValue_differentiableOn_upperRightHalfPlane :
    DifferentiableOn ℂ etaPairedValue etaUpperRightHalfPlane := by
  exact etaPairedValue_differentiableOn_rightHalfPlane.mono fun s hs => hs.1

/-- The paired eta value is holomorphic on the lower-right domain. -/
theorem etaPairedValue_differentiableOn_lowerRightHalfPlane :
    DifferentiableOn ℂ etaPairedValue etaLowerRightHalfPlane := by
  exact etaPairedValue_differentiableOn_rightHalfPlane.mono fun s hs => hs.1

/-- The raw zeta-product eta value is holomorphic on the upper-right domain. -/
theorem analyticEta_differentiableOn_upperRightHalfPlane :
    DifferentiableOn ℂ analyticEta etaUpperRightHalfPlane := by
  intro s hs
  change 0 < s.re ∧ 0 < s.im at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  unfold analyticEta
  have hfactor :
      DifferentiableAt ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) s := by
    fun_prop
  exact (hfactor.mul (differentiableAt_riemannZeta hs1)).differentiableWithinAt

/-- The raw zeta-product eta value is holomorphic on the lower-right domain. -/
theorem analyticEta_differentiableOn_lowerRightHalfPlane :
    DifferentiableOn ℂ analyticEta etaLowerRightHalfPlane := by
  intro s hs
  change 0 < s.re ∧ s.im < 0 at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  unfold analyticEta
  have hfactor :
      DifferentiableAt ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) s := by
    fun_prop
  exact (hfactor.mul (differentiableAt_riemannZeta hs1)).differentiableWithinAt

end DkMath.RH.Weave.Analytic
