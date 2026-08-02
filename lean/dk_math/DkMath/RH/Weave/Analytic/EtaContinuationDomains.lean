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
  simp only [map_add, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    Complex.mul_re, Complex.mul_im, sub_zero, add_zero]
  constructor
  · nlinarith
  · nlinarith

/-- The lower-right continuation domain is convex. -/
theorem convex_etaLowerRightHalfPlane :
    Convex ℝ etaLowerRightHalfPlane := by
  intro x hx y hy a b ha hb hab
  change 0 < x.re ∧ x.im < 0 at hx
  change 0 < y.re ∧ y.im < 0 at hy
  change 0 < (a • x + b • y).re ∧ (a • x + b • y).im < 0
  simp only [map_add, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    Complex.mul_re, Complex.mul_im, sub_zero, add_zero]
  constructor
  · nlinarith
  · nlinarith

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
