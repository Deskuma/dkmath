/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.ZeroLocusFactorBridge
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CompletedZetaBridge"

namespace DkMath.RH.CFBRCProjection

/-- A standard nontrivial Riemann-zeta zero cannot be `s = 0`. -/
theorem nontrivialRiemannZetaZero_ne_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    s ≠ 0 := by
  intro hs0
  subst s
  have hz := hs.1
  rw [riemannZeta_zero] at hz
  norm_num at hz

/-- Deligne's real Gamma factor is nonzero at every standard nontrivial zeta zero. -/
theorem gammaR_ne_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Complex.Gammaℝ s ≠ 0 := by
  rw [Ne, Complex.Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  rcases n with _ | n
  · apply nontrivialRiemannZetaZero_ne_zero hs
    simpa using hn
  · apply hs.2.1
    refine ⟨n, ?_⟩
    simpa [Nat.succ_eq_add_one] using hn

/--
Away from `s = 0` and zeros of `Gammaℝ`, standard and completed Riemann zeta
have exactly the same zero condition.
-/
theorem riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero
    {s : ℂ} (hs0 : s ≠ 0) (hGamma : Complex.Gammaℝ s ≠ 0) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0 := by
  rw [riemannZeta_def_of_ne_zero hs0]
  simp [hGamma]

/-- Every standard nontrivial zeta zero is a completed-zeta zero. -/
theorem completedRiemannZeta_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    completedRiemannZeta s = 0 := by
  exact
    (riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero
      (nontrivialRiemannZetaZero_ne_zero hs)
      (gammaR_ne_zero_of_nontrivialRiemannZetaZero hs)).mp hs.1

/-- The completed-zeta functional equation preserves the zero condition. -/
theorem completedRiemannZeta_one_sub_eq_zero_iff (s : ℂ) :
    completedRiemannZeta (1 - s) = 0 ↔
      completedRiemannZeta s = 0 := by
  rw [completedRiemannZeta_one_sub]

/-- A nontrivial standard zeta zero produces its completed-zeta reflected zero. -/
theorem completedRiemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    completedRiemannZeta (1 - s) = 0 := by
  rw [completedRiemannZeta_one_sub]
  exact completedRiemannZeta_eq_zero_of_nontrivialRiemannZetaZero hs

end DkMath.RH.CFBRCProjection
