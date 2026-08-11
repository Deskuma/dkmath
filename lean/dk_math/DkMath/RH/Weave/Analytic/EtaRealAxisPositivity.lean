/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaRealAxisContinuation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaRealAxisPositivity"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open DkMath.RH.CFBRCProjection

/-- A real eta vector is the complex embedding of the corresponding real power. -/
theorem etaUnsignedVector_real_eq_ofReal
    (σ : ℝ) (m : ℕ) :
    etaUnsignedVector (σ : ℂ) m =
      (((((m + 1 : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ) := by
  unfold etaUnsignedVector
  have hbase : 0 ≤ (((m + 1 : ℕ) : ℝ)) := by
    positivity
  simpa using
    (Complex.ofReal_cpow hbase (-σ)).symm

/-- A real eta pair is the complex embedding of a difference of real powers. -/
theorem etaPairTerm_real_eq_ofReal
    (σ : ℝ) (k : ℕ) :
    etaPairTerm (σ : ℂ) k =
      (((((2 * k + 1 : ℕ) : ℝ)) ^ (-σ) -
        (((2 * k + 2 : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ) := by
  unfold etaPairTerm
  rw [etaUnsignedVector_real_eq_ofReal,
    etaUnsignedVector_real_eq_ofReal]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring_nf

/-- Every real eta pair has strictly positive real part for a positive exponent. -/
theorem etaPairTerm_re_pos_of_pos_real
    {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    0 < (etaPairTerm (σ : ℂ) k).re := by
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * k + 2 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hab : a < b := by
    dsimp [a, b]
    exact_mod_cast (by omega : 2 * k + 1 < 2 * k + 2)
  have hexp : -σ < 0 := by
    linarith
  have hpow : b ^ (-σ) < a ^ (-σ) :=
    Real.strictAntiOn_rpow_Ioi_of_exponent_neg hexp ha hb hab
  rw [etaPairTerm_real_eq_ofReal]
  simp only [Complex.ofReal_re]
  dsimp [a, b] at hpow
  linarith

/-- Every real eta pair lies on the real axis. -/
theorem etaPairTerm_im_eq_zero_real
    (σ : ℝ) (k : ℕ) :
    (etaPairTerm (σ : ℂ) k).im = 0 := by
  rw [etaPairTerm_real_eq_ofReal]
  simp

/-- The real parts of the paired eta series are summable on `σ > 0`. -/
theorem summable_etaPairTerm_re_of_pos_real
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun k : ℕ => (etaPairTerm (σ : ℂ) k).re) := by
  have hsum : Summable (etaPairTerm (σ : ℂ)) := by
    exact etaPairedSummableAt_of_pos_re (s := (σ : ℂ)) (by simpa using hσ)
  exact
    (hsum.hasSum.map Complex.reCLM Complex.reCLM.continuous).summable

/-- The real part of paired eta is the tsum of the real parts of its pairs. -/
theorem etaPairedValue_re_eq_tsum_re
    {σ : ℝ} (hσ : 0 < σ) :
    (etaPairedValue (σ : ℂ)).re =
      ∑' k : ℕ, (etaPairTerm (σ : ℂ) k).re := by
  have hsum : Summable (etaPairTerm (σ : ℂ)) := by
    exact etaPairedSummableAt_of_pos_re (s := (σ : ℂ)) (by simpa using hσ)
  have hmap :=
    (hsum.hasSum.map Complex.reCLM Complex.reCLM.continuous).tsum_eq
  simpa [etaPairedValue] using hmap.symm

/-- The genuine paired eta value has positive real part on the positive real axis. -/
theorem etaPairedValue_re_pos_of_pos_real
    {σ : ℝ} (hσ : 0 < σ) :
    0 < (etaPairedValue (σ : ℂ)).re := by
  have hsumRe := summable_etaPairTerm_re_of_pos_real hσ
  have hfirst : 0 < (etaPairTerm (σ : ℂ) 0).re :=
    etaPairTerm_re_pos_of_pos_real hσ 0
  have hle :
      (etaPairTerm (σ : ℂ) 0).re ≤
        ∑' k : ℕ, (etaPairTerm (σ : ℂ) k).re := by
    exact hsumRe.le_tsum 0
      (fun k _ => (etaPairTerm_re_pos_of_pos_real hσ k).le)
  rw [etaPairedValue_re_eq_tsum_re hσ]
  exact hfirst.trans_le hle

/-- Analytic eta is nonzero on the open critical real interval. -/
theorem analyticEta_ne_zero_of_real_mem_Ioo_zero_one
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    analyticEta (σ : ℂ) ≠ 0 := by
  intro heta
  have heq :=
    etaPairedValue_eq_analyticEta_of_real_mem_Ioo_zero_one hσ0 hσ1
  have hpaired : etaPairedValue (σ : ℂ) = 0 := heq.trans heta
  have hpos := etaPairedValue_re_pos_of_pos_real hσ0
  rw [hpaired] at hpos
  norm_num at hpos

/-- The Riemann zeta function has no zero on the open critical real interval. -/
theorem riemannZeta_ne_zero_of_real_mem_openCriticalInterval
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro hz
  exact analyticEta_ne_zero_of_real_mem_Ioo_zero_one hσ0 hσ1
    (analyticEta_eq_zero_of_riemannZeta_eq_zero hz)

#print axioms riemannZeta_ne_zero_of_real_mem_openCriticalInterval

end DkMath.RH.Weave.Analytic
