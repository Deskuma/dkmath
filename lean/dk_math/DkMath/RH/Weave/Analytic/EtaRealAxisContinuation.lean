/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairedContinuation
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaRealAxisContinuation"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology

/-- A canonical sequence approaching the open critical real interval from above. -/
noncomputable def etaRealAxisUpperApproach
    (σ : ℝ) (n : ℕ) : ℂ :=
  (σ : ℂ) +
    (((1 : ℝ) / (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I

@[simp] theorem etaRealAxisUpperApproach_re
    (σ : ℝ) (n : ℕ) :
    (etaRealAxisUpperApproach σ n).re = σ := by
  simp [etaRealAxisUpperApproach]

@[simp] theorem etaRealAxisUpperApproach_im
    (σ : ℝ) (n : ℕ) :
    (etaRealAxisUpperApproach σ n).im =
      (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) := by
  simp [etaRealAxisUpperApproach]

/-- The canonical upper approach converges to the corresponding real point. -/
theorem etaRealAxisUpperApproach_tendsto
    (σ : ℝ) :
    Tendsto (etaRealAxisUpperApproach σ) atTop (nhds (σ : ℂ)) := by
  have hsmall :
      Tendsto
        (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    have h :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        tendsto_nat_succ_atTop
    simpa [Function.comp_def] using h
  have hcast :
      Tendsto
        (fun n : ℕ =>
          (((1 : ℝ) / (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ))
        atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hsmall
    simpa [Function.comp_def] using h
  have himag :
      Tendsto
        (fun n : ℕ =>
          (((1 : ℝ) / (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)
        atTop (nhds 0) := by
    simpa using hcast.mul_const Complex.I
  have hadd :=
    (show Tendsto (fun _ : ℕ => (σ : ℂ)) atTop (nhds (σ : ℂ)) from
      tendsto_const_nhds).add himag
  simpa [etaRealAxisUpperApproach] using hadd

/-- Every point of the canonical upper approach remains in the right half-plane. -/
theorem etaRealAxisUpperApproach_pos_re
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    0 < (etaRealAxisUpperApproach σ n).re := by
  simpa using hσ

/-- Every point of the canonical upper approach is nonreal. -/
theorem etaRealAxisUpperApproach_im_ne_zero
    (σ : ℝ) (n : ℕ) :
    (etaRealAxisUpperApproach σ n).im ≠ 0 := by
  have hden : 0 < (((n + 1 : ℕ) : ℝ)) := by
    positivity
  have hdiv : (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ≠ 0 :=
    div_ne_zero one_ne_zero hden.ne'
  simpa using hdiv

/-- The raw analytic eta product is differentiable at every real point in `(0,1)`. -/
theorem analyticEta_differentiableAt_of_real_mem_Ioo_zero_one
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    DifferentiableAt ℂ analyticEta (σ : ℂ) := by
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  unfold analyticEta
  have hfactor :
      DifferentiableAt ℂ
        (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z))
        (σ : ℂ) := by
    fun_prop
  exact hfactor.mul (differentiableAt_riemannZeta hs1)

/--
The paired eta infinite sum agrees with analytic eta on the open critical real
interval.  The proof approaches the real point from the upper-right half-plane,
where the identification is already Green, and uses uniqueness of limits.
-/
theorem etaPairedValue_eq_analyticEta_of_real_mem_Ioo_zero_one
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    etaPairedValue (σ : ℂ) = analyticEta (σ : ℂ) := by
  have hmem : (σ : ℂ) ∈ etaRightHalfPlane := by
    simpa [etaRightHalfPlane] using hσ0
  have hpairedAt : DifferentiableAt ℂ etaPairedValue (σ : ℂ) :=
    (etaPairedValue_differentiableOn_rightHalfPlane
      (σ : ℂ) hmem).differentiableAt
        (isOpen_etaRightHalfPlane.mem_nhds hmem)
  have hanalyticAt : DifferentiableAt ℂ analyticEta (σ : ℂ) :=
    analyticEta_differentiableAt_of_real_mem_Ioo_zero_one hσ0 hσ1
  have hseq := etaRealAxisUpperApproach_tendsto σ
  have hpaired :
      Tendsto
        (fun n : ℕ => etaPairedValue (etaRealAxisUpperApproach σ n))
        atTop (nhds (etaPairedValue (σ : ℂ))) :=
    hpairedAt.continuousAt.tendsto.comp hseq
  have hanalytic :
      Tendsto
        (fun n : ℕ => analyticEta (etaRealAxisUpperApproach σ n))
        atTop (nhds (analyticEta (σ : ℂ))) :=
    hanalyticAt.continuousAt.tendsto.comp hseq
  have heq :
      ∀ n : ℕ,
        etaPairedValue (etaRealAxisUpperApproach σ n) =
          analyticEta (etaRealAxisUpperApproach σ n) := by
    intro n
    exact etaPairedValue_eq_analyticEta_of_pos_re_of_im_ne_zero
      (etaRealAxisUpperApproach_pos_re hσ0 n)
      (etaRealAxisUpperApproach_im_ne_zero σ n)
  have hanalytic' :
      Tendsto
        (fun n : ℕ => etaPairedValue (etaRealAxisUpperApproach σ n))
        atTop (nhds (analyticEta (σ : ℂ))) := by
    refine hanalytic.congr' (Eventually.of_forall fun n => ?_)
    exact (heq n).symm
  exact tendsto_nhds_unique hpaired hanalytic'

#print axioms etaPairedValue_eq_analyticEta_of_real_mem_Ioo_zero_one

end DkMath.RH.Weave.Analytic
