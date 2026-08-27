/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedConstantAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelCorrectionTailBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Leading projection constant carried by the critical-mirror correction term. -/
noncomputable def etaCriticalMirrorCorrectionMirrorProjectionConstant
    (s : ℂ) : ℝ :=
  |s.im| *
    ((4 * |s.im| / (criticalMirror s).re) *
      (‖criticalMirror s‖ / (criticalMirror s).re))

/-- Leading projection constant carried by the original-point correction term. -/
noncomputable def etaCriticalMirrorCorrectionOriginalProjectionConstant
    (s : ℂ) : ℝ :=
  |s.im| *
    ((4 * |s.im| / s.re) *
      (‖s‖ / s.re))

/--
The named correction projection bound is exactly the sum of its mirror and
original power terms.
-/
theorem etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound_eq_constants
    (s : ℂ) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K =
      etaCriticalMirrorCorrectionMirrorProjectionConstant s *
          ((K : ℝ) ^ (-(criticalMirror s).re)) +
        etaCriticalMirrorCorrectionOriginalProjectionConstant s *
          ((K : ℝ) ^ (-s.re)) := by
  unfold etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
  unfold etaCriticalMirrorPairedFrameCorrectionTailPowerBound
  unfold etaCriticalMirrorCorrectionMirrorProjectionConstant
  unfold etaCriticalMirrorCorrectionOriginalProjectionConstant
  ring

/--
Right-side `K`-normalized correction audit. The mirror term is constant and the
original term carries the positive exponent gap `re s - re (criticalMirror s)`.
-/
noncomputable def etaCriticalMirrorRightIndexNormalizedCorrectionPowerAudit
    (s : ℂ) (K : ℕ) : ℝ :=
  etaCriticalMirrorCorrectionMirrorProjectionConstant s +
    etaCriticalMirrorCorrectionOriginalProjectionConstant s *
      ((K : ℝ) ^ (-(s.re - (criticalMirror s).re)))

/--
Left-side `K`-normalized correction audit. The original term is constant and
the mirror term carries the positive exponent gap `re (criticalMirror s) - re s`.
-/
noncomputable def etaCriticalMirrorLeftIndexNormalizedCorrectionPowerAudit
    (s : ℂ) (K : ℕ) : ℝ :=
  etaCriticalMirrorCorrectionMirrorProjectionConstant s *
      ((K : ℝ) ^ (-((criticalMirror s).re - s.re))) +
    etaCriticalMirrorCorrectionOriginalProjectionConstant s

/--
Eventually, right normalization of the actual correction power bound is
exactly the right audit expression.
-/
theorem eventually_etaCriticalMirrorRightIndexNormalizedCorrectionPowerBound_eq_audit
    (s : ℂ) :
    ∀ᶠ K : ℕ in atTop,
      ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K =
        etaCriticalMirrorRightIndexNormalizedCorrectionPowerAudit s K := by
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hmirrorCancel :
      ((K : ℝ) ^ (criticalMirror s).re) *
          ((K : ℝ) ^ (-(criticalMirror s).re)) = 1 := by
    calc
      ((K : ℝ) ^ (criticalMirror s).re) *
          ((K : ℝ) ^ (-(criticalMirror s).re)) =
        (K : ℝ) ^ ((criticalMirror s).re + (-(criticalMirror s).re)) :=
          (Real.rpow_add hKpos _ _).symm
      _ = 1 := by
        rw [show (criticalMirror s).re + (-(criticalMirror s).re) = 0 by ring]
        simp
  have hcross :
      ((K : ℝ) ^ (criticalMirror s).re) *
          ((K : ℝ) ^ (-s.re)) =
        (K : ℝ) ^ (-(s.re - (criticalMirror s).re)) := by
    calc
      ((K : ℝ) ^ (criticalMirror s).re) *
          ((K : ℝ) ^ (-s.re)) =
        (K : ℝ) ^ ((criticalMirror s).re + (-s.re)) :=
          (Real.rpow_add hKpos _ _).symm
      _ = (K : ℝ) ^ (-(s.re - (criticalMirror s).re)) := by
        rw [show (criticalMirror s).re + (-s.re) =
          -(s.re - (criticalMirror s).re) by ring]
  rw [etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound_eq_constants]
  unfold etaCriticalMirrorRightIndexNormalizedCorrectionPowerAudit
  calc
    ((K : ℝ) ^ (criticalMirror s).re) *
        (etaCriticalMirrorCorrectionMirrorProjectionConstant s *
            ((K : ℝ) ^ (-(criticalMirror s).re)) +
          etaCriticalMirrorCorrectionOriginalProjectionConstant s *
            ((K : ℝ) ^ (-s.re))) =
      etaCriticalMirrorCorrectionMirrorProjectionConstant s *
          (((K : ℝ) ^ (criticalMirror s).re) *
            ((K : ℝ) ^ (-(criticalMirror s).re))) +
        etaCriticalMirrorCorrectionOriginalProjectionConstant s *
          (((K : ℝ) ^ (criticalMirror s).re) *
            ((K : ℝ) ^ (-s.re))) := by ring
    _ = etaCriticalMirrorCorrectionMirrorProjectionConstant s +
        etaCriticalMirrorCorrectionOriginalProjectionConstant s *
          ((K : ℝ) ^ (-(s.re - (criticalMirror s).re))) := by
      rw [hmirrorCancel, hcross]
      ring

/--
Eventually, left normalization of the actual correction power bound is
exactly the left audit expression.
-/
theorem eventually_etaCriticalMirrorLeftIndexNormalizedCorrectionPowerBound_eq_audit
    (s : ℂ) :
    ∀ᶠ K : ℕ in atTop,
      ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K =
        etaCriticalMirrorLeftIndexNormalizedCorrectionPowerAudit s K := by
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have horiginalCancel :
      ((K : ℝ) ^ s.re) * ((K : ℝ) ^ (-s.re)) = 1 := by
    calc
      ((K : ℝ) ^ s.re) * ((K : ℝ) ^ (-s.re)) =
        (K : ℝ) ^ (s.re + (-s.re)) :=
          (Real.rpow_add hKpos _ _).symm
      _ = 1 := by
        rw [show s.re + (-s.re) = 0 by ring]
        simp
  have hcross :
      ((K : ℝ) ^ s.re) *
          ((K : ℝ) ^ (-(criticalMirror s).re)) =
        (K : ℝ) ^ (-((criticalMirror s).re - s.re)) := by
    calc
      ((K : ℝ) ^ s.re) *
          ((K : ℝ) ^ (-(criticalMirror s).re)) =
        (K : ℝ) ^ (s.re + (-(criticalMirror s).re)) :=
          (Real.rpow_add hKpos _ _).symm
      _ = (K : ℝ) ^ (-((criticalMirror s).re - s.re)) := by
        rw [show s.re + (-(criticalMirror s).re) =
          -((criticalMirror s).re - s.re) by ring]
  rw [etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound_eq_constants]
  unfold etaCriticalMirrorLeftIndexNormalizedCorrectionPowerAudit
  calc
    ((K : ℝ) ^ s.re) *
        (etaCriticalMirrorCorrectionMirrorProjectionConstant s *
            ((K : ℝ) ^ (-(criticalMirror s).re)) +
          etaCriticalMirrorCorrectionOriginalProjectionConstant s *
            ((K : ℝ) ^ (-s.re))) =
      etaCriticalMirrorCorrectionMirrorProjectionConstant s *
          (((K : ℝ) ^ s.re) *
            ((K : ℝ) ^ (-(criticalMirror s).re))) +
        etaCriticalMirrorCorrectionOriginalProjectionConstant s *
          (((K : ℝ) ^ s.re) * ((K : ℝ) ^ (-s.re))) := by ring
    _ = etaCriticalMirrorCorrectionMirrorProjectionConstant s *
          ((K : ℝ) ^ (-((criticalMirror s).re - s.re))) +
        etaCriticalMirrorCorrectionOriginalProjectionConstant s := by
      rw [hcross, horiginalCancel]
      ring

/-- On the right of the critical line, the right correction audit tends to its mirror constant. -/
theorem etaCriticalMirrorRightIndexNormalizedCorrectionPowerAudit_tendsto
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (etaCriticalMirrorRightIndexNormalizedCorrectionPowerAudit s)
      atTop
      (nhds (etaCriticalMirrorCorrectionMirrorProjectionConstant s)) := by
  have hgap : 0 < s.re - (criticalMirror s).re := by
    rw [criticalMirror_re]
    linarith
  have hpow :
      Tendsto
        (fun K : ℕ =>
          ((K : ℝ) ^ (-(s.re - (criticalMirror s).re))))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgap).comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun K : ℕ =>
      etaCriticalMirrorCorrectionMirrorProjectionConstant s +
        etaCriticalMirrorCorrectionOriginalProjectionConstant s *
          ((K : ℝ) ^ (-(s.re - (criticalMirror s).re))))
    atTop _
  simpa [Function.comp_def] using
    tendsto_const_nhds.add (tendsto_const_nhds.mul hpow)

/-- On the left of the critical line, the left correction audit tends to its original constant. -/
theorem etaCriticalMirrorLeftIndexNormalizedCorrectionPowerAudit_tendsto
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (etaCriticalMirrorLeftIndexNormalizedCorrectionPowerAudit s)
      atTop
      (nhds (etaCriticalMirrorCorrectionOriginalProjectionConstant s)) := by
  have hgap : 0 < (criticalMirror s).re - s.re := by
    rw [criticalMirror_re]
    linarith
  have hpow :
      Tendsto
        (fun K : ℕ =>
          ((K : ℝ) ^ (-((criticalMirror s).re - s.re))))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgap).comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun K : ℕ =>
      etaCriticalMirrorCorrectionMirrorProjectionConstant s *
          ((K : ℝ) ^ (-((criticalMirror s).re - s.re))) +
        etaCriticalMirrorCorrectionOriginalProjectionConstant s)
    atTop _
  simpa [Function.comp_def] using
    (tendsto_const_nhds.mul hpow).add tendsto_const_nhds

/--
On the right of the critical line, the actual correction power bound normalized
by `K ^ re(criticalMirror s)` tends to the mirror constant.
-/
theorem etaCriticalMirrorRightIndexNormalizedCorrectionPowerBound_tendsto
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K)
      atTop
      (nhds (etaCriticalMirrorCorrectionMirrorProjectionConstant s)) := by
  refine
    (etaCriticalMirrorRightIndexNormalizedCorrectionPowerAudit_tendsto hre).congr' ?_
  exact
    (eventually_etaCriticalMirrorRightIndexNormalizedCorrectionPowerBound_eq_audit s).mono
      (fun _ h => h.symm)

/--
On the left of the critical line, the actual correction power bound normalized
by `K ^ re s` tends to the original constant.
-/
theorem etaCriticalMirrorLeftIndexNormalizedCorrectionPowerBound_tendsto
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K)
      atTop
      (nhds (etaCriticalMirrorCorrectionOriginalProjectionConstant s)) := by
  refine
    (etaCriticalMirrorLeftIndexNormalizedCorrectionPowerAudit_tendsto hre).congr' ?_
  exact
    (eventually_etaCriticalMirrorLeftIndexNormalizedCorrectionPowerBound_eq_audit s).mono
      (fun _ h => h.symm)

end DkMath.RH.CFBRCProjection
