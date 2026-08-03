/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjectionTail
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameVariation"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology
open DkMath.RH.Weave.Analytic

/--
The finite cumulative signed motion of the pair-local frames telescopes to the
single endpoint log difference.
-/
theorem sum_range_etaPairFrameStepPhase
    (s : ℂ) (K : ℕ) :
    (Finset.range K).sum (etaPairFrameStepPhase s) =
      s.im *
        (Real.log (etaPairFrameLeftEndpoint K) -
          Real.log (etaPairFrameLeftEndpoint 0)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      unfold etaPairFrameStepPhase
      ring

/--
Since the initial pair frame is based at `1`, the cumulative signed frame
phase is exactly `s.im * log (2K+1)`.
-/
theorem sum_range_etaPairFrameStepPhase_eq_im_mul_log
    (s : ℂ) (K : ℕ) :
    (Finset.range K).sum (etaPairFrameStepPhase s) =
      s.im * Real.log (etaPairFrameLeftEndpoint K) := by
  simpa [etaPairFrameLeftEndpoint] using
    sum_range_etaPairFrameStepPhase s K

/--
The finite total angular variation of the pair-local frames also telescopes.
It is `|s.im| * log (2K+1)`.
-/
theorem sum_range_etaPairFrameStepSpan
    (s : ℂ) (K : ℕ) :
    (Finset.range K).sum (etaPairFrameStepSpan s) =
      |s.im| *
        (Real.log (etaPairFrameLeftEndpoint K) -
          Real.log (etaPairFrameLeftEndpoint 0)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have ha : 0 < etaPairFrameLeftEndpoint K :=
        etaPairFrameLeftEndpoint_pos K
      have hb : 0 < etaPairFrameLeftEndpoint (K + 1) :=
        etaPairFrameLeftEndpoint_pos (K + 1)
      rw [Finset.sum_range_succ, ih]
      unfold etaPairFrameStepSpan
      rw [Real.log_div hb.ne' ha.ne']
      ring

/-- The cumulative absolute frame motion is `|s.im| * log (2K+1)`. -/
theorem sum_range_etaPairFrameStepSpan_eq_abs_im_mul_log
    (s : ℂ) (K : ℕ) :
    (Finset.range K).sum (etaPairFrameStepSpan s) =
      |s.im| * Real.log (etaPairFrameLeftEndpoint K) := by
  simpa [etaPairFrameLeftEndpoint] using
    sum_range_etaPairFrameStepSpan s K

/-- The real left endpoints of the natural eta-pair frames tend to infinity. -/
theorem etaPairFrameLeftEndpoint_tendsto_atTop :
    Tendsto etaPairFrameLeftEndpoint atTop atTop := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := hcast.comp tendsto_two_mul_add_one_atTop
  simpa [etaPairFrameLeftEndpoint, Function.comp_def] using h

/--
At every nonreal point, the cumulative absolute pair-frame motion diverges
logarithmically to infinity, even though each adjacent step tends to zero.
-/
theorem etaPairFrameStepSpanPartial_tendsto_atTop_of_im_ne_zero
    {s : ℂ} (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        (Finset.range K).sum (etaPairFrameStepSpan s))
      atTop atTop := by
  have hlog :
      Tendsto
        (fun K : ℕ => Real.log (etaPairFrameLeftEndpoint K))
        atTop atTop :=
    Real.tendsto_log_atTop.comp etaPairFrameLeftEndpoint_tendsto_atTop
  have hscaled := hlog.const_mul_atTop (abs_pos.mpr him)
  simpa only [sum_range_etaPairFrameStepSpan_eq_abs_im_mul_log] using
    hscaled

/--
Consequently, the adjacent pair-frame spans are not summable at a nonreal
point.  A fixed asymptotic frame cannot be obtained by summing their absolute
angular increments.
-/
theorem not_summable_etaPairFrameStepSpan_of_im_ne_zero
    {s : ℂ} (him : s.im ≠ 0) :
    ¬ Summable (etaPairFrameStepSpan s) := by
  intro hsum
  have hfinite :
      Tendsto
        (fun K : ℕ =>
          (Finset.range K).sum (etaPairFrameStepSpan s))
        atTop
        (nhds (∑' k : ℕ, etaPairFrameStepSpan s k)) := by
    simpa using hsum.hasSum.tendsto_sum_nat
  exact
    not_tendsto_nhds_of_tendsto_atTop
      (etaPairFrameStepSpanPartial_tendsto_atTop_of_im_ne_zero him)
      _ hfinite

end DkMath.RH.CFBRCProjection
