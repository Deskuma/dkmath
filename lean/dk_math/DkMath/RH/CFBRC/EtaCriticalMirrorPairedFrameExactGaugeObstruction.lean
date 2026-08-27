/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGaugeAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameExactGaugeObstruction"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/--
Certificate for the exact-counterrotation fixed-frame obstruction.

The adjacent frame motion vanishes locally, but its cumulative absolute
variation diverges and is not summable.  Removing the known logarithmic frame
rotation exactly is only a gauge cancellation: it returns the original defect
partial, whose every fixed projection still tends to zero at a nonreal
nontrivial zeta zero.
-/
structure EtaCriticalMirrorPairedFrameExactGaugeObstructionCertificate
    (s ω : ℂ) : Prop where
  local_step_tendsto_zero :
    Tendsto (etaPairFrameStepSpan s) atTop (nhds 0)
  cumulative_span_eq :
    ∀ K : ℕ,
      (Finset.range K).sum (etaPairFrameStepSpan s) =
        |s.im| * Real.log (etaPairFrameLeftEndpoint K)
  cumulative_span_tendsto_atTop :
    Tendsto
      (fun K : ℕ =>
        (Finset.range K).sum (etaPairFrameStepSpan s))
      atTop atTop
  step_span_not_summable :
    ¬ Summable (etaPairFrameStepSpan s)
  exact_gauge_partial_eq_original :
    ∀ K : ℕ,
      etaCriticalMirrorGaugeRenormalizedDefectPairedPartial K s =
        etaCriticalMirrorDefectPairedPartial K s
  fixed_projection_tendsto_zero :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorGaugeRenormalizedProjectedPartial K ω s)
      atTop (nhds 0)

/--
At every nonreal nontrivial zeta zero, exact logarithmic counterrotation
produces the full obstruction certificate.
-/
theorem etaCriticalMirrorPairedFrameExactGaugeObstructionCertificate_of_nontrivialRiemannZetaZero
    {s ω : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    EtaCriticalMirrorPairedFrameExactGaugeObstructionCertificate s ω := by
  refine
    ⟨etaPairFrameStepSpan_tendsto_zero s,
      fun K => sum_range_etaPairFrameStepSpan_eq_abs_im_mul_log s K,
      etaPairFrameStepSpanPartial_tendsto_atTop_of_im_ne_zero him,
      not_summable_etaPairFrameStepSpan_of_im_ne_zero him,
      fun K => etaCriticalMirrorGaugeRenormalizedDefectPairedPartial_eq K s,
      etaCriticalMirrorGaugeRenormalizedProjectedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
        hs him⟩

/--
Named closure decision for the exact-gauge route: it yields a winding/gauge
obstruction certificate, not an off-critical zero/nonzero collision.
-/
theorem etaCriticalMirrorPairedFrameExactGaugeClosureDecision
    {s ω : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    EtaCriticalMirrorPairedFrameExactGaugeObstructionCertificate s ω :=
  etaCriticalMirrorPairedFrameExactGaugeObstructionCertificate_of_nontrivialRiemannZetaZero
    hs him

end DkMath.RH.CFBRCProjection
