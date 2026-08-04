/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCosineLossAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportReduction"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The signed projection of the complete frame-correction series is summable at
every nonreal nontrivial zero.
-/
theorem summable_etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Summable
      (etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm s) := by
  have hcorr :=
    summable_etaCriticalMirrorPairedFrameCorrectionTerm_of_nontrivialRiemannZetaZero
      hs him
  have himag :
      Summable
        (fun k : ℕ =>
          (etaCriticalMirrorPairedFrameCorrectionTerm s k).im) :=
    (hcorr.hasSum.map Complex.imCLM Complex.imCLM.continuous).summable
  have hscaled := himag.mul_left s.im
  change Summable
    (fun k : ℕ => s.im * (etaCriticalMirrorPairedFrameCorrectionTerm s k).im)
  exact hscaled

/--
The first-order sine-transport series is summable.  This follows from the
summable signed correction after subtracting the already absolutely summable
cosine-loss series.
-/
theorem summable_etaCriticalMirrorPairedFrameCorrectionSineTransportTerm
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Summable
      (etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s) := by
  have hsigned :=
    summable_etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm
      hs him
  have hcos :=
    summable_etaCriticalMirrorPairedFrameCorrectionCosineLossTerm
      hs him
  have hsub := hsigned.sub hcos
  refine hsub.congr ?_
  intro k
  rw [etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm_eq_sine_add_cosineLoss]
  ring

/-- Tail of the first-order sine transport beginning at correction index `K`. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionSineTransportTail
    (K : ℕ) (s : ℂ) : ℝ :=
  ∑' n : ℕ,
    etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s (n + K)

/-- Every shifted sine-transport tail series is summable. -/
theorem summable_etaCriticalMirrorPairedFrameCorrectionSineTransportTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    Summable
      (fun n : ℕ =>
        etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s (n + K)) :=
  (summable_nat_add_iff K).2
    (summable_etaCriticalMirrorPairedFrameCorrectionSineTransportTerm
      hs him)

/--
Exact tail-level split of the signed Abel correction into sine transport and
cosine loss.  All cancellation remains inside the signed real series.
-/
theorem etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_sineTransportTail_add_cosineLossTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTail K s =
      etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s +
        etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s := by
  have hsine :=
    summable_etaCriticalMirrorPairedFrameCorrectionSineTransportTail
      hs him K
  have hcos :
      Summable
        (fun n : ℕ =>
          etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s (n + K)) :=
    (summable_nat_add_iff K).2
      (summable_etaCriticalMirrorPairedFrameCorrectionCosineLossTerm
        hs him)
  rw [etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_tsum_sine_add_cosineLoss
    hs him K]
  unfold etaCriticalMirrorPairedFrameCorrectionSineTransportTail
  unfold etaCriticalMirrorPairedFrameCorrectionCosineLossTail
  exact (hsine.hasSum.add hcos.hasSum).tsum_eq

/--
Subtracting the sine-transport tail from the full correction projection leaves
exactly the cosine-loss tail.
-/
theorem etaCriticalMirrorPairedFrameCorrectionProjectionTail_sub_sineTransportTail_eq_cosineLossTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTail K s -
        etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s =
      etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s := by
  rw [etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_sineTransportTail_add_cosineLossTail
    hs him K]
  ring

/--
On the right, the predecessor correction and predecessor sine-transport tail
have the same pair-left normalized main order.
-/
theorem etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCorrectionSubSineTransport_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
          (etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s -
            etaCriticalMirrorPairedFrameCorrectionSineTransportTail (K - 1) s))
      atTop (nhds 0) := by
  have hcos :=
    etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCosineLossTail_tendsto_zero
      hs him hre
  refine hcos.congr' ?_
  filter_upwards with K
  rw [etaCriticalMirrorPairedFrameCorrectionProjectionTail_sub_sineTransportTail_eq_cosineLossTail
    hs him (K - 1)]

/--
On the left, the predecessor correction and predecessor sine-transport tail
have the same pair-left normalized main order.
-/
theorem etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCorrectionSubSineTransport_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ s.re *
          (etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s -
            etaCriticalMirrorPairedFrameCorrectionSineTransportTail (K - 1) s))
      atTop (nhds 0) := by
  have hcos :=
    etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCosineLossTail_tendsto_zero
      hs him hre
  refine hcos.congr' ?_
  filter_upwards with K
  rw [etaCriticalMirrorPairedFrameCorrectionProjectionTail_sub_sineTransportTail_eq_cosineLossTail
    hs him (K - 1)]

/-- Right normalized correction minus normalized sine transport tends to zero. -/
theorem etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCorrection_sub_normalizedSineTransport_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
            etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s -
          etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
            etaCriticalMirrorPairedFrameCorrectionSineTransportTail (K - 1) s)
      atTop (nhds 0) := by
  have hfactor :=
    etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCorrectionSubSineTransport_tendsto_zero
      hs him hre
  refine hfactor.congr' ?_
  filter_upwards with K
  ring

/-- Left normalized correction minus normalized sine transport tends to zero. -/
theorem etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCorrection_sub_normalizedSineTransport_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s -
          etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorPairedFrameCorrectionSineTransportTail (K - 1) s)
      atTop (nhds 0) := by
  have hfactor :=
    etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCorrectionSubSineTransport_tendsto_zero
      hs him hre
  refine hfactor.congr' ?_
  filter_upwards with K
  ring

end DkMath.RH.CFBRCProjection
