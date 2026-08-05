/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailChordCollapseCriterion
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailChordRateAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The even finite critical-mirror defect endpoint, multiplied by the same index
power used to normalize the paired defect tail.
-/
noncomputable def etaCriticalMirrorIndexNormalizedEvenDefectEndpoint
    (a : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  (((((k + 1 : ℕ) : ℝ)) ^ a : ℝ) : ℂ) *
    etaCriticalMirrorTransportDefectEndpoint (2 * (k + 1)) s

/-- The even endpoint subsequence remains cofinal. -/
private theorem tendsto_two_mul_succ_atTop :
    Tendsto (fun k : ℕ => 2 * (k + 1)) atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro k l hkl
  change 2 * (k + 1) < 2 * (l + 1)
  omega

/--
The unweighted even finite defect endpoint already tends to zero at every
nonreal nontrivial zero.  This records the currently available zero-locus
information before the missing rate upgrade is imposed.
-/
theorem etaCriticalMirrorEvenDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorTransportDefectEndpoint (2 * (k + 1)) s)
      atTop (nhds 0) :=
  (etaCriticalMirrorTransportDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him).comp tendsto_two_mul_succ_atTop

/--
At a nonreal nontrivial zero, the normalized unrotated defect tail is exactly
the negative of the correspondingly normalized even finite defect endpoint.
This is the exact bridge from the tail formulation back to zero-locus endpoint
data.
-/
theorem etaCriticalMirrorIndexNormalizedDefectTail_eq_neg_evenDefectEndpoint
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (a : ℝ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedDefectTail a s k =
      -etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k := by
  unfold etaCriticalMirrorIndexNormalizedDefectTail
  unfold etaCriticalMirrorIndexNormalizedEvenDefectEndpoint
  rw [etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial]
  rw [etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
    hs him]
  ring

/--
The missing rate statement at one normalization exponent: after multiplying
the even finite defect endpoint by the dominant index power, it still tends to
zero.
-/
def EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse
    (a : ℝ) (s : ℂ) : Prop :=
  Tendsto
    (etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s)
    atTop (nhds 0)

/-- The endpoint rate collapse forces the normalized unrotated tail to zero. -/
theorem etaCriticalMirrorIndexNormalizedDefectTail_tendsto_zero_of_evenEndpointRateCollapse
    {a : ℝ} {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hrate : EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse a s) :
    Tendsto
      (etaCriticalMirrorIndexNormalizedDefectTail a s)
      atTop (nhds 0) := by
  have hneg :
      Tendsto
        (fun k : ℕ =>
          -etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k)
        atTop (nhds 0) := by
    simpa using hrate.neg
  refine hneg.congr' (Eventually.of_forall fun k => ?_)
  exact
    (etaCriticalMirrorIndexNormalizedDefectTail_eq_neg_evenDefectEndpoint
      hs him a k).symm

namespace EtaPairPositiveDensityBlockSchedule

/-- Every positive-density terminal index is cofinal. -/
private theorem terminalIndex_tendsto_atTop_rateAudit
    (S : EtaPairPositiveDensityBlockSchedule) :
    Tendsto (fun K : ℕ => K + S.blockLength K) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro n
  exact eventually_atTop.2 ⟨n, by
    intro K hK
    omega⟩

/--
If the normalized unrotated tail itself tends to zero, then its chord along
any positive-density schedule also tends to zero.
-/
theorem scheduledNormalizedDefectTailChord_tendsto_zero_of_tail_tendsto_zero
    (S : EtaPairPositiveDensityBlockSchedule)
    {a : ℝ} {s : ℂ}
    (htail :
      Tendsto
        (etaCriticalMirrorIndexNormalizedDefectTail a s)
        atTop (nhds 0)) :
    Tendsto
      (S.scheduledNormalizedDefectTailChord a s)
      atTop (nhds 0) := by
  have hterminal :
      Tendsto
        (fun K : ℕ =>
          etaCriticalMirrorIndexNormalizedDefectTail
            a s (K + S.blockLength K))
        atTop (nhds 0) :=
    htail.comp S.terminalIndex_tendsto_atTop_rateAudit
  have hdiff :
      Tendsto
        (fun K : ℕ =>
          etaCriticalMirrorIndexNormalizedDefectTail
              a s (K + S.blockLength K) -
            etaCriticalMirrorIndexNormalizedDefectTail a s K)
        atTop (nhds 0) := by
    simpa using hterminal.sub htail
  have hnorm :
      Tendsto
        (fun K : ℕ =>
          ‖etaCriticalMirrorIndexNormalizedDefectTail
              a s (K + S.blockLength K) -
            etaCriticalMirrorIndexNormalizedDefectTail a s K‖)
        atTop (nhds 0) := by
    change Tendsto
      ((fun z : ℂ => ‖z‖) ∘
        (fun K : ℕ =>
          etaCriticalMirrorIndexNormalizedDefectTail
              a s (K + S.blockLength K) -
            etaCriticalMirrorIndexNormalizedDefectTail a s K))
      atTop (nhds 0)
    simpa only [norm_zero] using
      (continuous_norm.tendsto (0 : ℂ)).comp hdiff
  simpa [scheduledNormalizedDefectTailChord,
    etaCriticalMirrorIndexNormalizedDefectTailChord] using hnorm

end EtaPairPositiveDensityBlockSchedule

/--
The normalized even-endpoint rate collapse supplies the exact two-scale chord
collapse consumed by the same-object collision criterion.
-/
theorem etaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse_of_evenEndpointRateCollapse
    {a : ℝ} {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hrate : EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse a s) :
    EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse a s := by
  have htail :=
    etaCriticalMirrorIndexNormalizedDefectTail_tendsto_zero_of_evenEndpointRateCollapse
      hs him hrate
  exact
    ⟨etaPairHalfDensityBlockSchedule.
        scheduledNormalizedDefectTailChord_tendsto_zero_of_tail_tendsto_zero
          htail,
      etaPairFullDensityBlockSchedule.
        scheduledNormalizedDefectTailChord_tendsto_zero_of_tail_tendsto_zero
          htail⟩

/--
Side-aware zero-locus rate provider.  It asks for precisely the dominant
power-weighted endpoint decay missing from the currently available unweighted
endpoint theorem.
-/
structure EtaCriticalMirrorZeroLocusDominantEndpointRateCollapse
    (s : ℂ) : Prop where
  left_rate :
    s.re < (1 : ℝ) / 2 →
      EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse s.re s
  right_rate :
    (1 : ℝ) / 2 < s.re →
      EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse
        (criticalMirror s).re s

/-- The dominant endpoint-rate provider yields the two-scale chord provider. -/
theorem etaCriticalMirrorZeroLocusTwoScaleChordCollapse_of_dominantEndpointRateCollapse
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hrate : EtaCriticalMirrorZeroLocusDominantEndpointRateCollapse s) :
    EtaCriticalMirrorZeroLocusTwoScaleChordCollapse s where
  left_collapse hleft :=
    etaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse_of_evenEndpointRateCollapse
      hs him (hrate.left_rate hleft)
  right_collapse hright :=
    etaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse_of_evenEndpointRateCollapse
      hs him (hrate.right_rate hright)

/--
A nonreal nontrivial zero satisfying the dominant endpoint rate upgrade lies
on the critical line.
-/
theorem re_eq_half_of_nontrivialRiemannZetaZero_of_dominantEndpointRateCollapse
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hrate : EtaCriticalMirrorZeroLocusDominantEndpointRateCollapse s) :
    s.re = (1 : ℝ) / 2 := by
  apply re_eq_half_of_nontrivialRiemannZetaZero_of_twoScaleChordCollapse hs him
  exact
    etaCriticalMirrorZeroLocusTwoScaleChordCollapse_of_dominantEndpointRateCollapse
      hs him hrate

/-- The endpoint-rate provider maps a nonreal zero into CFBRC closure. -/
theorem offCriticalCFBRC_eq_zero_of_nontrivialRiemannZetaZero_of_dominantEndpointRateCollapse
    {d : ℕ} (hd : 0 < d) {s : ℂ} (Θ : ℝ)
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hrate : EtaCriticalMirrorZeroLocusDominantEndpointRateCollapse s) :
    offCriticalCFBRC d s.re Θ = 0 := by
  apply (offCriticalCFBRC_eq_zero_iff_re_eq_half hd s.re Θ).2
  exact
    re_eq_half_of_nontrivialRiemannZetaZero_of_dominantEndpointRateCollapse
      hs him hrate

end DkMath.RH.CFBRCProjection
