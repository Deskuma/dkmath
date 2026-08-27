/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailChordRateAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedEvenDefectEndpointAsymptotic"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The dominant-power normalized even finite defect endpoint transported into the
current pair-left frame.
-/
noncomputable def etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
    (a : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  etaPairBaseRotation s k *
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k

/--
At a nonreal nontrivial zero, the rotated normalized even endpoint is exactly
the negative of the rotated normalized defect tail.
-/
theorem etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_eq_neg_rotatedDefectTail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (a : ℝ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k =
      -etaCriticalMirrorIndexNormalizedRotatedDefectTail a s k := by
  unfold etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
  rw [etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul]
  rw [etaCriticalMirrorIndexNormalizedDefectTail_eq_neg_evenDefectEndpoint
    hs him a k]
  ring

/-- Pair-left rotation preserves the normalized even endpoint norm. -/
theorem norm_etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
    (a : ℝ) (s : ℂ) (k : ℕ) :
    ‖etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k‖ =
      ‖etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k‖ := by
  unfold etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
  rw [norm_mul, norm_etaPairBaseRotation, one_mul]

/--
Certificate recording the explicit rotating-frame endpoint limit and the
corresponding gauge-invariant norm limit.
-/
structure EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
    (a : ℝ) (s C : ℂ) : Prop where
  rotated_endpoint_tendsto :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
      atTop (nhds (-C))
  endpoint_norm_tendsto :
    Tendsto
      (fun k : ℕ =>
        ‖etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k‖)
      atTop (nhds ‖C‖)
  norm_limit_ne_zero :
    ‖C‖ ≠ 0

/--
A nonzero fixed limit of the rotated normalized defect tail yields an explicit
nonzero asymptotic for the normalized even finite endpoint.
-/
theorem etaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate_of_rotatedDefectTail_limit
    {a : ℝ} {s C : ℂ}
    (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (hrotated :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedDefectTail a s)
        atTop (nhds C))
    (hC : C ≠ 0) :
    EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
      a s C := by
  have hrotatedEndpoint :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
        atTop (nhds (-C)) := by
    have hneg := hrotated.neg
    refine hneg.congr' (Eventually.of_forall fun k => ?_)
    exact
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_eq_neg_rotatedDefectTail
        hs him a k).symm
  have hrotatedNorm :
      Tendsto
        (fun k : ℕ =>
          ‖etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k‖)
        atTop (nhds ‖-C‖) := by
    change Tendsto
      ((fun z : ℂ => ‖z‖) ∘
        etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
      atTop (nhds ‖-C‖)
    simpa only [Function.comp_apply] using
      (continuous_norm.tendsto (-C)).comp hrotatedEndpoint
  have hnorm :
      Tendsto
        (fun k : ℕ =>
          ‖etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k‖)
        atTop (nhds ‖-C‖) := by
    refine hrotatedNorm.congr' (Eventually.of_forall fun k => ?_)
    exact
      norm_etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k
  exact
    { rotated_endpoint_tendsto := hrotatedEndpoint
      endpoint_norm_tendsto := by
        simpa only [norm_neg] using hnorm
      norm_limit_ne_zero := norm_ne_zero_iff.mpr hC }

/--
A positive normalized endpoint norm limit is incompatible with endpoint rate
collapse to zero.
-/
theorem not_etaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse_of_asymptoticCertificate
    {a : ℝ} {s C : ℂ}
    (cert :
      EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
        a s C) :
    ¬ EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse a s := by
  intro hrate
  have hnormZero :
      Tendsto
        (fun k : ℕ =>
          ‖etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k‖)
        atTop (nhds 0) := by
    change Tendsto
      ((fun z : ℂ => ‖z‖) ∘
        etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s)
      atTop (nhds 0)
    simpa only [norm_zero] using
      (continuous_norm.tendsto (0 : ℂ)).comp hrate
  have hEq : ‖C‖ = 0 :=
    tendsto_nhds_unique cert.endpoint_norm_tendsto hnormZero
  exact cert.norm_limit_ne_zero hEq

/--
Right of the critical line, the dominant normalized even endpoint has the
mirror half-tail constant as its nonzero norm limit.
-/
theorem etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
      (criticalMirror s).re s
      (etaPairIndexNormalizedTailConstant (criticalMirror s)) := by
  apply
    etaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate_of_rotatedDefectTail_limit
      hs him
  · convert
      etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_tendsto_constant
        hs hre using 1
    rfl
  · exact etaPairIndexNormalizedTailConstant_ne_zero (criticalMirror s)

/--
Left of the critical line, the dominant normalized even endpoint has the
original half-tail constant as its nonzero norm limit.
-/
theorem etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
      s.re s (-etaPairIndexNormalizedTailConstant s) := by
  apply
    etaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate_of_rotatedDefectTail_limit
      hs him
  · convert
      etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_tendsto_neg_constant
        hs hre using 1
    rfl
  · exact neg_ne_zero.mpr (etaPairIndexNormalizedTailConstant_ne_zero s)

/-- The right dominant endpoint rate collapse is impossible at an off-critical zero. -/
theorem not_etaCriticalMirrorRightIndexNormalizedEvenDefectEndpointRateCollapse
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ¬ EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse
        (criticalMirror s).re s :=
  not_etaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse_of_asymptoticCertificate
    (etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
      hs him hre)

/-- The left dominant endpoint rate collapse is impossible at an off-critical zero. -/
theorem not_etaCriticalMirrorLeftIndexNormalizedEvenDefectEndpointRateCollapse
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ¬ EtaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse s.re s :=
  not_etaCriticalMirrorIndexNormalizedEvenDefectEndpointRateCollapse_of_asymptoticCertificate
    (etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
      hs him hre)

/--
Every nonreal off-critical nontrivial zero carries one dominant endpoint
asymptotic certificate with a nonzero gauge-invariant norm limit.
-/
structure EtaCriticalMirrorOffCriticalDominantEndpointAsymptoticCertificate
    (s : ℂ) : Prop where
  side_certificate :
    (s.re < (1 : ℝ) / 2 ∧
      EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
        s.re s (-etaPairIndexNormalizedTailConstant s)) ∨
    ((1 : ℝ) / 2 < s.re ∧
      EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
        (criticalMirror s).re s
        (etaPairIndexNormalizedTailConstant (criticalMirror s)))

/-- Build the dominant endpoint asymptotic certificate from an off-critical zero. -/
theorem etaCriticalMirrorOffCriticalDominantEndpointAsymptoticCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    EtaCriticalMirrorOffCriticalDominantEndpointAsymptoticCertificate s := by
  refine ⟨?_⟩
  rcases lt_or_gt_of_ne hre with hleft | hright
  · exact Or.inl
      ⟨hleft,
        etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
          hs him hleft⟩
  · exact Or.inr
      ⟨hright,
        etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
          hs him hright⟩

/--
Consequently, the side-aware dominant endpoint rate provider cannot hold at a
nonreal off-critical nontrivial zero.
-/
theorem not_etaCriticalMirrorZeroLocusDominantEndpointRateCollapse_of_offCriticalZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    ¬ EtaCriticalMirrorZeroLocusDominantEndpointRateCollapse s := by
  intro hrate
  rcases lt_or_gt_of_ne hre with hleft | hright
  · exact
      not_etaCriticalMirrorLeftIndexNormalizedEvenDefectEndpointRateCollapse
        hs him hleft (hrate.left_rate hleft)
  · exact
      not_etaCriticalMirrorRightIndexNormalizedEvenDefectEndpointRateCollapse
        hs him hright (hrate.right_rate hright)

end DkMath.RH.CFBRCProjection
