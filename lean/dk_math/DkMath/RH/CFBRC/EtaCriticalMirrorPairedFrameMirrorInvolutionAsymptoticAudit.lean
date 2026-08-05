/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedEvenDefectEndpointAsymptotic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMirrorInvolutionAsymptoticAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Critical reflection preserves every pair-left base rotation. -/
theorem etaPairBaseRotation_criticalMirror
    (s : ℂ) (k : ℕ) :
    etaPairBaseRotation (criticalMirror s) k =
      etaPairBaseRotation s k := by
  unfold etaPairBaseRotation
  rw [criticalMirror_im]

/-- One paired critical-mirror defect changes sign under critical reflection. -/
theorem etaCriticalMirrorDefectPairTerm_criticalMirror_eq_neg
    (s : ℂ) (k : ℕ) :
    etaCriticalMirrorDefectPairTerm (criticalMirror s) k =
      -etaCriticalMirrorDefectPairTerm s k := by
  calc
    etaCriticalMirrorDefectPairTerm (criticalMirror s) k =
        etaPairTerm (criticalMirror (criticalMirror s)) k -
          etaPairTerm (criticalMirror s) k :=
      etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub
        (criticalMirror s) k
    _ = etaPairTerm s k - etaPairTerm (criticalMirror s) k := by
      rw [criticalMirror_involutive]
    _ = -(etaPairTerm (criticalMirror s) k - etaPairTerm s k) := by
      ring
    _ = -etaCriticalMirrorDefectPairTerm s k := by
      rw [etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub]

/-- Every finite paired defect endpoint changes sign under critical reflection. -/
theorem etaCriticalMirrorDefectPairedPartial_criticalMirror_eq_neg
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorDefectPairedPartial K (criticalMirror s) =
      -etaCriticalMirrorDefectPairedPartial K s := by
  calc
    etaCriticalMirrorDefectPairedPartial K (criticalMirror s) =
        etaPairedPartial K (criticalMirror (criticalMirror s)) -
          etaPairedPartial K (criticalMirror s) :=
      etaCriticalMirrorDefectPairedPartial_eq_etaPairedPartial_sub
        K (criticalMirror s)
    _ = etaPairedPartial K s - etaPairedPartial K (criticalMirror s) := by
      rw [criticalMirror_involutive]
    _ = -(etaPairedPartial K (criticalMirror s) - etaPairedPartial K s) := by
      ring
    _ = -etaCriticalMirrorDefectPairedPartial K s := by
      rw [etaCriticalMirrorDefectPairedPartial_eq_etaPairedPartial_sub]

/-- Every infinite paired defect tail changes sign under critical reflection. -/
theorem etaCriticalMirrorDefectPairTail_criticalMirror_eq_neg
    (K : ℕ) (s : ℂ) :
    etaCriticalMirrorDefectPairTail K (criticalMirror s) =
      -etaCriticalMirrorDefectPairTail K s := by
  unfold etaCriticalMirrorDefectPairTail
  rw [show
    (fun j : ℕ =>
      etaCriticalMirrorDefectPairTerm (criticalMirror s) (j + K)) =
        (fun j : ℕ => -etaCriticalMirrorDefectPairTerm s (j + K)) by
      funext j
      exact etaCriticalMirrorDefectPairTerm_criticalMirror_eq_neg s (j + K)]
  exact tsum_neg

/-- Index normalization preserves the mirror sign reversal of the defect tail. -/
theorem etaCriticalMirrorIndexNormalizedDefectTail_criticalMirror_eq_neg
    (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedDefectTail a (criticalMirror s) k =
      -etaCriticalMirrorIndexNormalizedDefectTail a s k := by
  unfold etaCriticalMirrorIndexNormalizedDefectTail
  rw [etaCriticalMirrorDefectPairTail_criticalMirror_eq_neg]
  ring

/-- The normalized even finite defect endpoint changes sign under reflection. -/
theorem etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_criticalMirror_eq_neg
    (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a (criticalMirror s) k =
      -etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k := by
  unfold etaCriticalMirrorIndexNormalizedEvenDefectEndpoint
  rw [etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial,
    etaCriticalMirrorTransportDefectEndpoint_two_mul_eq_pairedPartial,
    etaCriticalMirrorDefectPairedPartial_criticalMirror_eq_neg]
  ring

/-- The rotating-frame normalized defect tail also changes sign exactly. -/
theorem etaCriticalMirrorIndexNormalizedRotatedDefectTail_criticalMirror_eq_neg
    (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedDefectTail a (criticalMirror s) k =
      -etaCriticalMirrorIndexNormalizedRotatedDefectTail a s k := by
  rw [etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul,
    etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul,
    etaPairBaseRotation_criticalMirror,
    etaCriticalMirrorIndexNormalizedDefectTail_criticalMirror_eq_neg]
  ring

/-- The rotating-frame normalized even endpoint changes sign exactly. -/
theorem etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_criticalMirror_eq_neg
    (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (criticalMirror s) k =
      -etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k := by
  unfold etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
  rw [etaPairBaseRotation_criticalMirror,
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint_criticalMirror_eq_neg]
  ring

/-- Mirror reflection transports every rotating endpoint limit to its negative. -/
theorem etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_criticalMirror_tendsto_neg
    {a : ℝ} {s C : ℂ}
    (hendpoint :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
        atTop (nhds C)) :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (criticalMirror s))
      atTop (nhds (-C)) := by
  have hneg := hendpoint.neg
  refine hneg.congr' (Eventually.of_forall fun k => ?_)
  exact
    (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_criticalMirror_eq_neg
      a s k).symm

/--
Certificate showing that the original and mirror endpoint asymptotics are
exact sign partners, not competing limits of one sequence.
-/
structure EtaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate
    (a : ℝ) (s C : ℂ) : Prop where
  original_endpoint_tendsto :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
      atTop (nhds C)
  mirror_endpoint_tendsto :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
        a (criticalMirror s))
      atTop (nhds (-C))
  exact_sign_reversal :
    ∀ k : ℕ,
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
          a (criticalMirror s) k =
        -etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s k

/-- Build the mirror compatibility certificate from either endpoint limit. -/
theorem etaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate_of_limit
    {a : ℝ} {s C : ℂ}
    (hendpoint :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
        atTop (nhds C)) :
    EtaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate
      a s C :=
  { original_endpoint_tendsto := hendpoint
    mirror_endpoint_tendsto :=
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_criticalMirror_tendsto_neg
        hendpoint
    exact_sign_reversal :=
      etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_criticalMirror_eq_neg
        a s }

/--
Right of the critical line, the original endpoint limit `-C` and the mirror
endpoint limit `C` are the exact sign-compatible pair.
-/
theorem etaCriticalMirrorRightEndpointMirrorAsymptoticCompatibilityCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    EtaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate
      (criticalMirror s).re s
      (-etaPairIndexNormalizedTailConstant (criticalMirror s)) := by
  apply
    etaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate_of_limit
  exact
    (etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
      hs him hre).rotated_endpoint_tendsto

/--
Left of the critical line, the original endpoint limit `C` and the mirror
endpoint limit `-C` are the exact sign-compatible pair.
-/
theorem etaCriticalMirrorLeftEndpointMirrorAsymptoticCompatibilityCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    EtaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate
      s.re s (etaPairIndexNormalizedTailConstant s) := by
  apply
    etaCriticalMirrorEndpointMirrorAsymptoticCompatibilityCertificate_of_limit
  simpa only [neg_neg] using
    (etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
      hs him hre).rotated_endpoint_tendsto

end DkMath.RH.CFBRCProjection
