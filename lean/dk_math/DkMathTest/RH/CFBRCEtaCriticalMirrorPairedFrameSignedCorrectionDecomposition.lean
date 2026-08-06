/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSignedCorrectionDecomposition

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameSignedCorrectionDecomposition"

noncomputable section

namespace DkMath.RH.CFBRCProjection

example (s : ℂ) (k : ℕ) :
    (etaPairFrameStepMultiplier s k).re =
      Real.cos (etaPairFrameStepPhase s k) - 1 :=
  etaPairFrameStepMultiplier_re s k

example (s : ℂ) (k : ℕ) :
    (etaPairFrameStepMultiplier s k).im =
      Real.sin (etaPairFrameStepPhase s k) :=
  etaPairFrameStepMultiplier_im s k

example (s : ℂ) (k : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionTerm s k =
      etaPairFrameStepMultiplier s k *
        etaCriticalMirrorPairFrameTransportedDefectPartial s k :=
  etaCriticalMirrorPairedFrameCorrectionTerm_eq_stepMultiplier_mul s k

example (s : ℂ) (k : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm s k =
      etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k +
        etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s k :=
  etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm_eq_sine_add_cosineLoss
    s k

example (s : ℂ) (N : ℕ) :
    (Finset.range N).sum
        (etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm s) =
      (Finset.range N).sum
          (etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s) +
        (Finset.range N).sum
          (etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s) :=
  sum_etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm_eq s N

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTail K s =
      ∑' n : ℕ,
        etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm
          s (n + K) :=
  etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_tsum_signedTerms
    hs him K

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTail K s =
      ∑' n : ℕ,
        (etaCriticalMirrorPairedFrameCorrectionSineTransportTerm
            s (n + K) +
          etaCriticalMirrorPairedFrameCorrectionCosineLossTerm
            s (n + K)) :=
  etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_tsum_sine_add_cosineLoss
    hs him K

end DkMath.RH.CFBRCProjection
