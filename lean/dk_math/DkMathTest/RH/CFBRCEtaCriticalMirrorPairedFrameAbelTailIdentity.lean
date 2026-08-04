/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelTailIdentity

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameAbelTailIdentity"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameAbelTailIdentity

open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Summable (etaCriticalMirrorRotatedDefectPairTerm s) :=
  summable_etaCriticalMirrorRotatedDefectPairTerm hs

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    (∑' k : ℕ, etaCriticalMirrorRotatedDefectPairTerm s k) =
      -(∑' k : ℕ,
        etaCriticalMirrorPairedFrameCorrectionTerm s k) :=
  tsum_etaCriticalMirrorRotatedDefectPairTerm_eq_neg_correction_tsum
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaPairBaseRotation s (K - 1) *
        etaCriticalMirrorDefectPairTail K s =
      etaCriticalMirrorRotatedDefectPairTail K s +
        etaCriticalMirrorPairedFrameCorrectionTail (K - 1) s :=
  etaPairBaseRotation_pred_mul_defectPairTail_eq_rotatedTail_add_correctionTail
    hs him K

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPredecessorFrameWholeTailProjection K s =
      etaCriticalMirrorRotatedDefectProjectionTail K s +
        etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s :=
  etaCriticalMirrorPredecessorFrameWholeTailProjection_eq_rotatedProjectionTail_add_correction
    hs him K

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameAbelTailIdentity
