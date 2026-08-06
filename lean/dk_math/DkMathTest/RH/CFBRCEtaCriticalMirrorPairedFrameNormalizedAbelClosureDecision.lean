import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedAbelClosureDecision

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedAbelClosureDecision"

noncomputable section
namespace DkMath.RH.CFBRCProjection

example (s : ℂ) :
    etaCriticalMirrorRightNormalizedAbelClosureResidual s = 0 :=
  etaCriticalMirrorRightNormalizedAbelClosureResidual_eq_zero s

example (s : ℂ) :
    etaCriticalMirrorLeftNormalizedAbelClosureResidual s = 0 :=
  etaCriticalMirrorLeftNormalizedAbelClosureResidual_eq_zero s

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    EtaCriticalMirrorNormalizedAbelCancellationCertificate
      (etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s)
      (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s) :=
  etaCriticalMirrorRightNormalizedAbelCancellationCertificate hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    EtaCriticalMirrorNormalizedAbelCancellationCertificate
      (etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s)
      (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s) :=
  etaCriticalMirrorLeftNormalizedAbelCancellationCertificate hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorRightNormalizedAbelClosureResidual s = 0 ∧
      EtaCriticalMirrorNormalizedAbelCancellationCertificate
        (etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s)
        (etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s) :=
  etaCriticalMirrorRightNormalizedAbelClosureDecision hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorLeftNormalizedAbelClosureResidual s = 0 ∧
      EtaCriticalMirrorNormalizedAbelCancellationCertificate
        (etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s)
        (etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s) :=
  etaCriticalMirrorLeftNormalizedAbelClosureDecision hs him

end DkMath.RH.CFBRCProjection
