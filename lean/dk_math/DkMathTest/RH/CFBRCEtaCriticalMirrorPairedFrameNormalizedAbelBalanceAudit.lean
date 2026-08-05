import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedAbelBalanceAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedAbelBalanceAudit"

noncomputable section
namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPredecessorFrameWholeTailProjection (K + 1) s)
      atTop (nhds 0) :=
  etaCriticalMirrorRightSuccessorIndexNormalizedPredecessorWholeTailProjection_tendsto_zero
    hs hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorRotatedDefectProjectionTail (K + 1) s)
      atTop
      (nhds
        (etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s)) :=
  etaCriticalMirrorRightSuccessorIndexNormalizedMovingProjectionTail_tendsto_constant
    hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        (((K + 1 : ℕ) : ℝ) ^ s.re) *
          etaCriticalMirrorRotatedDefectProjectionTail (K + 1) s)
      atTop
      (nhds
        (etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s)) :=
  etaCriticalMirrorLeftSuccessorIndexNormalizedMovingProjectionTail_tendsto_constant
    hs him hre

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (q : ℝ) (K : ℕ) :
    (((K + 1 : ℕ) : ℝ) ^ q) *
        etaCriticalMirrorPredecessorFrameWholeTailProjection (K + 1) s =
      (((K + 1 : ℕ) : ℝ) ^ q) *
          etaCriticalMirrorRotatedDefectProjectionTail (K + 1) s +
        (((K + 1 : ℕ) : ℝ) ^ q) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTail K s :=
  etaCriticalMirrorSuccessorIndexNormalizedAbelBalance_eq hs him q K

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    0 < etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s ∧
      etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s < 0 ∧
      etaCriticalMirrorRightNormalizedMovingProjectionTailConstant s +
          etaCriticalMirrorRightNormalizedCorrectionProjectionTailConstant s = 0 :=
  etaCriticalMirrorRightNormalizedAbelBalance_nonzero_cancellation hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s < 0 ∧
      0 < etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s ∧
      etaCriticalMirrorLeftNormalizedMovingProjectionTailConstant s +
          etaCriticalMirrorLeftNormalizedCorrectionProjectionTailConstant s = 0 :=
  etaCriticalMirrorLeftNormalizedAbelBalance_nonzero_cancellation hs him

end DkMath.RH.CFBRCProjection
