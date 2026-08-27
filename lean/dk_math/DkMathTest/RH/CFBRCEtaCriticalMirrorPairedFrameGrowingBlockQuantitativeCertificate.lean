import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate

open Filter
open scoped BigOperators Topology
open DkMath.RH.CFBRCProjection

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        16 * etaCriticalMirrorDefectPairNormCoefficient s *
            etaPairFrameBlockSpan s K j <
          |s.im| :=
  EtaPairGrowingBlockSchedule.eventually_all_subblock_sixteen_mul_normCoefficient_mul_span_lt_abs_im
    S him

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < S.blockLength K →
        etaCriticalMirrorRightPairMargin s (K + j) / 2 <
          etaCriticalMirrorBlockStartDefectPairProjection s K j :=
  EtaPairGrowingBlockSchedule.eventually_all_rightPairMargin_div_two_lt_blockStartProjection
    S hs him hre

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < S.blockLength K →
        etaCriticalMirrorLeftPairMargin s (K + j) / 2 <
          -etaCriticalMirrorBlockStartDefectPairProjection s K j :=
  EtaPairGrowingBlockSchedule.eventually_all_leftPairMargin_div_two_lt_neg_blockStartProjection
    S hs him hre

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      (1 : ℝ) / 2 *
          etaCriticalMirrorRightBlockMarginSum s K (S.blockLength K) <
        etaCriticalMirrorBlockStartDefectBlockProjection
          s K (S.blockLength K) :=
  EtaPairGrowingBlockSchedule.eventually_half_rightBlockMarginSum_lt_blockStartProjection
    S hs him hre

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      (1 : ℝ) / 2 *
          etaCriticalMirrorLeftBlockMarginSum s K (S.blockLength K) <
        -etaCriticalMirrorBlockStartDefectBlockProjection
          s K (S.blockLength K) :=
  EtaPairGrowingBlockSchedule.eventually_half_leftBlockMarginSum_lt_neg_blockStartProjection
    S hs him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate
