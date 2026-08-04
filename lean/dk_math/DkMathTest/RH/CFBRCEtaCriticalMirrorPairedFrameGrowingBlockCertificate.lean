import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockCertificate

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGrowingBlockCertificate

open Filter
open DkMath.RH.CFBRCProjection

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < S.blockLength K →
        0 < etaCriticalMirrorBlockStartDefectPairProjection s K j :=
  EtaPairGrowingBlockSchedule.eventually_all_blockStartDefectPairProjection_pos_of_half_lt_re
      S hs him hre

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < S.blockLength K →
        etaCriticalMirrorBlockStartDefectPairProjection s K j < 0 :=
  EtaPairGrowingBlockSchedule.eventually_all_blockStartDefectPairProjection_neg_of_re_lt_half
      S hs him hre

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorBlockStartDefectBlockProjection
        s K (S.blockLength K) :=
  EtaPairGrowingBlockSchedule.eventually_blockStartDefectBlockProjection_pos_of_half_lt_re
      S hs him hre

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorBlockStartDefectBlockProjection
        s K (S.blockLength K) < 0 :=
  EtaPairGrowingBlockSchedule.eventually_blockStartDefectBlockProjection_neg_of_re_lt_half
      S hs him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGrowingBlockCertificate
