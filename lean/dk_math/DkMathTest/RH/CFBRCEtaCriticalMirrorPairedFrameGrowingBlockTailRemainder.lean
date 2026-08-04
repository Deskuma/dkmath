import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGrowingBlockTailRemainder

open Filter
open scoped BigOperators Topology
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hsum : Summable (etaCriticalMirrorDefectPairTerm s))
    (K N : ℕ) :
    etaCriticalMirrorDefectPairTail K s =
      (Finset.range N).sum
          (fun j : ℕ => etaCriticalMirrorDefectPairTerm s (K + j)) +
        etaCriticalMirrorDefectPairTail (K + N) s :=
  etaCriticalMirrorDefectPairTail_eq_block_add_tail hsum K N

example {s : ℂ} (hsum : Summable (etaCriticalMirrorDefectPairTerm s))
    (K N : ℕ) :
    etaCriticalMirrorBlockStartWholeTailProjection s K =
      etaCriticalMirrorBlockStartDefectBlockProjection s K N +
        etaCriticalMirrorBlockStartResidualTailProjection s K N :=
  etaCriticalMirrorBlockStartWholeTailProjection_eq_block_add_residual
    hsum K N

example {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
    {K N : ℕ} (hKN : 1 ≤ K + N) :
    |etaCriticalMirrorBlockStartResidualTailProjection s K N| ≤
      etaCriticalMirrorBlockStartResidualTailPowerBound s K N :=
  abs_etaCriticalMirrorBlockStartResidualTailProjection_le_powerBound
    hs hm hKN

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    ∀ᶠ K : ℕ in atTop,
      |etaCriticalMirrorBlockStartResidualTailProjection
          s K (S.blockLength K)| ≤
        etaCriticalMirrorBlockStartResidualTailPowerBound
          s K (S.blockLength K) :=
  EtaPairGrowingBlockSchedule.eventually_abs_blockStartResidualTailProjection_le_powerBound
    S hs

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightResidualTailDominated s) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorBlockStartWholeTailProjection s K :=
  EtaPairGrowingBlockSchedule.eventually_blockStartWholeTailProjection_pos_of_rightResidualTailDominated
    S hs him hre hdom

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftResidualTailDominated s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorBlockStartWholeTailProjection s K < 0 :=
  EtaPairGrowingBlockSchedule.eventually_blockStartWholeTailProjection_neg_of_leftResidualTailDominated
    S hs him hre hdom

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGrowingBlockTailRemainder
