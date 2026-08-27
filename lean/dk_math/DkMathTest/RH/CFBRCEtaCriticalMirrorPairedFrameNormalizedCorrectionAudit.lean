/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCorrectionAudit"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCorrectionAudit

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (s : ℂ) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K =
      etaCriticalMirrorCorrectionMirrorProjectionConstant s *
          ((K : ℝ) ^ (-(criticalMirror s).re)) +
        etaCriticalMirrorCorrectionOriginalProjectionConstant s *
          ((K : ℝ) ^ (-s.re)) :=
  etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound_eq_constants s K

example (s : ℂ) :
    ∀ᶠ K : ℕ in atTop,
      ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K =
        etaCriticalMirrorRightIndexNormalizedCorrectionPowerAudit s K :=
  eventually_etaCriticalMirrorRightIndexNormalizedCorrectionPowerBound_eq_audit s

example (s : ℂ) :
    ∀ᶠ K : ℕ in atTop,
      ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K =
        etaCriticalMirrorLeftIndexNormalizedCorrectionPowerAudit s K :=
  eventually_etaCriticalMirrorLeftIndexNormalizedCorrectionPowerBound_eq_audit s

example {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (etaCriticalMirrorRightIndexNormalizedCorrectionPowerAudit s)
      atTop
      (nhds (etaCriticalMirrorCorrectionMirrorProjectionConstant s)) :=
  etaCriticalMirrorRightIndexNormalizedCorrectionPowerAudit_tendsto hre

example {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (etaCriticalMirrorLeftIndexNormalizedCorrectionPowerAudit s)
      atTop
      (nhds (etaCriticalMirrorCorrectionOriginalProjectionConstant s)) :=
  etaCriticalMirrorLeftIndexNormalizedCorrectionPowerAudit_tendsto hre

example {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K)
      atTop
      (nhds (etaCriticalMirrorCorrectionMirrorProjectionConstant s)) :=
  etaCriticalMirrorRightIndexNormalizedCorrectionPowerBound_tendsto hre

example {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K)
      atTop
      (nhds (etaCriticalMirrorCorrectionOriginalProjectionConstant s)) :=
  etaCriticalMirrorLeftIndexNormalizedCorrectionPowerBound_tendsto hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCorrectionAudit
