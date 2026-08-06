/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailChordCollapseCriterion

set_option linter.style.longLine false

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDefectTailChordCollapseCriterion"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    {a : ℝ} {s C : ℂ}
    (cert :
      EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate a s C) :
    ¬ EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse a s :=
  not_etaCriticalMirrorTwoScaleNormalizedDefectTailChordCollapse_of_certificate
    cert

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hcollapse : EtaCriticalMirrorZeroLocusTwoScaleChordCollapse s) :
    s.re = (1 : ℝ) / 2 :=
  re_eq_half_of_nontrivialRiemannZetaZero_of_twoScaleChordCollapse
    hs him hcollapse

example
    {d : ℕ} (hd : 0 < d) {s : ℂ} (Θ : ℝ)
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hcollapse : EtaCriticalMirrorZeroLocusTwoScaleChordCollapse s) :
    offCriticalCFBRC d s.re Θ = 0 :=
  offCriticalCFBRC_eq_zero_of_nontrivialRiemannZetaZero_of_twoScaleChordCollapse
    hd Θ hs him hcollapse

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    ¬ EtaCriticalMirrorZeroLocusTwoScaleChordCollapse s :=
  not_etaCriticalMirrorZeroLocusTwoScaleChordCollapse_of_offCriticalZero
    hs him hre

end DkMathTest.RH.CFBRCProjection
