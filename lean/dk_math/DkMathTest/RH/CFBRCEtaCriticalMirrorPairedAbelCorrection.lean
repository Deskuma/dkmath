/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelCorrection

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelCorrection"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelCorrection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (σ : ℝ) (k : ℕ) :
    (1 / (((k + 1 : ℕ) : ℝ))) *
        (((k + 1 : ℕ) : ℝ) ^ (-σ)) =
      (((k + 1 : ℕ) : ℝ) ^ (-σ - 1)) :=
  one_div_nat_succ_mul_rpow_neg_eq σ k

example {s : ℂ} (hs : 0 < s.re)
    (hm : 0 < (criticalMirror s).re) :
    Summable (etaCriticalMirrorPairedFrameCorrectionMajorant s) :=
  summable_etaCriticalMirrorPairedFrameCorrectionMajorant hs hm

example (s : ℂ) (k : ℕ) :
    |s.im| / etaPairFrameLeftEndpoint k ≤
      |s.im| / (((k + 1 : ℕ) : ℝ)) :=
  abs_im_div_etaPairFrameLeftEndpoint_le_succ s k

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ)
    (hspan : etaPairFrameStepSpan s k ≤ 1) :
    ‖etaCriticalMirrorPairedFrameCorrectionTerm s k‖ ≤
      etaCriticalMirrorPairedFrameCorrectionMajorant s k :=
  norm_etaCriticalMirrorPairedFrameCorrectionTerm_le_majorant
    hs him k hspan

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      ‖etaCriticalMirrorPairedFrameCorrectionTerm s k‖ ≤
        etaCriticalMirrorPairedFrameCorrectionMajorant s k :=
  eventually_norm_etaCriticalMirrorPairedFrameCorrectionTerm_le_majorant
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Summable (etaCriticalMirrorPairedFrameCorrectionTerm s) :=
  summable_etaCriticalMirrorPairedFrameCorrectionTerm_of_nontrivialRiemannZetaZero
    hs him

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelCorrection
