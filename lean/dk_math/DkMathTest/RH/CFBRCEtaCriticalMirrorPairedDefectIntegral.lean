/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectIntegral

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedDefectIntegral"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedDefectIntegral

open MeasureTheory
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (k : ℕ) :
    etaCriticalMirrorDefectPairTerm s k =
      ∫ x : ℝ in (((2 * k + 1 : ℕ) : ℝ))..
          (((2 * k + 2 : ℕ) : ℝ)),
        etaCriticalMirrorDefectPairIntegralKernel s x :=
  etaCriticalMirrorDefectPairTerm_eq_intervalIntegral hs hm k

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorDefectPairTerm s k =
      ∫ x : ℝ in (((2 * k + 1 : ℕ) : ℝ))..
          (((2 * k + 2 : ℕ) : ℝ)),
        etaCriticalMirrorDefectPairIntegralKernel s x :=
  etaCriticalMirrorDefectPairTerm_eq_intervalIntegral_of_nontrivialRiemannZetaZero
    hs k

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedDefectIntegral
