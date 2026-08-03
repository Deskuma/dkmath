/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorContinuousWeightThreshold

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorContinuousWeightThreshold"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorContinuousWeightThreshold

open Filter
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      2 ≤ etaCriticalMirrorContinuousWeightR s
        (etaPairFrameLeftEndpoint k) :=
  eventually_two_le_etaCriticalMirrorContinuousWeightR_leftEndpoint_of_half_lt_re
    hre

example {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      etaCriticalMirrorContinuousWeightR s
        (etaPairFrameLeftEndpoint k) ≤ (1 : ℝ) / 2 :=
  eventually_etaCriticalMirrorContinuousWeightR_leftEndpoint_le_half_of_re_lt_half
    hre

example {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        2 ≤ etaCriticalMirrorContinuousWeightR s x :=
  eventually_two_le_etaCriticalMirrorContinuousWeightR_on_pair_of_half_lt_re
    hre

example {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        etaCriticalMirrorContinuousWeightR s x ≤ (1 : ℝ) / 2 :=
  eventually_etaCriticalMirrorContinuousWeightR_on_pair_le_half_of_re_lt_half
    hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorContinuousWeightThreshold
