/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedTailBound"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedTailBound

open DkMath.RH.CFBRCProjection

example {σ : ℝ} (hσ : 0 < σ) {K : ℕ} (hK : 1 ≤ K) :
    (∑' j : ℕ,
      (((j + K + 1 : ℕ) : ℝ) ^ (-σ - 1))) ≤
      ((K : ℝ) ^ (-σ)) / σ :=
  shifted_rpow_tail_le hσ hK

example {s : ℂ} (hs : 0 < s.re)
    (hm : 0 < (criticalMirror s).re) (k : ℕ) :
    ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
      etaCriticalMirrorDefectPairMajorant s k :=
  norm_etaCriticalMirrorDefectPairTerm_le_majorant hs hm k

example {s : ℂ} (hs : 0 < s.re)
    (hm : 0 < (criticalMirror s).re) :
    Summable (etaCriticalMirrorDefectPairMajorant s) :=
  summable_etaCriticalMirrorDefectPairMajorant hs hm

example {s : ℂ} (hs : 0 < s.re)
    (hm : 0 < (criticalMirror s).re)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖etaCriticalMirrorDefectPairTail K s‖ ≤
      ‖criticalMirror s‖ *
          (((K : ℝ) ^ (-(criticalMirror s).re)) /
            (criticalMirror s).re) +
        ‖s‖ * (((K : ℝ) ^ (-s.re)) / s.re) :=
  norm_etaCriticalMirrorDefectPairTail_le hs hm hK

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedTailBound
