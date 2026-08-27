/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectDecay
import Mathlib.Tactic

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedDefectDecay"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedDefectDecay

open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Analytic

example (s : ℂ) (m : ℕ) :
    etaCriticalMirrorDefectTerm s m =
      etaSignedVector (criticalMirror s) m - etaSignedVector s m :=
  etaCriticalMirrorDefectTerm_eq_mirror_sub_original s m

example (s : ℂ) (k : ℕ) :
    etaCriticalMirrorDefectPairTerm s k =
      etaPairTerm (criticalMirror s) k - etaPairTerm s k :=
  etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub s k

example (K : ℕ) (s : ℂ) :
    etaCriticalMirrorDefectPairedPartial K s =
      etaPairedPartial K (criticalMirror s) - etaPairedPartial K s :=
  etaCriticalMirrorDefectPairedPartial_eq_etaPairedPartial_sub K s

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
      ‖criticalMirror s‖ *
          (((2 * k + 1 : ℕ) : ℝ) ^ (-(criticalMirror s).re - 1)) +
        ‖s‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
  norm_etaCriticalMirrorDefectPairTerm_le_one_extra_decay_of_nontrivialRiemannZetaZero
    hs k

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedDefectDecay
