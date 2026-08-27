/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedTail"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedTail

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : 0 < s.re)
    (hm : 0 < (criticalMirror s).re) :
    Summable (etaCriticalMirrorDefectPairTerm s) :=
  summable_etaCriticalMirrorDefectPairTerm hs hm

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Summable (etaCriticalMirrorDefectPairTerm s) :=
  summable_etaCriticalMirrorDefectPairTerm_of_nontrivialRiemannZetaZero hs

example {s : ℂ} (hsum : Summable (etaCriticalMirrorDefectPairTerm s))
    (K : ℕ) :
    etaCriticalMirrorDefectPairedPartial K s +
        etaCriticalMirrorDefectPairTail K s =
      ∑' k : ℕ, etaCriticalMirrorDefectPairTerm s k :=
  etaCriticalMirrorDefectPairedPartial_add_tail_eq_tsum hsum K

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => etaCriticalMirrorDefectPairedPartial K s)
      atTop (nhds 0) :=
  etaCriticalMirrorDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    (∑' k : ℕ, etaCriticalMirrorDefectPairTerm s k) = 0 :=
  tsum_etaCriticalMirrorDefectPairTerm_eq_zero_of_nontrivialRiemannZetaZero
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorDefectPairedPartial K s =
      -etaCriticalMirrorDefectPairTail K s :=
  etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
    hs him K

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedTail
