/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelLimit"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelLimit

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example :
    Tendsto (fun K : ℕ => K + 1) atTop atTop :=
  tendsto_nat_succ_atTop

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ => etaCriticalMirrorPairedAbelBoundaryTerm K s)
      atTop (nhds 0) :=
  etaCriticalMirrorPairedAbelBoundaryTerm_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        (Finset.range K).sum
          (etaCriticalMirrorPairedFrameCorrectionTerm s))
      atTop
      (nhds
        (∑' k : ℕ,
          etaCriticalMirrorPairedFrameCorrectionTerm s k)) :=
  etaCriticalMirrorPairedFrameCorrectionPartial_tendsto_tsum_of_nontrivialRiemannZetaZero
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorRotatedDefectPairedPartial (K + 1) s)
      atTop
      (nhds
        (-(∑' k : ℕ,
          etaCriticalMirrorPairedFrameCorrectionTerm s k))) :=
  etaCriticalMirrorRotatedDefectPairedPartial_succ_tendsto_neg_correction_tsum
    hs him

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelLimit
