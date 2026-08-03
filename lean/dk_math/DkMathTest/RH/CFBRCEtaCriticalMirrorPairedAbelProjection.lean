/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjection

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelProjection"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial K s <
        etaCriticalMirrorRotatedDefectProjectionPartial (K + 1) s :=
  eventually_etaCriticalMirrorRotatedDefectProjectionPartial_lt_succ_of_half_lt_re
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial (K + 1) s <
        etaCriticalMirrorRotatedDefectProjectionPartial K s :=
  eventually_etaCriticalMirrorRotatedDefectProjectionPartial_succ_lt_of_re_lt_half
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorRotatedDefectProjectionPartial K s)
      atTop
      (nhds
        (etaCriticalMirrorSignedVerticalProjection s
          (-(∑' k : ℕ,
            etaCriticalMirrorPairedFrameCorrectionTerm s k)))) :=
  etaCriticalMirrorRotatedDefectProjectionPartial_tendsto_neg_correction_projection
    hs him

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelProjection
