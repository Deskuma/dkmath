/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimitSide

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelLimitSide"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelLimitSide

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorRotatedDefectProjectionPartial K s)
      atTop
      (nhds (etaCriticalMirrorRotatedDefectProjectionLimit s)) :=
  etaCriticalMirrorRotatedDefectProjectionPartial_tendsto_limit hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial K s <
        etaCriticalMirrorRotatedDefectProjectionLimit s :=
  eventually_etaCriticalMirrorRotatedDefectProjectionPartial_lt_limit_of_half_lt_re
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionLimit s <
        etaCriticalMirrorRotatedDefectProjectionPartial K s :=
  eventually_etaCriticalMirrorRotatedDefectProjectionLimit_lt_partial_of_re_lt_half
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorRotatedDefectProjectionLimitGap K s :=
  eventually_etaCriticalMirrorRotatedDefectProjectionLimitGap_pos_of_half_lt_re
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionLimitGap K s < 0 :=
  eventually_etaCriticalMirrorRotatedDefectProjectionLimitGap_neg_of_re_lt_half
    hs him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelLimitSide
