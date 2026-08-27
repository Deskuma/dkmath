/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjectionTail

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelProjectionTail"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelProjectionTail

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Summable
      (fun k : ℕ =>
        etaCriticalMirrorRotatedDefectPairProjection s k) :=
  summable_etaCriticalMirrorRotatedDefectPairProjection hs

example (K : ℕ) (s : ℂ) :
    etaCriticalMirrorRotatedDefectProjectionPartial K s =
      (Finset.range K).sum
        (etaCriticalMirrorRotatedDefectPairProjection s) :=
  etaCriticalMirrorRotatedDefectProjectionPartial_eq_sum_range K s

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    (∑' k : ℕ,
      etaCriticalMirrorRotatedDefectPairProjection s k) =
      etaCriticalMirrorRotatedDefectProjectionLimit s :=
  tsum_etaCriticalMirrorRotatedDefectPairProjection_eq_limit hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0)
    (K : ℕ) :
    etaCriticalMirrorRotatedDefectProjectionLimitGap K s =
      etaCriticalMirrorRotatedDefectProjectionTail K s :=
  etaCriticalMirrorRotatedDefectProjectionLimitGap_eq_tsum_nat_add hs him K

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorRotatedDefectProjectionTail K s :=
  eventually_etaCriticalMirrorRotatedDefectProjectionTail_pos_of_half_lt_re
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionTail K s < 0 :=
  eventually_etaCriticalMirrorRotatedDefectProjectionTail_neg_of_re_lt_half
    hs him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelProjectionTail
