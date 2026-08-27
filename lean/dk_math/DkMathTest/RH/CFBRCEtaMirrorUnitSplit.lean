/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaMirrorUnitSplit

#print "file: DkMathTest.RH.CFBRCEtaMirrorUnitSplit"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaMirrorUnitSplit

open DkMath.Algebra.MetallicRatioCore
open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Analytic

example (s : ℂ) (m : ℕ) :
    (etaMirrorAmplitudePair s m).x =
      ‖etaSignedVector (criticalMirror s) m‖ := by
  rfl

example (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeBig s m =
      etaMirrorAmplitudeGap s m +
        4 * etaMirrorAmplitudeProduct s m := by
  exact etaMirrorAmplitudeBig_eq_gap_add_four_mul_product s m

example (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeGap s m = 0 ↔
      etaMirrorAmplitudeRatio s m = 1 := by
  exact etaMirrorAmplitudeGap_eq_zero_iff_ratio_eq_one s m

example (s : ℂ) (m : ℕ) :
    (etaMirrorUnitPair s m).product = 1 := by
  exact etaMirrorUnitPair_product_eq_one s m

example (s : ℂ) (m : ℕ) :
    etaMirrorUnitBig s m = etaMirrorUnitGap s m + 4 := by
  exact etaMirrorUnitBig_eq_gap_add_four s m

example (s : ℂ) (m : ℕ) :
    etaMirrorUnitGap s m = 0 ↔
      etaMirrorAmplitudeGap s m = 0 := by
  exact etaMirrorUnitGap_eq_zero_iff_amplitudeGap_eq_zero s m

end DkMathTest.RH.CFBRCEtaMirrorUnitSplit
