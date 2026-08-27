/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaKUSMirrorUnitBridge

#print "file: DkMathTest.RH.CFBRCEtaKUSMirrorUnitBridge"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaKUSMirrorUnitBridge

open DkMath.KUS
open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Analytic
open DkMath.RH.Weave.Finite

example (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) :
    etaKUSMirrorUnitGap x 1 = 0 ↔
      x.unit.point.re = (1 : ℝ) / 2 := by
  exact etaKUSMirrorUnitGap_one_eq_zero_iff_re_eq_half x

example
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0)
    (m : ℕ) :
    etaKUSMirrorUnitGap (etaKUSState N s ω hTotal) m =
      etaKUSMirrorUnitGap (etaKUSZeroState N s ω hTotal) m := by
  exact etaKUSMirrorUnitGap_state_eq_zeroState N s ω hTotal m

example
    (c : ℂ) (S : US EtaKUSUnit EtaKUSBlueprint) (m : ℕ) :
    etaKUSMirrorUnitBig (mkGWith c S) m =
      etaKUSMirrorUnitBig (gZeroState (C := ℂ) S) m := by
  exact etaKUSMirrorUnitBig_mkGWith_eq_gZeroState c S m

example (N : ℕ) (s : ℂ) (m : ℕ) :
    etaKUSMirrorUnitGap (etaUnitKUSState N s) m =
      etaKUSMirrorUnitGap (etaUnitKUSZeroState N s) m := by
  exact etaKUSMirrorUnitGap_etaUnit_state_eq_zeroState N s m

end DkMathTest.RH.CFBRCEtaKUSMirrorUnitBridge
