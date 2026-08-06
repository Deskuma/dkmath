/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaKUSMirrorGapBridgeAudit

#print "file: DkMathTest.RH.CFBRCEtaKUSMirrorGapBridgeAudit"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaKUSMirrorGapBridgeAudit

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (s : ℂ) :
    Tendsto (etaUnitKUSMirrorGapTrace s) atTop (nhds 0) ↔
      s.re = (1 : ℝ) / 2 := by
  exact etaUnitKUSMirrorGapTrace_tendsto_zero_iff_re_eq_half s

example {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    EtaKUSCoefficientMirrorGapCoupledAt s ↔
      s.re = (1 : ℝ) / 2 := by
  exact etaKUSCoefficientMirrorGapCoupledAt_iff_re_eq_half hre him hz

example :
    Nonempty StandardZetaEtaKUSMirrorGapZeroBridge ↔
      RiemannHypothesis := by
  exact nonempty_standardZetaEtaKUSMirrorGapZeroBridge_iff_riemannHypothesis

end DkMathTest.RH.CFBRCEtaKUSMirrorGapBridgeAudit
