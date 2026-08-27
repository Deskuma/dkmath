/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePowerTailAbelian
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportReduction
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedSineTransportTailLimit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Right-side normalized sine-transport tail constant. -/
noncomputable def etaCriticalMirrorRightNormalizedSineTransportTailConstant
    (s : ℂ) : ℝ :=
  etaCriticalMirrorRightNormalizedSineTransportTermConstant s /
    (criticalMirror s).re

/-- Left-side normalized sine-transport tail constant. -/
noncomputable def etaCriticalMirrorLeftNormalizedSineTransportTailConstant
    (s : ℂ) : ℝ :=
  etaCriticalMirrorLeftNormalizedSineTransportTermConstant s / s.re

/--
Right of the critical line, the normalized sine-transport tail converges to
its explicit negative Abelian constant.
-/
theorem etaCriticalMirrorRightNormalizedSineTransportTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s)
      atTop
      (nhds (etaCriticalMirrorRightNormalizedSineTransportTailConstant s)) := by
  have halpha : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  have hsum :
      Summable
        (etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s) :=
    summable_etaCriticalMirrorPairedFrameCorrectionSineTransportTerm hs him
  have hterm :=
    etaCriticalMirrorRightNormalizedSineTransportTerm_tendsto_constant
      hs him hre
  have htail :=
    normalized_realSequenceTail_tendsto
      (a := etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s)
      (alpha := (criticalMirror s).re)
      (D := etaCriticalMirrorRightNormalizedSineTransportTermConstant s)
      halpha hsum hterm
  simpa [etaCriticalMirrorRightNormalizedSineTransportTailConstant,
    realSequenceTail,
    etaCriticalMirrorPairedFrameCorrectionSineTransportTail] using htail

/--
Left of the critical line, the normalized sine-transport tail converges to
its explicit positive Abelian constant.
-/
theorem etaCriticalMirrorLeftNormalizedSineTransportTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s)
      atTop
      (nhds (etaCriticalMirrorLeftNormalizedSineTransportTailConstant s)) := by
  have halpha : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hsum :
      Summable
        (etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s) :=
    summable_etaCriticalMirrorPairedFrameCorrectionSineTransportTerm hs him
  have hterm :=
    etaCriticalMirrorLeftNormalizedSineTransportTerm_tendsto_constant
      hs him hre
  have htail :=
    normalized_realSequenceTail_tendsto
      (a := etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s)
      (alpha := s.re)
      (D := etaCriticalMirrorLeftNormalizedSineTransportTermConstant s)
      halpha hsum hterm
  simpa [etaCriticalMirrorLeftNormalizedSineTransportTailConstant,
    realSequenceTail,
    etaCriticalMirrorPairedFrameCorrectionSineTransportTail] using htail

/-- The right normalized sine-transport tail constant is strictly negative. -/
theorem etaCriticalMirrorRightNormalizedSineTransportTailConstant_neg
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    etaCriticalMirrorRightNormalizedSineTransportTailConstant s < 0 := by
  have halpha : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  have himsq : 0 < s.im ^ 2 := sq_pos_of_ne_zero him
  have hconstant :
      0 < etaPairIndexNormalizedTailConstantReal (criticalMirror s) :=
    etaPairIndexNormalizedTailConstantReal_pos (criticalMirror s)
  have hterm :
      etaCriticalMirrorRightNormalizedSineTransportTermConstant s < 0 := by
    unfold etaCriticalMirrorRightNormalizedSineTransportTermConstant
    exact neg_lt_zero.mpr (mul_pos himsq hconstant)
  unfold etaCriticalMirrorRightNormalizedSineTransportTailConstant
  exact div_neg_of_neg_of_pos hterm halpha

/-- The left normalized sine-transport tail constant is strictly positive. -/
theorem etaCriticalMirrorLeftNormalizedSineTransportTailConstant_pos
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    0 < etaCriticalMirrorLeftNormalizedSineTransportTailConstant s := by
  have halpha : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have himsq : 0 < s.im ^ 2 := sq_pos_of_ne_zero him
  have hconstant :
      0 < etaPairIndexNormalizedTailConstantReal s :=
    etaPairIndexNormalizedTailConstantReal_pos s
  have hterm :
      0 < etaCriticalMirrorLeftNormalizedSineTransportTermConstant s := by
    unfold etaCriticalMirrorLeftNormalizedSineTransportTermConstant
    exact mul_pos himsq hconstant
  unfold etaCriticalMirrorLeftNormalizedSineTransportTailConstant
  exact div_pos hterm halpha

end DkMath.RH.CFBRCProjection
