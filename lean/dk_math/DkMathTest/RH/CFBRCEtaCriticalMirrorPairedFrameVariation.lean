/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameVariation

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameVariation"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameVariation

open Filter
open scoped BigOperators Topology
open DkMath.RH.CFBRCProjection

example (s : ℂ) (K : ℕ) :
    (Finset.range K).sum (etaPairFrameStepPhase s) =
      s.im * Real.log (etaPairFrameLeftEndpoint K) :=
  sum_range_etaPairFrameStepPhase_eq_im_mul_log s K

example (s : ℂ) (K : ℕ) :
    (Finset.range K).sum (etaPairFrameStepSpan s) =
      |s.im| * Real.log (etaPairFrameLeftEndpoint K) :=
  sum_range_etaPairFrameStepSpan_eq_abs_im_mul_log s K

example :
    Tendsto etaPairFrameLeftEndpoint atTop atTop :=
  etaPairFrameLeftEndpoint_tendsto_atTop

example {s : ℂ} (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        (Finset.range K).sum (etaPairFrameStepSpan s))
      atTop atTop :=
  etaPairFrameStepSpanPartial_tendsto_atTop_of_im_ne_zero him

example {s : ℂ} (him : s.im ≠ 0) :
    ¬ Summable (etaPairFrameStepSpan s) :=
  not_summable_etaPairFrameStepSpan_of_im_ne_zero him

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameVariation
