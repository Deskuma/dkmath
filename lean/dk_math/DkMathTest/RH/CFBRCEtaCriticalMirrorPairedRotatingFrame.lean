/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedRotatingFrame

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedRotatingFrame"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedRotatingFrame

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic
open DkMath.RH.CFBRCProjection

example (s : ℂ) (k : ℕ) :
    ‖etaPairBaseRotation s k‖ = 1 :=
  norm_etaPairBaseRotation s k

example (s : ℂ) (k : ℕ) (x : ℝ) :
    ‖etaPairResidualRotation s k x‖ = 1 :=
  norm_etaPairResidualRotation s k x

example (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k) :
    |etaPairResidualPhase s k x| ≤
      etaPairDerivativePhaseSpan s k :=
  abs_etaPairResidualPhase_le_phaseSpan s k hleft hright

example (s : ℂ) (k : ℕ) {x : ℝ}
    (hleft : etaPairFrameLeftEndpoint k ≤ x)
    (hright : x ≤ etaPairFrameRightEndpoint k)
    (hspan : etaPairDerivativePhaseSpan s k < Real.pi / 2) :
    0 < (etaPairResidualRotation s k x).re :=
  etaPairResidualRotation_re_pos_of_span_lt_pi_div_two
    s k hleft hright hspan

example (s : ℂ) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        0 < (etaPairResidualRotation s k x).re :=
  eventually_etaPairResidualRotation_re_pos s

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedRotatingFrame
