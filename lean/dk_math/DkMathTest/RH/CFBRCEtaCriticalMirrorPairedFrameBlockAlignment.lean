/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockAlignment

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockAlignment"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockAlignment

open Filter
open scoped BigOperators Topology
open DkMath.RH.CFBRCProjection

example
    (s : ℂ) (K N : ℕ) :
    (Finset.range N).sum
        (fun j : ℕ => etaPairFrameStepPhase s (K + j)) =
      s.im *
        (Real.log (etaPairFrameLeftEndpoint (K + N)) -
          Real.log (etaPairFrameLeftEndpoint K)) :=
  sum_range_etaPairFrameStepPhase_nat_add s K N

example
    (s : ℂ) (K N : ℕ) :
    etaPairFrameBlockSpan s K N =
      |s.im| *
        (Real.log (etaPairFrameLeftEndpoint (K + N)) -
          Real.log (etaPairFrameLeftEndpoint K)) :=
  etaPairFrameBlockSpan_eq s K N

example
    (s : ℂ) (N : ℕ) :
    Tendsto
      (fun K : ℕ => etaPairFrameBlockSpan s K N)
      atTop (nhds 0) :=
  etaPairFrameBlockSpan_tendsto_zero s N

example
    (s : ℂ) (N : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      etaPairFrameBlockSpan s K N < Real.pi / 2 :=
  eventually_etaPairFrameBlockSpan_lt_pi_div_two s N

example
    (s : ℂ) (K N : ℕ) :
    etaPairFrameBlockRotation s K N =
      Complex.exp
        (Complex.I *
          ((((Finset.range N).sum
            (fun j : ℕ => etaPairFrameStepPhase s (K + j)) : ℝ) : ℂ))) :=
  etaPairFrameBlockRotation_eq_exp s K N

example
    (s : ℂ) (K N : ℕ) :
    ‖etaPairFrameBlockRotation s K N‖ = 1 :=
  norm_etaPairFrameBlockRotation s K N

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockAlignment
