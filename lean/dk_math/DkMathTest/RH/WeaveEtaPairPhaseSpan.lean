/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairPhaseSpan

#print "file: DkMathTest.RH.WeaveEtaPairPhaseSpan"

noncomputable section

namespace DkMathTest.RH.WeaveEtaPairPhaseSpan

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

example (s : ℂ) (k : ℕ) :
    0 ≤ etaPairDerivativePhaseSpan s k :=
  etaPairDerivativePhaseSpan_nonneg s k

example (s : ℂ) (k : ℕ) :
    etaPairDerivativePhaseSpan s k ≤
      |s.im| / (((2 * k + 1 : ℕ) : ℝ)) :=
  etaPairDerivativePhaseSpan_le_inv s k

example (s : ℂ) :
    Tendsto (fun k : ℕ => etaPairDerivativePhaseSpan s k)
      atTop (nhds 0) :=
  etaPairDerivativePhaseSpan_tendsto_zero s

example (s : ℂ) :
    ∀ᶠ k : ℕ in atTop,
      etaPairDerivativePhaseSpan s k < Real.pi / 2 :=
  eventually_etaPairDerivativePhaseSpan_lt_pi_div_two s

end DkMathTest.RH.WeaveEtaPairPhaseSpan
