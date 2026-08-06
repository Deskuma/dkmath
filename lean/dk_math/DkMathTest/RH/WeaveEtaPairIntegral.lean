/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairIntegral

#print "file: DkMathTest.RH.WeaveEtaPairIntegral"

noncomputable section

namespace DkMathTest.RH.WeaveEtaPairIntegral

open MeasureTheory
open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Analytic

example {s : ℂ} (hs : s ≠ 0) (k : ℕ) :
    etaPairTerm s k =
      ∫ x : ℝ in (((2 * k + 1 : ℕ) : ℝ))..
          (((2 * k + 2 : ℕ) : ℝ)),
        etaPairIntegralKernel s x :=
  etaPairTerm_eq_intervalIntegral hs k

example (s : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (etaPairIntegralKernel s) volume a b :=
  etaPairIntegralKernel_intervalIntegrable s ha hab

end DkMathTest.RH.WeaveEtaPairIntegral
