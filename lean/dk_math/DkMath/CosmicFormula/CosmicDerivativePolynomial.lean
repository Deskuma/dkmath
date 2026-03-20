/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

import DkMath.CosmicFormula.CosmicDerivativePowerLimit

#print "file: DkMath.CosmicFormula.CosmicDerivativePolynomial"

namespace DkMath.CosmicFormula

/-- Polynomial evaluation has the expected derivative in cosmic notation. -/
theorem hasDerivAt_polynomial_eval_cosmic (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval y) (p.derivative.eval x) x := by
  simpa using (p.hasDerivAt x)

/-- Cosmic-kernel limit form for polynomial evaluation. -/
theorem tendsto_cosmicKernel_polynomial_eval (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => p.eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_polynomial_eval_cosmic p x)

/-- `deriv` form of the polynomial-evaluation derivative theorem. -/
theorem deriv_polynomial_eval_cosmic (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => p.eval y) x = p.derivative.eval x := by
  simp [p.deriv (x := x)]

/-- Finite-sum polynomial generalization in `HasDerivAt` form. -/
theorem hasDerivAt_polynomial_eval_finset_sum_cosmic
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Finset.sum s (fun i => (P i).eval y))
      (Finset.sum s (fun i => ((P i).derivative).eval x)) x := by
  simpa [Polynomial.eval_finset_sum, Polynomial.derivative_sum] using
    (hasDerivAt_polynomial_eval_cosmic (p := Finset.sum s P) (x := x))

end DkMath.CosmicFormula
