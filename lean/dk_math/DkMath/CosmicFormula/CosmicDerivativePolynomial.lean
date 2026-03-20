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

/-- Additive operation API in `HasDerivAt` form. -/
theorem hasDerivAt_polynomial_eval_add_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (p + q).eval y)
      (p.derivative.eval x + q.derivative.eval x) x := by
  simpa [Polynomial.eval_add, Polynomial.derivative_add] using
    (hasDerivAt_polynomial_eval_cosmic (p := p + q) (x := x))

/-- Additive operation API in cosmic-kernel limit form. -/
theorem tendsto_cosmicKernel_polynomial_eval_add
    (p q : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => (p + q).eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x + q.derivative.eval x)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_polynomial_eval_add_cosmic p q x)

/-- Additive operation API in `deriv` form. -/
theorem deriv_polynomial_eval_add_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => (p + q).eval y) x =
      p.derivative.eval x + q.derivative.eval x := by
  simpa using (hasDerivAt_polynomial_eval_add_cosmic p q x).deriv

/-- Multiplicative operation API in `HasDerivAt` form. -/
theorem hasDerivAt_polynomial_eval_mul_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (p * q).eval y)
      (p.derivative.eval x * q.eval x + p.eval x * q.derivative.eval x) x := by
  simpa [Polynomial.eval_mul, Polynomial.derivative_mul] using
    (hasDerivAt_polynomial_eval_cosmic (p := p * q) (x := x))

/-- Multiplicative operation API in cosmic-kernel limit form. -/
theorem tendsto_cosmicKernel_polynomial_eval_mul
    (p q : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => (p * q).eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x * q.eval x + p.eval x * q.derivative.eval x)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_polynomial_eval_mul_cosmic p q x)

/-- Multiplicative operation API in `deriv` form. -/
theorem deriv_polynomial_eval_mul_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => (p * q).eval y) x =
      p.derivative.eval x * q.eval x + p.eval x * q.derivative.eval x := by
  simpa using (hasDerivAt_polynomial_eval_mul_cosmic p q x).deriv

/-- Compositional operation API in `HasDerivAt` form. -/
theorem hasDerivAt_polynomial_eval_comp_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (p.comp q).eval y)
      (p.derivative.eval (q.eval x) * q.derivative.eval x) x := by
  simpa [Polynomial.eval_comp, Polynomial.derivative_comp, Polynomial.eval_mul,
    mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_polynomial_eval_cosmic (p := p.comp q) (x := x))

/-- Compositional operation API in cosmic-kernel limit form. -/
theorem tendsto_cosmicKernel_polynomial_eval_comp
    (p q : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => (p.comp q).eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval (q.eval x) * q.derivative.eval x)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_polynomial_eval_comp_cosmic p q x)

/-- Compositional operation API in `deriv` form. -/
theorem deriv_polynomial_eval_comp_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => (p.comp q).eval y) x =
      p.derivative.eval (q.eval x) * q.derivative.eval x := by
  simpa using (hasDerivAt_polynomial_eval_comp_cosmic p q x).deriv

/-- Finite-sum polynomial generalization in `HasDerivAt` form. -/
theorem hasDerivAt_polynomial_eval_finset_sum_cosmic
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Finset.sum s (fun i => (P i).eval y))
      (Finset.sum s (fun i => ((P i).derivative).eval x)) x := by
  simpa [Polynomial.eval_finset_sum, Polynomial.derivative_sum] using
    (hasDerivAt_polynomial_eval_cosmic (p := Finset.sum s P) (x := x))

/-- Finite-sum polynomial generalization in cosmic-kernel limit form. -/
theorem tendsto_cosmicKernel_polynomial_eval_finset_sum
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto
      (fun u : ℝ => cosmicKernel (fun y : ℝ => Finset.sum s (fun i => (P i).eval y)) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (Finset.sum s (fun i => ((P i).derivative).eval x))) := by
  exact tendsto_cosmicKernel_of_hasDerivAt
    (hasDerivAt_polynomial_eval_finset_sum_cosmic (s := s) (P := P) (x := x))

/-- Finite-sum polynomial generalization in `deriv` form. -/
theorem deriv_polynomial_eval_finset_sum_cosmic
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => Finset.sum s (fun i => (P i).eval y)) x =
      Finset.sum s (fun i => ((P i).derivative).eval x) := by
  simpa using
    (hasDerivAt_polynomial_eval_finset_sum_cosmic (s := s) (P := P) (x := x)).deriv

end DkMath.CosmicFormula
