/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

import DkMath.CosmicFormula.CosmicDerivativePowerLimit

#print "file: DkMath.CosmicFormula.CosmicDerivativePolynomial"

namespace DkMath.CosmicFormula

/-- Polynomial evaluation derivative (legacy bridge via existing mathlib theorem).
Canonical theorem: `hasDerivAt_polynomial_eval_cosmic`. -/
theorem hasDerivAt_polynomial_eval_cosmic_from_mathlib (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval y) (p.derivative.eval x) x := by
  simpa using (p.hasDerivAt x)

/-- Cosmic-kernel limit form for polynomial evaluation (legacy bridge style).
Canonical theorem: `tendsto_cosmicKernel_polynomial_eval`. -/
theorem tendsto_cosmicKernel_polynomial_eval_from_hasDerivAt (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => p.eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_polynomial_eval_cosmic_from_mathlib p x)

/-- `deriv` form (legacy bridge via existing mathlib theorem).
Canonical theorem: `deriv_polynomial_eval_cosmic`. -/
theorem deriv_polynomial_eval_cosmic_from_mathlib (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => p.eval y) x = p.derivative.eval x := by
  simp [p.deriv (x := x)]

/-- Cosmic-kernel form for a scalar monomial function (punctured at `u = 0`). -/
theorem cosmicKernel_monomial_of_ne_zero
    (a x u : ℝ) (n : ℕ) (hu : u ≠ 0) :
    cosmicKernel (fun y : ℝ => a * y ^ n) x u = a * powerKernel n x u := by
  calc
    cosmicKernel (fun y : ℝ => a * y ^ n) x u
        = a * cosmicKernel (fun y : ℝ => y ^ n) x u := by
          simpa using (cosmicKernel_smul a (fun y : ℝ => y ^ n) x u)
    _ = a * powerKernel n x u := by
      rw [cosmicKernel_pow_eq_powerKernel_of_ne_zero n x u hu]

/-- `Polynomial.monomial` specialization of `cosmicKernel_monomial_of_ne_zero`. -/
theorem cosmicKernel_eval_monomial_of_ne_zero
    (a x u : ℝ) (n : ℕ) (hu : u ≠ 0) :
    cosmicKernel (fun y : ℝ => (Polynomial.monomial n a).eval y) x u
      = a * powerKernel n x u := by
  simpa [Polynomial.eval_monomial] using
    (cosmicKernel_monomial_of_ne_zero a x u n hu)

/-- Kernel-level expansion of a polynomial into a finite sum of monomial kernels. -/
theorem cosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernel_of_ne_zero
    (p : Polynomial ℝ) (x u : ℝ) (hu : u ≠ 0) :
    cosmicKernel (fun y : ℝ => p.eval y) x u
      = Finset.sum (Finset.range (p.natDegree + 1))
          (fun n => p.coeff n * powerKernel n x u) := by
  have hfun :
      (fun y : ℝ => p.eval y)
        = (fun y : ℝ =>
            Finset.sum (Finset.range (p.natDegree + 1))
              (fun n => p.coeff n * y ^ n)) := by
    funext y
    calc
      p.eval y
          = (Finset.sum (Finset.range (p.natDegree + 1))
              (fun n => Polynomial.C (p.coeff n) * Polynomial.X ^ n)).eval y := by
              exact congrArg (fun q : Polynomial ℝ => q.eval y) p.as_sum_range_C_mul_X_pow
      _ = Finset.sum (Finset.range (p.natDegree + 1))
            (fun n => (Polynomial.C (p.coeff n) * Polynomial.X ^ n).eval y) := by
            rw [Polynomial.eval_finset_sum]
      _ = Finset.sum (Finset.range (p.natDegree + 1))
            (fun n => p.coeff n * y ^ n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp
  rw [hfun]
  rw [cosmicKernel_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simpa using (cosmicKernel_monomial_of_ne_zero (a := p.coeff n) (x := x) (u := u) (n := n) hu)

/-- Continuous extension kernel for polynomial evaluation (explicitly including `u = 0`). -/
def polynomialKernelExt (p : Polynomial ℝ) (x u : ℝ) : ℝ :=
  Finset.sum (Finset.range (p.natDegree + 1)) (fun n => p.coeff n * powerKernel n x u)

/-- On `u ≠ 0`, `cosmicKernel` coincides with `polynomialKernelExt`. -/
theorem cosmicKernel_polynomial_eval_eq_polynomialKernelExt_of_ne_zero
    (p : Polynomial ℝ) (x u : ℝ) (hu : u ≠ 0) :
    cosmicKernel (fun y : ℝ => p.eval y) x u = polynomialKernelExt p x u := by
  simpa [polynomialKernelExt] using
    (cosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernel_of_ne_zero p x u hu)

/-- Range-sum form of `p.derivative.eval x` compatible with `polynomialKernelExt`. -/
theorem derivative_eval_eq_sum_range_coeff_mul_pow
    (p : Polynomial ℝ) (x : ℝ) :
    p.derivative.eval x
      = Finset.sum (Finset.range (p.natDegree + 1))
          (fun n => p.coeff n * ((n : ℝ) * x ^ (n - 1))) := by
  rw [Polynomial.derivative_eval]
  simpa [mul_assoc] using
    (p.sum_over_range
      (f := fun n a => a * (n : ℝ) * x ^ (n - 1))
      (h := by intro n; simp))

/-- `polynomialKernelExt` is continuous in `u`. -/
theorem continuous_polynomialKernelExt (p : Polynomial ℝ) (x : ℝ) :
    Continuous (fun u : ℝ => polynomialKernelExt p x u) := by
  unfold polynomialKernelExt
  refine continuous_finset_sum (s := Finset.range (p.natDegree + 1)) ?_
  intro n hn
  exact (continuous_const.mul (continuous_powerKernel n x))

/-- Evaluation of `polynomialKernelExt` at `u = 0`. -/
theorem polynomialKernelExt_zero (p : Polynomial ℝ) (x : ℝ) :
    polynomialKernelExt p x 0 = p.derivative.eval x := by
  unfold polynomialKernelExt
  calc
    Finset.sum (Finset.range (p.natDegree + 1))
      (fun n => p.coeff n * powerKernel n x 0)
        = Finset.sum (Finset.range (p.natDegree + 1))
            (fun n => p.coeff n * ((n : ℝ) * x ^ (n - 1))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [powerKernel_zero]
    _ = p.derivative.eval x := by
      simpa using (derivative_eval_eq_sum_range_coeff_mul_pow p x).symm

/-- Full-neighborhood limit for the continuous extension kernel at `u → 0`. -/
theorem tendsto_polynomialKernelExt_zero (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => polynomialKernelExt p x u)
      (nhds (0 : ℝ))
      (nhds (p.derivative.eval x)) := by
  simpa [polynomialKernelExt_zero] using (continuous_polynomialKernelExt p x).tendsto 0

/-- Punctured-neighborhood variant for the continuous extension kernel. -/
theorem tendsto_polynomialKernelExt_zero_punctured (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => polynomialKernelExt p x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x)) :=
  (tendsto_polynomialKernelExt_zero p x).mono_left nhdsWithin_le_nhds

/-- Polynomial cosmic-kernel limit reconstructed from kernel decomposition + power limits. -/
theorem tendsto_cosmicKernel_polynomial_eval_via_powerKernel
    (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => p.eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x)) := by
  have hExt :
      Filter.Tendsto (fun u : ℝ => polynomialKernelExt p x u)
        (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
        (nhds (p.derivative.eval x)) :=
    tendsto_polynomialKernelExt_zero_punctured p x
  refine tendsto_nhdsWithin_congr ?hEq hExt
  intro u hu
  have hu0 : u ≠ 0 := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hu
  exact (cosmicKernel_polynomial_eval_eq_polynomialKernelExt_of_ne_zero p x u hu0).symm

/-- Canonical cosmic-kernel limit form for polynomial evaluation (power-kernel flow). -/
theorem tendsto_cosmicKernel_polynomial_eval (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => p.eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x)) :=
  tendsto_cosmicKernel_polynomial_eval_via_powerKernel p x

/-- Polynomial derivative theorem reconstructed via kernel decomposition flow. -/
theorem hasDerivAt_polynomial_eval_cosmic_via_powerKernel (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval y) (p.derivative.eval x) x := by
  exact hasDerivAt_of_tendsto_cosmicKernel
    (tendsto_cosmicKernel_polynomial_eval_via_powerKernel p x)

/-- `deriv` form reconstructed via kernel decomposition flow. -/
theorem deriv_polynomial_eval_cosmic_via_powerKernel (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => p.eval y) x = p.derivative.eval x := by
  simp [(hasDerivAt_polynomial_eval_cosmic_via_powerKernel p x).deriv]

/-- `deriv` form for polynomial evaluation (canonical: via power-kernel decomposition flow). -/
theorem deriv_polynomial_eval_cosmic (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => p.eval y) x = p.derivative.eval x :=
  deriv_polynomial_eval_cosmic_via_powerKernel p x

/-- Polynomial evaluation derivative (canonical: via power-kernel decomposition flow). -/
theorem hasDerivAt_polynomial_eval_cosmic (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval y) (p.derivative.eval x) x :=
  hasDerivAt_polynomial_eval_cosmic_via_powerKernel p x

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
    (hasDerivAt_polynomial_eval_cosmic_via_powerKernel (p := Finset.sum s P) (x := x))

/-- Finite-sum polynomial generalization in cosmic-kernel limit form. -/
theorem tendsto_cosmicKernel_polynomial_eval_finset_sum
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto
      (fun u : ℝ => cosmicKernel (fun y : ℝ => Finset.sum s (fun i => (P i).eval y)) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (Finset.sum s (fun i => ((P i).derivative).eval x))) := by
  simpa [Polynomial.eval_finset_sum, Polynomial.derivative_sum] using
    (tendsto_cosmicKernel_polynomial_eval_via_powerKernel (p := Finset.sum s P) (x := x))

/-- Finite-sum polynomial generalization in `deriv` form. -/
theorem deriv_polynomial_eval_finset_sum_cosmic
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => Finset.sum s (fun i => (P i).eval y)) x =
      Finset.sum s (fun i => ((P i).derivative).eval x) := by
  simpa using
    (hasDerivAt_polynomial_eval_finset_sum_cosmic (s := s) (P := P) (x := x)).deriv

end DkMath.CosmicFormula
