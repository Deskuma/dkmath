/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormula.CosmicDerivativePowerLimit

#print "file: DkMath.CosmicFormula.CosmicDerivativePolynomial"

namespace DkMath.CosmicFormula

/--
Legacy bridge:
derive polynomial evaluation directly from mathlib's `Polynomial.hasDerivAt`.

Mathematical content:
`d/dx (p(x)) = p'(x)`.

Canonical theorem is `hasDerivAt_polynomial_eval_cosmic`, which is reconstructed
from the cosmic-kernel decomposition flow.
-/
theorem hasDerivAt_polynomial_eval_cosmic_from_mathlib (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval y) (p.derivative.eval x) x := by
  simpa using (p.hasDerivAt x)

/--
Legacy bridge in limit form:
convert `HasDerivAt` to the cosmic-kernel punctured limit.

Formula:
`cosmicKernel f x u = (f (x + u) - f x) / u`
and
`cosmicKernel (fun y => p.eval y) x u -> p.derivative.eval x` as `u -> 0`, `u ≠ 0`.

Canonical theorem is `tendsto_cosmicKernel_polynomial_eval`.
-/
theorem tendsto_cosmicKernel_polynomial_eval_from_hasDerivAt (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => p.eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_polynomial_eval_cosmic_from_mathlib p x)

/--
Legacy bridge in `deriv` form:
`deriv (fun y => p.eval y) x = p.derivative.eval x` via existing mathlib theorem.

Canonical theorem is `deriv_polynomial_eval_cosmic`.
-/
theorem deriv_polynomial_eval_cosmic_from_mathlib (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => p.eval y) x = p.derivative.eval x := by
  simp [p.deriv (x := x)]

/--
Monomial kernel decomposition (`u ≠ 0`):
for `f(y) = a * y^n`,
`cosmicKernel f x u = a * powerKernel n x u`.

This is the basic brick used to expand polynomial kernels coefficient-wise.
-/
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

/--
Polynomial kernel decomposition (`u ≠ 0`):
`cosmicKernel (fun y => p.eval y) x u` is expanded as the finite sum
`sum_{n=0}^{natDegree p} coeff_n * powerKernel n x u`.

This corresponds to termwise expansion of `(p(x+u)-p(x))/u` into monomials.
-/
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

/--
Continuous extension of the polynomial kernel to `u = 0`:
`polynomialKernelExt p x u` is defined as a finite sum of `powerKernel`.

Design intent:
1. For `u ≠ 0`, it matches the original `cosmicKernel`.
2. At `u = 0`, it evaluates to `p.derivative.eval x`.

So this object realizes a textbook "removable singularity" extension.
-/
def polynomialKernelExt (p : Polynomial ℝ) (x u : ℝ) : ℝ :=
  Finset.sum (Finset.range (p.natDegree + 1)) (fun n => p.coeff n * powerKernel n x u)

/--
Compatibility on punctured neighborhood:
if `u ≠ 0`, then
`cosmicKernel (fun y => p.eval y) x u = polynomialKernelExt p x u`.
-/
theorem cosmicKernel_polynomial_eval_eq_polynomialKernelExt_of_ne_zero
    (p : Polynomial ℝ) (x u : ℝ) (hu : u ≠ 0) :
    cosmicKernel (fun y : ℝ => p.eval y) x u = polynomialKernelExt p x u := by
  simpa [polynomialKernelExt] using
    (cosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernel_of_ne_zero p x u hu)

/--
Derivative evaluation in range-sum form:
`p.derivative.eval x` is rewritten as
`sum coeff_n * (n * x^(n-1))` over `range (natDegree p + 1)`.

This normalization makes the `u = 0` value of `polynomialKernelExt` align
with the derivative expression term by term.
-/
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

/--
Continuity of the extended kernel in `u`.

Reason:
each `powerKernel n x u` is continuous in `u`,
and finite sums and scalar multiples preserve continuity.
-/
theorem continuous_polynomialKernelExt (p : Polynomial ℝ) (x : ℝ) :
    Continuous (fun u : ℝ => polynomialKernelExt p x u) := by
  unfold polynomialKernelExt
  refine continuous_finset_sum (s := Finset.range (p.natDegree + 1)) ?_
  intro n hn
  exact (continuous_const.mul (continuous_powerKernel n x))

/--
Value of the continuous extension at the center:
`polynomialKernelExt p x 0 = p.derivative.eval x`.

This is the key identity that identifies the limit value of the kernel.
-/
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

/--
Full-neighborhood limit of the extension:
`polynomialKernelExt p x u -> p.derivative.eval x` in `nhds 0`.

This is obtained from continuity plus the center-value identity.
-/
theorem tendsto_polynomialKernelExt_zero (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => polynomialKernelExt p x u)
      (nhds (0 : ℝ))
      (nhds (p.derivative.eval x)) := by
  simpa [polynomialKernelExt_zero] using (continuous_polynomialKernelExt p x).tendsto 0

/--
Punctured-neighborhood variant:
restrict the previous full-neighborhood limit to `u ≠ 0`.
-/
theorem tendsto_polynomialKernelExt_zero_punctured (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => polynomialKernelExt p x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x)) :=
  (tendsto_polynomialKernelExt_zero p x).mono_left nhdsWithin_le_nhds

/--
Core reconstruction theorem (decomposition flow):
combine
1. `cosmicKernel = polynomialKernelExt` on `u ≠ 0`,
2. punctured limit of `polynomialKernelExt`.

Conclusion:
`cosmicKernel (fun y => p.eval y) x u -> p.derivative.eval x`
on the punctured neighborhood of `0`.
-/
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

/--
Canonical punctured-limit theorem for polynomial evaluation.

This theorem is intentionally routed through the decomposition flow
(`..._via_powerKernel`) as the public mainline API.
-/
theorem tendsto_cosmicKernel_polynomial_eval (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => p.eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x)) :=
  tendsto_cosmicKernel_polynomial_eval_via_powerKernel p x

/--
Canonical derivative theorem in `HasDerivAt` form, reconstructed from the
cosmic-kernel limit (`hasDerivAt_of_tendsto_cosmicKernel`).
-/
theorem hasDerivAt_polynomial_eval_cosmic_via_powerKernel (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval y) (p.derivative.eval x) x := by
  exact hasDerivAt_of_tendsto_cosmicKernel
    (tendsto_cosmicKernel_polynomial_eval_via_powerKernel p x)

/--
`deriv` form of the decomposition-based derivative theorem:
`deriv (fun y => p.eval y) x = p.derivative.eval x`.
-/
theorem deriv_polynomial_eval_cosmic_via_powerKernel (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => p.eval y) x = p.derivative.eval x := by
  simp [(hasDerivAt_polynomial_eval_cosmic_via_powerKernel p x).deriv]

/--
Canonical `deriv` API for polynomial evaluation.

Mathematical statement:
if `f(y) = p(y)`, then `f'(x) = p'(x)`.

Implementation route is fixed to `..._via_powerKernel`.
-/
theorem deriv_polynomial_eval_cosmic (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => p.eval y) x = p.derivative.eval x :=
  deriv_polynomial_eval_cosmic_via_powerKernel p x

/--
Canonical `HasDerivAt` API for polynomial evaluation.

Textbook form:
`HasDerivAt (fun y => p.eval y) (p.derivative.eval x) x`.
-/
theorem hasDerivAt_polynomial_eval_cosmic (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval y) (p.derivative.eval x) x :=
  hasDerivAt_polynomial_eval_cosmic_via_powerKernel p x

/--
Additivity (`HasDerivAt` form):
for `f(y) = (p+q)(y)`,
`f'(x) = p'(x) + q'(x)`.
-/
theorem hasDerivAt_polynomial_eval_add_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (p + q).eval y)
      (p.derivative.eval x + q.derivative.eval x) x := by
  simpa [Polynomial.eval_add, Polynomial.derivative_add] using
    (hasDerivAt_polynomial_eval_cosmic (p := p + q) (x := x))

/--
Additivity in cosmic-kernel punctured-limit form:
`cosmicKernel (fun y => (p+q).eval y) x u`
tends to `p'(x)+q'(x)` as `u -> 0`, `u ≠ 0`.
-/
theorem tendsto_cosmicKernel_polynomial_eval_add
    (p q : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => (p + q).eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x + q.derivative.eval x)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_polynomial_eval_add_cosmic p q x)

/--
Additivity in `deriv` form:
`deriv (fun y => (p+q).eval y) x = p'(x) + q'(x)`.
-/
theorem deriv_polynomial_eval_add_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => (p + q).eval y) x =
      p.derivative.eval x + q.derivative.eval x := by
  simpa using (hasDerivAt_polynomial_eval_add_cosmic p q x).deriv

/--
Product rule (`HasDerivAt` form):
for `f(y) = (p*q)(y)`,
`f'(x) = p'(x) q(x) + p(x) q'(x)`.
-/
theorem hasDerivAt_polynomial_eval_mul_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (p * q).eval y)
      (p.derivative.eval x * q.eval x + p.eval x * q.derivative.eval x) x := by
  simpa [Polynomial.eval_mul, Polynomial.derivative_mul] using
    (hasDerivAt_polynomial_eval_cosmic (p := p * q) (x := x))

/--
Product rule in cosmic-kernel punctured-limit form:
`cosmicKernel (fun y => (p*q).eval y) x u`
tends to `p'(x)q(x) + p(x)q'(x)` as `u -> 0`, `u ≠ 0`.
-/
theorem tendsto_cosmicKernel_polynomial_eval_mul
    (p q : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => (p * q).eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval x * q.eval x + p.eval x * q.derivative.eval x)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_polynomial_eval_mul_cosmic p q x)

/--
Product rule in `deriv` form:
`deriv (fun y => (p*q).eval y) x = p'(x)q(x) + p(x)q'(x)`.
-/
theorem deriv_polynomial_eval_mul_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => (p * q).eval y) x =
      p.derivative.eval x * q.eval x + p.eval x * q.derivative.eval x := by
  simpa using (hasDerivAt_polynomial_eval_mul_cosmic p q x).deriv

/--
Chain rule (`HasDerivAt` form):
for `f(y) = p(q(y))`,
`f'(x) = p'(q(x)) * q'(x)`.
-/
theorem hasDerivAt_polynomial_eval_comp_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (p.comp q).eval y)
      (p.derivative.eval (q.eval x) * q.derivative.eval x) x := by
  simpa [Polynomial.eval_comp, Polynomial.derivative_comp, Polynomial.eval_mul,
    mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_polynomial_eval_cosmic (p := p.comp q) (x := x))

/--
Chain rule in cosmic-kernel punctured-limit form:
`cosmicKernel (fun y => (p.comp q).eval y) x u`
tends to `p'(q(x)) * q'(x)` as `u -> 0`, `u ≠ 0`.
-/
theorem tendsto_cosmicKernel_polynomial_eval_comp
    (p q : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => (p.comp q).eval y) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (p.derivative.eval (q.eval x) * q.derivative.eval x)) := by
  exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_polynomial_eval_comp_cosmic p q x)

/--
Chain rule in `deriv` form:
`deriv (fun y => (p.comp q).eval y) x = p'(q(x)) * q'(x)`.
-/
theorem deriv_polynomial_eval_comp_cosmic
    (p q : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => (p.comp q).eval y) x =
      p.derivative.eval (q.eval x) * q.derivative.eval x := by
  simpa using (hasDerivAt_polynomial_eval_comp_cosmic p q x).deriv

/--
Finite-sum linearity (`HasDerivAt` form):
for `F(y) = sum_{i in s} P i (y)`,
`F'(x) = sum_{i in s} (P i)'(x)`.
-/
theorem hasDerivAt_polynomial_eval_finset_sum_cosmic
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Finset.sum s (fun i => (P i).eval y))
      (Finset.sum s (fun i => ((P i).derivative).eval x)) x := by
  simpa [Polynomial.eval_finset_sum, Polynomial.derivative_sum] using
    (hasDerivAt_polynomial_eval_cosmic_via_powerKernel (p := Finset.sum s P) (x := x))

/--
Finite-sum linearity in cosmic-kernel punctured-limit form:
the kernel of `sum_{i in s} P i` tends to
`sum_{i in s} (P i)'(x)` as `u -> 0`, `u ≠ 0`.
-/
theorem tendsto_cosmicKernel_polynomial_eval_finset_sum
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto
      (fun u : ℝ => cosmicKernel (fun y : ℝ => Finset.sum s (fun i => (P i).eval y)) x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds (Finset.sum s (fun i => ((P i).derivative).eval x))) := by
  simpa [Polynomial.eval_finset_sum, Polynomial.derivative_sum] using
    (tendsto_cosmicKernel_polynomial_eval_via_powerKernel (p := Finset.sum s P) (x := x))

/--
Finite-sum linearity in `deriv` form:
`deriv (fun y => sum_{i in s} P i (y)) x = sum_{i in s} (P i)'(x)`.
-/
theorem deriv_polynomial_eval_finset_sum_cosmic
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => Finset.sum s (fun i => (P i).eval y)) x =
      Finset.sum s (fun i => ((P i).derivative).eval x) := by
  simpa using
    (hasDerivAt_polynomial_eval_finset_sum_cosmic (s := s) (P := P) (x := x)).deriv

end DkMath.CosmicFormula
