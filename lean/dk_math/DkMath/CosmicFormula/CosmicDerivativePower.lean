/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormula.CosmicDifferenceKernel
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.CosmicFormula.CosmicDerivativePower"

namespace DkMath.CosmicFormula

open scoped BigOperators

noncomputable section

/--
Power-case kernel polynomial:
`powerKernel d x u = sum_{j=0}^{d-1} (choose d (j+1)) * x^(d-1-j) * u^j`.

It is the polynomial part that appears after factoring
`(x+u)^d - x^d` by `u`.
-/
def powerKernel (d : ℕ) (x u : ℝ) : ℝ :=
  Finset.sum (Finset.range d) (fun j =>
    (Nat.choose d (j + 1) : ℝ) * x ^ (d - 1 - j) * u ^ j)

/--
Compatibility with the binomial helper `GN`:
`powerKernel d x u = GN d u x`.
-/
theorem powerKernel_eq_GN_swap (d : ℕ) (x u : ℝ) :
    powerKernel d x u = DkMath.CosmicFormulaBinom.GN d u x := by
  unfold powerKernel
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/--
Exact factorization of the power increment:
`(x+u)^d - x^d = u * powerKernel d x u`.

This is the key algebraic decomposition behind the derivative proof.
-/
theorem sub_pow_eq_u_mul_powerKernel (d : ℕ) (x u : ℝ) :
    (x + u) ^ d - x ^ d = u * powerKernel d x u := by
  have h :=
    (DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := ℝ) (d := d) (x := u) (u := x))
  calc
    (x + u) ^ d - x ^ d = (u + x) ^ d - x ^ d := by
      simp [add_comm]
    _ = (u * DkMath.CosmicFormulaBinom.GN d u x + x ^ d) - x ^ d := by
      rw [h]
    _ = u * DkMath.CosmicFormulaBinom.GN d u x := by
      ring
    _ = u * powerKernel d x u := by
      rw [powerKernel_eq_GN_swap]

/--
Alias of `sub_pow_eq_u_mul_powerKernel` for naming compatibility.
-/
theorem sub_eq_u_mul_powerKernel (d : ℕ) (x u : ℝ) :
    (x + u) ^ d - x ^ d = u * powerKernel d x u :=
  sub_pow_eq_u_mul_powerKernel d x u

/--
On `u ≠ 0`, the cosmic kernel of `y^d` coincides with `powerKernel`:
`cosmicKernel (fun y => y^d) x u = powerKernel d x u`.
-/
theorem cosmicKernel_pow_eq_powerKernel_of_ne_zero
    (d : ℕ) (x u : ℝ) (hu : u ≠ 0) :
    cosmicKernel (fun y : ℝ => y ^ d) x u = powerKernel d x u := by
  unfold cosmicKernel delta
  calc
    ((x + u) ^ d - x ^ d) / u = (u * powerKernel d x u) / u := by
      rw [sub_pow_eq_u_mul_powerKernel]
    _ = powerKernel d x u := by
      exact mul_div_cancel_left₀ (powerKernel d x u) hu

end

end DkMath.CosmicFormula
