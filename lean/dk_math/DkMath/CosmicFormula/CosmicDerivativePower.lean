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

/-- Power-case cosmic kernel polynomial part. -/
def powerKernel (d : ℕ) (x u : ℝ) : ℝ :=
  Finset.sum (Finset.range d) (fun j =>
    (Nat.choose d (j + 1) : ℝ) * x ^ (d - 1 - j) * u ^ j)

theorem powerKernel_eq_GN_swap (d : ℕ) (x u : ℝ) :
    powerKernel d x u = DkMath.CosmicFormulaBinom.GN d u x := by
  unfold powerKernel DkMath.CosmicFormulaBinom.GN
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
Exact factorization for powers in cosmic-kernel form.
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

theorem sub_eq_u_mul_powerKernel (d : ℕ) (x u : ℝ) :
    (x + u) ^ d - x ^ d = u * powerKernel d x u :=
  sub_pow_eq_u_mul_powerKernel d x u

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
