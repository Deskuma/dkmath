/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.CosmicFormula.CosmicDifferenceKernel"

namespace DkMath.CosmicFormula

noncomputable section

/--
Difference operator (forward increment):
`delta f x u = f(x+u) - f(x)`.

This is the numerator of the difference quotient.
-/
def delta (f : ℝ → ℝ) (x u : ℝ) : ℝ :=
  f (x + u) - f x

/--
Cosmic kernel (difference quotient form):
`cosmicKernel f x u = (f(x+u)-f(x))/u = delta f x u / u`.

This is the central object used to express derivatives as limits.
-/
def cosmicKernel (f : ℝ → ℝ) (x u : ℝ) : ℝ :=
  delta f x u / u

/-- Zero increment identity: `delta f x 0 = 0`. -/
@[simp] theorem delta_zero_right (f : ℝ → ℝ) (x : ℝ) :
    delta f x 0 = 0 := by
  simp [delta]

/-- Linearity of `delta` for addition: `delta(f+g) = delta f + delta g`. -/
theorem delta_add (f g : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => f y + g y) x u = delta f x u + delta g x u := by
  unfold delta
  ring

/-- Linearity of `delta` for subtraction: `delta(f-g) = delta f - delta g`. -/
theorem delta_sub (f g : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => f y - g y) x u = delta f x u - delta g x u := by
  unfold delta
  ring

/-- Scalar compatibility of `delta`: `delta(a • f) = a • delta f`. -/
theorem delta_smul (a : ℝ) (f : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => a * f y) x u = a * delta f x u := by
  unfold delta
  ring

/--
Product expansion for increments:
`delta(fg) = f(x+u) * delta g + g(x) * delta f`.

This is the discrete product rule at increment level.
-/
theorem delta_mul (f g : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => f y * g y) x u
      = f (x + u) * delta g x u + g x * delta f x u := by
  unfold delta
  ring

/--
Finite-sum linearity of increments:
`delta (sum_i F_i) = sum_i delta(F_i)`.
-/
theorem delta_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ) (x u : ℝ) :
    delta (fun y => Finset.sum s (fun i => F i y)) x u
      = Finset.sum s (fun i => delta (F i) x u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [delta]
  | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, delta_add, ih]

theorem cosmicKernel_eq (f : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel f x u = (f (x + u) - f x) / u := by
  rfl

/-- Linearity of `cosmicKernel` for addition. -/
theorem cosmicKernel_add (f g : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel (fun y => f y + g y) x u
      = cosmicKernel f x u + cosmicKernel g x u := by
  simp [cosmicKernel, delta_add, add_div]

/-- Linearity of `cosmicKernel` for subtraction. -/
theorem cosmicKernel_sub (f g : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel (fun y => f y - g y) x u
      = cosmicKernel f x u - cosmicKernel g x u := by
  simp [cosmicKernel, delta_sub, sub_div]

/-- Scalar compatibility of `cosmicKernel`. -/
theorem cosmicKernel_smul (a : ℝ) (f : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel (fun y => a * f y) x u = a * cosmicKernel f x u := by
  simp [cosmicKernel, delta_smul, div_eq_mul_inv, mul_assoc]

/--
Finite-sum linearity of `cosmicKernel`:
`cosmicKernel (sum_i F_i) = sum_i cosmicKernel(F_i)`.
-/
theorem cosmicKernel_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ) (x u : ℝ) :
    cosmicKernel (fun y => Finset.sum s (fun i => F i y)) x u
      = Finset.sum s (fun i => cosmicKernel (F i) x u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [cosmicKernel, delta]
  | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, cosmicKernel_add, ih]

/--
Product formula for `cosmicKernel`:
`K_{fg}(x,u) = f(x+u) K_g(x,u) + g(x) K_f(x,u)`.

This is obtained by dividing the increment product expansion (`delta_mul`) by `u`.
-/
theorem cosmicKernel_mul (f g : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel (fun y => f y * g y) x u
      = f (x + u) * cosmicKernel g x u + g x * cosmicKernel f x u := by
  calc
    cosmicKernel (fun y => f y * g y) x u
        = delta (fun y => f y * g y) x u / u := rfl
    _ = (f (x + u) * delta g x u + g x * delta f x u) / u := by
      rw [delta_mul]
    _ = (f (x + u) * delta g x u) / u + (g x * delta f x u) / u := by
      rw [add_div]
    _ = f (x + u) * (delta g x u / u) + g x * (delta f x u / u) := by
      simp [div_eq_mul_inv, mul_left_comm, mul_comm]
    _ = f (x + u) * cosmicKernel g x u + g x * cosmicKernel f x u := rfl

end

end DkMath.CosmicFormula
