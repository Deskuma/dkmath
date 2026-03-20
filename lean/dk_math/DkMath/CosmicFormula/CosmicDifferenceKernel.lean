/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.CosmicFormula.CosmicDifferenceKernel"

namespace DkMath.CosmicFormula

noncomputable section

/-- Difference operator: `f (x + u) - f x`. -/
def delta (f : ℝ → ℝ) (x u : ℝ) : ℝ :=
  f (x + u) - f x

/-- Cosmic kernel (difference quotient form). -/
def cosmicKernel (f : ℝ → ℝ) (x u : ℝ) : ℝ :=
  delta f x u / u

@[simp] theorem delta_zero_right (f : ℝ → ℝ) (x : ℝ) :
    delta f x 0 = 0 := by
  simp [delta]

theorem delta_add (f g : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => f y + g y) x u = delta f x u + delta g x u := by
  unfold delta
  ring

theorem delta_sub (f g : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => f y - g y) x u = delta f x u - delta g x u := by
  unfold delta
  ring

theorem delta_mul (f g : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => f y * g y) x u
      = f (x + u) * delta g x u + g x * delta f x u := by
  unfold delta
  ring

theorem cosmicKernel_eq (f : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel f x u = (f (x + u) - f x) / u := by
  rfl

theorem cosmicKernel_add (f g : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel (fun y => f y + g y) x u
      = cosmicKernel f x u + cosmicKernel g x u := by
  simp [cosmicKernel, delta_add, add_div]

theorem cosmicKernel_sub (f g : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel (fun y => f y - g y) x u
      = cosmicKernel f x u - cosmicKernel g x u := by
  simp [cosmicKernel, delta_sub, sub_div]

end

end DkMath.CosmicFormula
