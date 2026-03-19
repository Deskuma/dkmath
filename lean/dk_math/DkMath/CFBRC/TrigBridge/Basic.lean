/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace DkMath.CFBRC.TrigBridge

/-- Quadratic Body: `(a' + x)^2 - x^2`. -/
def body2 {α : Type _} [Ring α] (ap x : α) : α :=
  (ap + x) ^ 2 - x ^ 2

/-- CFBRC core polynomial in the complex plane. -/
def cfbrc (d : ℕ) (X Θ : ℂ) : ℂ :=
  (X + Complex.I * Θ) ^ d - (Complex.I * Θ) ^ d

/-- Real-input version of `cfbrc`, coerced into `ℂ`. -/
def cfbrcR (d : ℕ) (X Θ : ℝ) : ℂ :=
  cfbrc d X Θ

lemma body2_factor {α : Type _} [CommRing α] (ap x : α) :
    body2 ap x = ap * (ap + 2 * x) := by
  simp [body2, pow_two]
  ring

lemma body2_sub {α : Type _} [CommRing α] (a x : α) :
    body2 (a - x) x = a ^ 2 - x ^ 2 := by
  simp [body2, pow_two]

lemma body2_sub_factor {α : Type _} [CommRing α] (a x : α) :
    body2 (a - x) x = (a - x) * ((a - x) + 2 * x) := by
  simpa using (body2_factor (a - x) x)

end DkMath.CFBRC.TrigBridge
