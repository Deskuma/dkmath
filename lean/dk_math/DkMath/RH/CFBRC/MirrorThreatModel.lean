/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.OffCriticalExclusionGeneral
import DkMath.CFBRC.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.MirrorThreatModel"

namespace DkMath.RH.CFBRCProjection

open DkMath.CFBRC

/--
Mirror CFBRC around the centered line `X = 0`.

Unlike the standard exclusion polynomial, this larger symmetric model may have
zeros with `X ≠ 0`.  It is introduced only as a threat model: a future zeta
bridge must either land in the standard CFBRC family or rule out the nontrivial
mirror-core branches.
-/
noncomputable def mirrorCFBRC (d : ℕ) (X Θ : ℝ) : ℂ :=
  ((X : ℂ) + Complex.I * (Θ : ℂ)) ^ d -
    ((-X : ℂ) + Complex.I * (Θ : ℂ)) ^ d

/--
The shifted cyclotomic core left after extracting the centered boundary factor
`2X` from `mirrorCFBRC`.
-/
noncomputable def mirrorCFBRCCore (d : ℕ) (X Θ : ℝ) : ℂ :=
  cyclotomicPrimeCore d
    (2 * (X : ℂ))
    ((-X : ℂ) + Complex.I * (Θ : ℂ))

/--
Exact CFBRC factorization of the mirror polynomial.

`mirrorCFBRC d X Θ = 2X * mirrorCFBRCCore d X Θ`.
-/
theorem mirrorCFBRC_eq_boundary_mul_core
    (d : ℕ) (X Θ : ℝ) :
    mirrorCFBRC d X Θ =
      (2 * (X : ℂ)) * mirrorCFBRCCore d X Θ := by
  let x : ℂ := 2 * (X : ℂ)
  let u : ℂ := (-X : ℂ) + Complex.I * (Θ : ℂ)
  have h := add_pow_eq_mul_cyclotomicPrimeCore_add_gap d x u
  have hxadd : x + u = (X : ℂ) + Complex.I * (Θ : ℂ) := by
    dsimp [x, u]
    ring
  calc
    mirrorCFBRC d X Θ = (x + u) ^ d - u ^ d := by
      rw [mirrorCFBRC, hxadd]
      rfl
    _ = x * cyclotomicPrimeCore d x u := by
      rw [h]
      ring
    _ = (2 * (X : ℂ)) * mirrorCFBRCCore d X Θ := by
      rfl

/--
Away from the centered line, mirror closure is exactly the vanishing of the
mirror cyclotomic core.
-/
theorem mirrorCFBRC_eq_zero_iff_core_eq_zero
    {d : ℕ} {X Θ : ℝ} (hX : X ≠ 0) :
    mirrorCFBRC d X Θ = 0 ↔ mirrorCFBRCCore d X Θ = 0 := by
  rw [mirrorCFBRC_eq_boundary_mul_core]
  simp [hX]

/-- Degree one has only the centered boundary factor. -/
@[simp] theorem mirrorCFBRC_one (X Θ : ℝ) :
    mirrorCFBRC 1 X Θ = 2 * (X : ℂ) := by
  simp [mirrorCFBRC]
  ring

/-- Degree two also has no off-centered mirror zero when `Θ ≠ 0`. -/
theorem mirrorCFBRC_two (X Θ : ℝ) :
    mirrorCFBRC 2 X Θ = 4 * Complex.I * (X : ℂ) * (Θ : ℂ) := by
  simp [mirrorCFBRC, pow_two]
  ring

/--
The first nontrivial real mirror branch appears in degree three.
-/
theorem mirrorCFBRC_three (X Θ : ℝ) :
    mirrorCFBRC 3 X Θ =
      (2 * X * (X ^ 2 - 3 * Θ ^ 2) : ℝ) := by
  simp [mirrorCFBRC, pow_succ, pow_two]
  ring

/--
Degree-three mirror closure splits into the centered branch and the first
nontrivial off-centered branch equation.
-/
theorem mirrorCFBRC_three_eq_zero_iff (X Θ : ℝ) :
    mirrorCFBRC 3 X Θ = 0 ↔ X = 0 ∨ X ^ 2 = 3 * Θ ^ 2 := by
  rw [mirrorCFBRC_three]
  norm_cast
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h2X | hbranch
    · left
      nlinarith
    · right
      nlinarith
  · intro h
    rcases h with hX | hbranch
    · subst X
      simp
    · nlinarith

end DkMath.RH.CFBRCProjection
