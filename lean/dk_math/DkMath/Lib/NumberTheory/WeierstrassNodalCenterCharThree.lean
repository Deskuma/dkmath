/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra
import DkMath.Lib.NumberTheory.EllipticNodalSmoothCard
import Mathlib.Tactic.ReduceModChar

#print "file: DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharThree"

/-!
# A rational singular centre in characteristic three

Here `c₄ = b₂²`, so `c₄ ≠ 0` permits division by `b₂`.  The explicit
coordinates `x₀ = -b₄/b₂`, `y₀ = -(a₁*x₀+a₃)/2` kill both partial
 derivatives.  The identity `b₂³ * equationDefect W x₀ y₀ = Δ` then proves
that `Δ = 0` puts the candidate on the curve.  All statements hold over any
field of characteristic three; there is no finite enumeration or splitness
hypothesis.
-/

namespace DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharThree

open WeierstrassCurve WeierstrassCurve.Affine
open EllipticCriticalCentreAlgebra EllipticNodalSmoothCard

variable {k : Type*} [Field k] [CharP k 3]

private lemma two_ne_zero : (2 : k) ≠ 0 := by
  intro h
  have hd := (CharP.cast_eq_zero_iff k 3 2).mp h
  norm_num at hd

/-- In characteristic three the `24*b₄` term vanishes. -/
theorem c4_eq_b2_sq (W : WeierstrassCurve k) : W.c₄ = W.b₂ ^ 2 := by
  simp only [c₄]
  reduce_mod_char!

/-- The denominator-cleared defect of the explicit candidate is exactly `Δ`.
This is a field identity in characteristic three, before assuming `Δ = 0`. -/
theorem candidate_defect_identity (W : WeierstrassCurve k) (hb : W.b₂ ≠ 0) :
    W.b₂ ^ 3 * equationDefect W (-W.b₄ / W.b₂)
      (-(W.a₁ * (-W.b₄ / W.b₂) + W.a₃) / 2) = W.Δ := by
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  simp only [equationDefect, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈] at *
  field_simp [hb, h2]
  ring_nf
  reduce_mod_char!
  ring

/-- A singular model with nonzero `c₄` has a rational singular centre in
characteristic three.  No tangent direction or square-root choice is needed. -/
noncomputable def singularCentre_of_char_three_of_delta_zero_of_c4_ne_zero
    (W : WeierstrassCurve k) (hΔ : W.Δ = 0) (hc4 : W.c₄ ≠ 0) :
    SingularCentre W := by
  have hb : W.b₂ ≠ 0 := by
    intro hz
    apply hc4
    rw [c4_eq_b2_sq, hz, zero_pow (by decide)]
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  let x₀ := -W.b₄ / W.b₂
  let y₀ := -(W.a₁ * x₀ + W.a₃) / 2
  have hdy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    dsimp [y₀]
    field_simp [h2]
    ring
  have hdx : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0 := by
    dsimp [x₀, y₀]
    simp only [b₂, b₄] at *
    field_simp [hb, h2]
    ring_nf
    reduce_mod_char!
  refine ⟨x₀, y₀, ?_, hdx, hdy⟩
  rw [equation_iff]
  apply sub_eq_zero.mp
  change equationDefect W x₀ y₀ = 0
  have h := candidate_defect_identity W hb
  rw [hΔ] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 hb)

end DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharThree
