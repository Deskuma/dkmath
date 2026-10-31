/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticCriticalCentreAlgebra
import DkMath.Lib.NumberTheory.EllipticNodalSmoothCard

#print "file: DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharTwo"

/-!
# A rational singular centre in characteristic two

For a Weierstrass model over a field of characteristic two, the invariant
identity `c₄ = a₁⁴` makes `c₄ ≠ 0` exactly the non-vanishing condition needed
to divide by `a₁`.  The point

`x₀ = a₃ / a₁`,   `y₀ = (x₀² + a₄) / a₁`

then has both partial derivatives equal to zero.  The remaining curve equation
is not assumed: after clearing denominators, the explicit identity

`a₁⁶ * equationDefect W x₀ y₀ = Δ`

shows that `Δ = 0` puts this point on the cubic.  This is a direct finite-field
construction, independent of tangent-direction splitting or a square-root
choice, and is therefore the concrete `q = 2` entry point for the nodal local
component argument.
-/

namespace DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharTwo

open WeierstrassCurve WeierstrassCurve.Affine
open EllipticCriticalCentreAlgebra
open EllipticNodalSmoothCard

variable {k : Type*} [Field k] [CharP k 2]

private lemma cast_two_eq_zero : (2 : k) = 0 := CharP.cast_eq_zero k 2

private lemma cast_four_eq_zero : (4 : k) = 0 := by
  calc
    (4 : k) = 2 * 2 := by norm_num
    _ = 0 := by rw [cast_two_eq_zero]; simp

private lemma cast_twenty_four_eq_zero : (24 : k) = 0 := by
  calc
    (24 : k) = 2 * 2 * 2 * 3 := by norm_num
    _ = 0 := by rw [cast_two_eq_zero]; simp

private lemma cast_twenty_seven_eq_one : (27 : k) = 1 := by
  calc
    (27 : k) = 26 + 1 := by norm_num
    _ = 1 := by
      have h26 : (26 : k) = 0 := by
        calc
          (26 : k) = 2 * 13 := by norm_num
          _ = 0 := by rw [cast_two_eq_zero]; simp
      rw [h26]
      simp

private lemma cast_three_eq_one : (3 : k) = 1 := by
  calc
    (3 : k) = 2 + 1 := by norm_num
    _ = 1 := by rw [cast_two_eq_zero]; simp

private lemma c4_eq_a1_four (W : WeierstrassCurve k) : W.c₄ = W.a₁ ^ 4 := by
  simp only [c₄, b₂, b₄]
  simp only [cast_four_eq_zero, cast_twenty_four_eq_zero, zero_mul, add_zero, sub_zero]
  ring

private lemma a1_ne_zero (W : WeierstrassCurve k) (hc4 : W.c₄ ≠ 0) : W.a₁ ≠ 0 := by
  intro ha
  apply hc4
  rw [c4_eq_a1_four W, ha, zero_pow (by decide)]

private lemma candidate_defect_identity (W : WeierstrassCurve k) (ha1 : W.a₁ ≠ 0) :
    W.a₁ ^ 6 * equationDefect W (W.a₃ / W.a₁)
      (((W.a₃ / W.a₁) ^ 2 + W.a₄) / W.a₁) = W.Δ := by
  simp only [equationDefect, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  simp [cast_two_eq_zero, cast_four_eq_zero, cast_twenty_seven_eq_one]
  field_simp [ha1]
  ring_nf
  linear_combination
    (W.a₃ ^ 2 * W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 4) * (CharP.cast_eq_zero k 2)

/-- [DkMath.Lib] In characteristic two, `Δ = 0` and `c₄ ≠ 0` construct a
rational singular centre explicitly.  The tangent directions are not chosen;
only the singular point required by the finite smooth-point bound is returned.
-/
noncomputable def singularCentre_of_char_two_of_delta_zero_of_c4_ne_zero
    (W : WeierstrassCurve k) (hΔ : W.Δ = 0) (hc4 : W.c₄ ≠ 0) :
    SingularCentre W := by
  let x₀ : k := W.a₃ / W.a₁
  let y₀ : k := (x₀ ^ 2 + W.a₄) / W.a₁
  have ha1 : W.a₁ ≠ 0 := a1_ne_zero W hc4
  have hdef : equationDefect W x₀ y₀ = 0 := by
    have h := candidate_defect_identity W ha1
    rw [hΔ] at h
    have hzero : W.a₁ ^ 6 * equationDefect W x₀ y₀ = 0 := by
      simpa [x₀, y₀] using h
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 6 ha1)
  have hderY : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    rw [cast_two_eq_zero]
    dsimp [x₀]
    field_simp [ha1]
    ring_nf
    linear_combination W.a₃ * (CharP.cast_eq_zero k 2)
  have hderX : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0 := by
    rw [cast_two_eq_zero, cast_three_eq_one]
    dsimp [y₀]
    field_simp [ha1]
    ring_nf
  refine ⟨x₀, y₀, ?_, hderX, hderY⟩
  rw [equation_iff]
  exact sub_eq_zero.mp hdef

end DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharTwo
