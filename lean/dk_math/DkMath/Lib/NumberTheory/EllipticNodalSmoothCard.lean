/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticNodalTorsion
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Set.Card

#print "file: DkMath.Lib.NumberTheory.EllipticNodalSmoothCard"

/-!
# A nodal slope coordinate and the elementary smooth-point bound

Let `C = (x₀,y₀)` be a rational singular point of a Weierstrass cubic.  The
three equations saying that `C` lies on the cubic and that both partial
derivatives vanish imply, after translation to `C`,

`Y² + a₁ X Y - (a₂ + 3 x₀) X² = X³`.

Every nonsingular finite point has `X ≠ 0`; its slope `t = Y / X` therefore
recovers `X` as `t² + a₁t - (a₂ + 3x₀)`, and then recovers `Y`.  Thus the
smooth point group injects into `Option K`: `none` records infinity and
`some t` records the slope through the node.  Over a finite field this gives
the intentionally weak, but splitness-free, bound `#E_sm(K) ≤ #K + 1`.

No tangent direction is chosen.  In particular the construction applies to a
nonsplit node as soon as its singular point is rational.  Supplying such a
rational singular centre from multiplicative reduction remains a separate
local-geometric obligation.
-/

namespace DkMath.Lib.NumberTheory.EllipticNodalSmoothCard

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {K : Type*} [Field K] {W : WeierstrassCurve K}

private lemma e₁ {K : Type*} {W : WeierstrassCurve K} : W.toAffine.a₁ = W.a₁ := rfl
private lemma e₂ {K : Type*} {W : WeierstrassCurve K} : W.toAffine.a₂ = W.a₂ := rfl
private lemma e₃ {K : Type*} {W : WeierstrassCurve K} : W.toAffine.a₃ = W.a₃ := rfl
private lemma e₄ {K : Type*} {W : WeierstrassCurve K} : W.toAffine.a₄ = W.a₄ := rfl
private lemma e₆ {K : Type*} {W : WeierstrassCurve K} : W.toAffine.a₆ = W.a₆ := rfl

/-- A rational singular centre, without choosing either tangent direction. -/
structure SingularCentre (W : WeierstrassCurve K) where
  x : K
  y : K
  equation : W.toAffine.Equation x y
  derivativeX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0
  derivativeY : 2 * y + W.a₁ * x + W.a₃ = 0

namespace SingularCentre

variable (C : SingularCentre W)

/-- Translating the Weierstrass equation to a singular centre removes its
constant and linear terms.  This calculation works in all characteristics. -/
lemma translated_equation {x y : K} (h : W.toAffine.Equation x y) :
    (y - C.y) ^ 2 + W.a₁ * (x - C.x) * (y - C.y) -
        (W.a₂ + 3 * C.x) * (x - C.x) ^ 2 = (x - C.x) ^ 3 := by
  have hc := C.equation
  rw [equation_iff, e₁, e₂, e₃, e₄, e₆] at h hc
  linear_combination h - hc - (x - C.x) * C.derivativeX -
    (y - C.y) * C.derivativeY

/-- The singular centre itself is not a member of the smooth affine point
type. -/
lemma not_nonsingular : ¬ W.toAffine.Nonsingular C.x C.y := by
  rw [nonsingular_iff', e₁, e₂, e₃, e₄]
  rintro ⟨-, h | h⟩
  · exact h C.derivativeX
  · exact h C.derivativeY

/-- A smooth finite point cannot have the same `x` coordinate as the singular
centre. -/
lemma sub_x_ne_zero {x y : K} (h : W.toAffine.Nonsingular x y) : x - C.x ≠ 0 := by
  intro hx
  have hx' : x = C.x := sub_eq_zero.mp hx
  have he := translated_equation C h.left
  rw [hx'] at he h
  have hxy : y - C.y = 0 := by
    have he' : (y - C.y) ^ 2 = 0 := by simpa using he
    exact sq_eq_zero_iff.mp he'
  have hy : y = C.y := sub_eq_zero.mp hxy
  subst y
  exact not_nonsingular C h

/-- The translated `x` coordinate is recovered from the slope through the
singular centre. -/
lemma sub_x_eq_slope_polynomial {x y : K} (h : W.toAffine.Nonsingular x y) :
    x - C.x = ((y - C.y) / (x - C.x)) ^ 2 + W.a₁ * ((y - C.y) / (x - C.x)) -
      (W.a₂ + 3 * C.x) := by
  have hx := sub_x_ne_zero C h
  have he := translated_equation C h.left
  calc
    x - C.x = (x - C.x) ^ 3 / (x - C.x) ^ 2 := by field_simp [hx]
    _ = ((y - C.y) ^ 2 + W.a₁ * (x - C.x) * (y - C.y) -
        (W.a₂ + 3 * C.x) * (x - C.x) ^ 2) / (x - C.x) ^ 2 := by rw [he]
    _ = ((y - C.y) / (x - C.x)) ^ 2 + W.a₁ * ((y - C.y) / (x - C.x)) -
        (W.a₂ + 3 * C.x) := by field_simp [hx]

/-- The slope through the rational node, with `none` reserved for the point at
infinity. -/
noncomputable def slopeAt : W.toAffine.Point → Option K
  | 0 => none
  | .some x y _ => some ((y - C.y) / (x - C.x))

/-- The nodal slope coordinate is injective on all smooth affine points. -/
theorem slopeAt_injective : Function.Injective (slopeAt C) := by
  intro P Q hPQ
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · cases hPQ
  · cases hPQ
  · change Option.some ((y₁ - C.y) / (x₁ - C.x)) =
      Option.some ((y₂ - C.y) / (x₂ - C.x)) at hPQ
    have hslope : (y₁ - C.y) / (x₁ - C.x) = (y₂ - C.y) / (x₂ - C.x) :=
      Option.some.inj hPQ
    have hx₁ := sub_x_ne_zero C h₁
    have hx₂ := sub_x_ne_zero C h₂
    have hX₁ := sub_x_eq_slope_polynomial C h₁
    have hX₂ := sub_x_eq_slope_polynomial C h₂
    have hX : x₁ - C.x = x₂ - C.x := by rw [hX₁, hX₂, hslope]
    have hx : x₁ = x₂ := by linear_combination hX
    have hY : y₁ - C.y = y₂ - C.y := by
      calc
        y₁ - C.y = ((y₁ - C.y) / (x₁ - C.x)) * (x₁ - C.x) :=
          (div_mul_cancel₀ _ hx₁).symm
        _ = ((y₂ - C.y) / (x₂ - C.x)) * (x₂ - C.x) := by rw [hslope, hx]
        _ = y₂ - C.y := div_mul_cancel₀ _ hx₂
    have hy : y₁ = y₂ := by linear_combination hY
    subst x₂
    subst y₂
    rfl

end SingularCentre

variable [Finite K]

/-- The slope coordinate also proves that the smooth point type is finite over
a finite field.  It is exposed separately so consumers may use positivity of
`Nat.card` without re-proving the injection. -/
theorem finitePoints (C : SingularCentre W) : Finite W.toAffine.Point :=
  Finite.of_injective (SingularCentre.slopeAt C) (SingularCentre.slopeAt_injective C)

/-- The smooth point group is nonempty (it contains infinity), hence its
finite cardinality is positive. -/
theorem natCard_points_pos (C : SingularCentre W) : 0 < Nat.card W.toAffine.Point := by
  let _ : Finite W.toAffine.Point := finitePoints C
  exact Nat.card_pos

variable [Fintype K]

/-- A rational singular centre gives the elementary nodal bound
`#E_sm(K) ≤ #K + 1`.  Unlike the exact `q-1`/`q+1` formula, it needs no
splitness decision and no enumeration of tangent directions. -/
theorem natCard_points_le_card_add_one (C : SingularCentre W) :
    Nat.card W.toAffine.Point ≤ Fintype.card K + 1 := by
  classical
  calc
    Nat.card W.toAffine.Point ≤ Nat.card (Option K) :=
      Nat.card_le_card_of_injective (SingularCentre.slopeAt C)
        (SingularCentre.slopeAt_injective C)
    _ = Fintype.card K + 1 := by simp [Nat.card_eq_fintype_card]

end DkMath.Lib.NumberTheory.EllipticNodalSmoothCard
