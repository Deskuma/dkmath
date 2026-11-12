/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral

#print "file: DkMathTest.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral"

namespace DkMathTest.WeierstrassTwoTorsionTranslateGeneral

open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral
open scoped WeierstrassCurve.Affine

variable {F : Type*} [Field F] [NeZero (2 : F)] [DecidableEq F]
variable {ι : Type*}

example (W : WeierstrassCurve F)
    {e₁ e₂ e₃ : F}
    (h₁ : W.twoTorsionPolynomial.toPoly.eval e₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval e₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval e₃ = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    4 * (e₁ + e₂ + e₃) = -(W.a₁ ^ 2 + 4 * W.a₂) :=
  two_torsion_root_sum W h₁ h₂ h₃ h₁₂ h₁₃ h₂₃

example (W : WeierstrassCurve F) {e t : F}
    (h : W.toAffine.Nonsingular e t)
    (htor : 2 • (Affine.Point.some e t h) = 0) :
    2 * t + W.a₁ * e + W.a₃ = 0 :=
  two_torsion_y_condition W h htor

example (W : WeierstrassCurve F)
    {e₁ e₂ e₃ t₁ x y : F}
    (hσ₁ : 4 * (e₁ + e₂ + e₃) = -(W.a₁ ^ 2 + 4 * W.a₂))
    (hz : (2 * y + W.a₁ * x + W.a₃) ^ 2 =
      4 * (x - e₁) * (x - e₂) * (x - e₃))
    (hTtwo : 2 * t₁ + W.a₁ * e₁ + W.a₃ = 0)
    (hxe : x ≠ e₁) :
    (e₂ - W.toAffine.addX e₁ x (W.toAffine.slope e₁ x t₁ y)) *
        (x - e₁) = (e₂ - e₁) * (x - e₃) :=
  translated_root_difference_general W hσ₁ hz hTtwo hxe

example (W : WeierstrassCurve F)
    {e₁ e₂ e₃ t₁ x y : F}
    (h₁ : W.twoTorsionPolynomial.toPoly.eval e₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval e₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval e₃ = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (hσ₁ : 4 * (e₁ + e₂ + e₃) = -(W.a₁ ^ 2 + 4 * W.a₂))
    (hTtwo : 2 * t₁ + W.a₁ * e₁ + W.a₃ = 0)
    (hQ : W.toAffine.Equation x y) (hxe : x ≠ e₁) :
    (e₂ - W.toAffine.addX e₁ x (W.toAffine.slope e₁ x t₁ y)) *
        (x - e₁) = (e₂ - e₁) * (x - e₃) :=
  translated_root_difference_general_of_roots W h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
    hσ₁ hTtwo hQ hxe

example (W : WeierstrassCurve F)
    (s : Finset ι) (x y : ι → F)
    (t₁ e₁ e₂ e₃ : F)
    (h₁ : W.twoTorsionPolynomial.toPoly.eval e₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval e₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval e₃ = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (hσ₁ : 4 * (e₁ + e₂ + e₃) = -(W.a₁ ^ 2 + 4 * W.a₂))
    (hTtwo : 2 * t₁ + W.a₁ * e₁ + W.a₃ = 0)
    (hEq : ∀ q ∈ s, W.toAffine.Equation (x q) (y q))
    (hxe : ∀ q ∈ s, x q ≠ e₁) :
    (∏ q ∈ s, (e₂ - W.toAffine.addX e₁ (x q)
      (W.toAffine.slope e₁ (x q) t₁ (y q)))) *
        (∏ q ∈ s, (x q - e₁)) =
      (e₂ - e₁) ^ s.card * ∏ q ∈ s, (x q - e₃) :=
  translated_root_product_relation_general W s x y t₁ e₁ e₂ e₃
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hσ₁ hTtwo hEq hxe

#print axioms
  DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral.two_torsion_root_sum
#print axioms
  DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral.two_torsion_y_condition
#print axioms
  DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral.translated_root_difference_general
#print axioms
  DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral.translated_root_difference_general_of_roots
#print axioms
  DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslateGeneral.translated_root_product_relation_general

end DkMathTest.WeierstrassTwoTorsionTranslateGeneral
