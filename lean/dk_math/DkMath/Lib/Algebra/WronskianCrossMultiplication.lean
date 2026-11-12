/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import Mathlib.Algebra.Polynomial.Derivative
import DkMath.Lib.Algebra.RationalPolynomialFiber

#print "file: DkMath.Lib.Algebra.WronskianCrossMultiplication"

/-!
# 交差乗算による Wronskian 輸送

`F / G = A / D` を多項式の交差乗算
`F * D = A * G` として保持すると、形式微分は

`W(F,G) * D² = W(A,D) * G²`

を与える。この等式は分母を割らずに成立するため、後で有限点へ評価する際に
必要な非零条件を明示的に分離できる。Vélu の共通分母対から標準 `RatFunc`
分子分母対へ Wronskian 零点を輸送する一般代数の教科書補題である。
-/

namespace DkMath.Lib.Algebra

open Polynomial RationalPolynomialFiber

variable {R : Type*} [Field R]

variable {S : Type*} [Field S] [Algebra R S]

/-
The coefficient-descent step is often presented as an informal cancellation of
fractions.  The following lemma makes its two guards explicit: both evaluated
denominators are non-zero, and the evaluation element is transcendental over
the coefficient field.  The latter is exactly what makes polynomial
evaluation injective, so no false ``evaluation is injective'' principle over a
function field is used.
-/

/-- A rational-function equality at a transcendental element yields a polynomial cross relation. -/
theorem cross_relation_of_aeval_div_eq
    (F G A D : R[X]) (x : S)
    (hx : Transcendental R x)
    (hG : Polynomial.aeval x G ≠ 0)
    (hD : Polynomial.aeval x D ≠ 0)
    (hrel : Polynomial.aeval x F / Polynomial.aeval x G =
      Polynomial.aeval x A / Polynomial.aeval x D) :
    F * D = A * G := by
  have hcross_eval : Polynomial.aeval x F * Polynomial.aeval x D =
      Polynomial.aeval x A * Polynomial.aeval x G :=
    (div_eq_div_iff hG hD).mp hrel
  apply (transcendental_iff_injective.mp hx)
  simpa only [map_mul] using hcross_eval

/-- 交差乗算の多項式恒等式は Wronskian を二乗因子付きで輸送する。 -/
theorem wronskian_mul_denominator_sq_eq
    (F G A D : R[X]) (hcross : F * D = A * G) :
    wronskian F G * D ^ 2 = wronskian A D * G ^ 2 := by
  have hcross' := congrArg derivative hcross
  simp only [derivative_mul] at hcross'
  unfold wronskian
  linear_combination
    D * G * hcross' - (D.derivative * G + G.derivative * D) * hcross

/-
The preceding identity is useful only after it is evaluated at a finite point.
The next lemma records the exact cancellation rule needed there: a zero of the
Wronskian for the common-denominator pair transports to a zero of the standard
numerator/denominator pair as soon as the common denominator does not vanish.
Notice that no assertion about the existence of the cross relation is hidden in
this lemma; producing that relation from the function-field presentation is a
separate coefficient-descent obligation.
-/

/-- A non-vanishing common denominator transports a Wronskian root. -/
theorem wronskian_isRoot_of_cross_relation
    (F G A D : R[X]) (x : R)
    (hcross : F * D = A * G)
    (hD : D.eval x ≠ 0)
    (hAD : (wronskian A D).IsRoot x) :
    (wronskian F G).IsRoot x := by
  change (wronskian F G).eval x = 0
  have htransport := congrArg (fun p : R[X] => p.eval x)
    (wronskian_mul_denominator_sq_eq F G A D hcross)
  rw [eval_mul, eval_pow, eval_mul, eval_pow] at htransport
  change (wronskian A D).eval x = 0 at hAD
  rw [hAD, zero_mul] at htransport
  exact (mul_eq_zero.mp htransport).resolve_right (pow_ne_zero 2 hD)

/-- The converse cancellation rule uses non-vanishing of the standard denominator. -/
theorem wronskian_isRoot_of_cross_relation_rev
    (F G A D : R[X]) (x : R)
    (hcross : F * D = A * G)
    (hG : G.eval x ≠ 0)
    (hFG : (wronskian F G).IsRoot x) :
    (wronskian A D).IsRoot x := by
  change (wronskian A D).eval x = 0
  have htransport := congrArg (fun p : R[X] => p.eval x)
    (wronskian_mul_denominator_sq_eq F G A D hcross)
  rw [eval_mul, eval_pow, eval_mul, eval_pow] at htransport
  change (wronskian F G).eval x = 0 at hFG
  have hzero : (wronskian A D).eval x * G.eval x ^ 2 = 0 := by
    simpa [hFG] using htransport
  exact (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero 2 hG)

/-
This is the final scalar cancellation in the geometric specialization.  The
identity is deliberately stated after evaluation: all regularity and
denominator obligations belong to the preceding specialization theorem, while
this lemma only expresses that a non-zero source completed-square coordinate
cannot annihilate a non-zero Wronskian value.
-/

/-- A cleared completed-square identity forces a Wronskian root. -/
theorem wronskian_isRoot_of_denominator_cleared_identity
    (A D : R[X]) (x z zH : R)
    (hidentity : D.eval x ^ 2 * zH = z * (wronskian A D).eval x)
    (hz : z ≠ 0) (hzH : zH = 0) :
    (wronskian A D).IsRoot x := by
  change (wronskian A D).eval x = 0
  have hzero : z * (wronskian A D).eval x = 0 := by
    rw [← hidentity, hzH, mul_zero]
  exact (mul_eq_zero.mp hzero).resolve_left hz

end DkMath.Lib.Algebra
