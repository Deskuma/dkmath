/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicInt
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion

#print "file: DkMath.FLT.Seven.SevenRealCubicEisenstein"

namespace DkMath.FLT.Seven

open Polynomial

noncomputable section

namespace SevenRealCubicInt

/-- The translated generator adapted to the unique prime above seven. -/
def eisensteinAxis : SevenRealCubicInt :=
  ⟨-3, 1, 0⟩

theorem eisensteinAxis_eq :
    eisensteinAxis = alpha - 3 := by
  change eisensteinAxis = alpha - ofInt 3
  ext <;> norm_num [eisensteinAxis, alpha]

/-- Minimal-polynomial candidate of the translated generator. -/
def eisensteinPolynomial : ℤ[X] :=
  C 1 * X ^ 3 + C 7 * X ^ 2 + C 14 * X + C 7

theorem eisensteinAxis_relation :
    eisensteinAxis ^ 3 +
        7 * eisensteinAxis ^ 2 +
        14 * eisensteinAxis + 7 = 0 := by
  change
    eisensteinAxis ^ 3 +
        ofInt 7 * eisensteinAxis ^ 2 +
        ofInt 14 * eisensteinAxis + ofInt 7 = 0
  ext <;> norm_num [eisensteinAxis, mul, pow_succ]

theorem eisensteinAxis_cube :
    eisensteinAxis ^ 3 =
      -7 * (eisensteinAxis + 1) ^ 2 := by
  change
    eisensteinAxis ^ 3 =
      -ofInt 7 * (eisensteinAxis + 1) ^ 2
  ext <;> norm_num [eisensteinAxis, mul, pow_succ]

theorem eisensteinPolynomial_aeval :
    aeval eisensteinAxis eisensteinPolynomial = 0 := by
  rw [eisensteinPolynomial]
  simp only [map_add, map_mul, map_pow, aeval_X, map_one, map_ofNat]
  exact eisensteinAxis_relation

theorem eisensteinPolynomial_monic :
    eisensteinPolynomial.Monic := by
  rw [Monic.def, eisensteinPolynomial]
  exact
    leadingCoeff_cubic (a := (1 : ℤ)) (b := 7) (c := 14) (d := 7)
      (by norm_num)

theorem eisensteinPolynomial_natDegree :
    eisensteinPolynomial.natDegree = 3 := by
  rw [eisensteinPolynomial]
  exact
    natDegree_cubic (a := (1 : ℤ)) (b := 7) (c := 14) (d := 7)
      (by norm_num)

theorem eisensteinPolynomial_degree :
    eisensteinPolynomial.degree = 3 := by
  rw [eisensteinPolynomial]
  exact
    degree_cubic (a := (1 : ℤ)) (b := 7) (c := 14) (d := 7)
      (by norm_num)

/-- The power basis `1, θ, θ²` has discriminant `49`. -/
theorem eisensteinPolynomial_discr :
    eisensteinPolynomial.discr = 49 := by
  rw [discr_of_degree_eq_three eisensteinPolynomial_degree]
  norm_num [eisensteinPolynomial, coeff_X]

/-- The translated polynomial is Eisenstein at `(7)`. -/
theorem eisensteinPolynomial_isEisensteinAt :
    eisensteinPolynomial.IsEisensteinAt
      (Ideal.span ({(7 : ℤ)} : Set ℤ)) := by
  refine eisensteinPolynomial_monic.isEisensteinAt_of_mem_of_notMem
    (Ideal.IsPrime.ne_top <|
      (Ideal.span_singleton_prime (by norm_num : (7 : ℤ) ≠ 0)).2
        (by norm_num : Prime (7 : ℤ))) ?_ ?_
  · intro n hn
    rw [eisensteinPolynomial_natDegree] at hn
    interval_cases n <;>
      norm_num [eisensteinPolynomial, Ideal.mem_span_singleton, coeff_X]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [eisensteinPolynomial]

theorem eisensteinPolynomial_irreducible :
    Irreducible eisensteinPolynomial := by
  apply eisensteinPolynomial_isEisensteinAt.irreducible
  · exact
      (Ideal.span_singleton_prime (by norm_num : (7 : ℤ) ≠ 0)).2
        (by norm_num : Prime (7 : ℤ))
  · exact eisensteinPolynomial_monic.isPrimitive
  · rw [eisensteinPolynomial_natDegree]
    norm_num

theorem eisensteinPolynomial_map_rat_irreducible :
    Irreducible
      (eisensteinPolynomial.map (algebraMap ℤ ℚ)) :=
  eisensteinPolynomial_monic
    |>.irreducible_iff_irreducible_map_fraction_map
    |>.mp eisensteinPolynomial_irreducible

/-- The nontrivial cyclic rotation sends `alpha` to `alpha² - 2 alpha`. -/
def rotateHom : SevenRealCubicInt →+* SevenRealCubicInt where
  toFun x := ⟨x.fst + 2 * x.thd, -2 * x.snd - 3 * x.thd,
    x.snd + x.thd⟩
  map_zero' := by ext <;> norm_num
  map_one' := by ext <;> norm_num
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by ext <;> simp <;> ring

@[simp] theorem rotateHom_fst (x : SevenRealCubicInt) :
    (rotateHom x).fst = x.fst + 2 * x.thd := rfl

@[simp] theorem rotateHom_snd (x : SevenRealCubicInt) :
    (rotateHom x).snd = -2 * x.snd - 3 * x.thd := rfl

@[simp] theorem rotateHom_thd (x : SevenRealCubicInt) :
    (rotateHom x).thd = x.snd + x.thd := rfl

theorem rotateHom_three (x : SevenRealCubicInt) :
    rotateHom (rotateHom (rotateHom x)) = x := by
  ext <;> simp <;> ring

/-- The order-three integral automorphism of the real cubic order. -/
def rotateEquiv : SevenRealCubicInt ≃+* SevenRealCubicInt where
  __ := rotateHom
  invFun x := rotateHom (rotateHom x)
  left_inv := rotateHom_three
  right_inv x := rotateHom_three x

@[simp] theorem rotateEquiv_apply (x : SevenRealCubicInt) :
    rotateEquiv x = rotateHom x := rfl

theorem rotateEquiv_alpha :
    rotateEquiv alpha = alpha ^ 2 - 2 * alpha := by
  change rotateEquiv alpha = alpha ^ 2 - ofInt 2 * alpha
  ext <;> norm_num [rotateEquiv, rotateHom, alpha, mul, pow_two]

theorem rotateEquiv_sq_alpha :
    rotateEquiv (rotateEquiv alpha) =
      -alpha ^ 2 + alpha + 2 := by
  change rotateEquiv (rotateEquiv alpha) =
    -alpha ^ 2 + alpha + ofInt 2
  ext <;> norm_num [rotateEquiv, rotateHom, alpha, mul, pow_two]

theorem rotateEquiv_three (x : SevenRealCubicInt) :
    rotateEquiv (rotateEquiv (rotateEquiv x)) = x := by
  exact rotateHom_three x

/-- Explicit inverse of `alpha`. -/
def alphaInv : SevenRealCubicInt :=
  ⟨1, 2, -1⟩

theorem alpha_mul_inv :
    alpha * alphaInv = 1 := by
  ext <;> norm_num [alpha, alphaInv, mul]

theorem alpha_isUnit : IsUnit alpha :=
  IsUnit.of_mul_eq_one alphaInv alpha_mul_inv

/-- Explicit inverse of `1 + alpha`. -/
def alphaAddOneInv : SevenRealCubicInt :=
  ⟨2, -3, 1⟩

theorem alphaAddOne_mul_inv :
    (1 + alpha) * alphaAddOneInv = 1 := by
  ext <;> norm_num [alpha, alphaAddOneInv, mul]

theorem alphaAddOne_isUnit : IsUnit (1 + alpha) :=
  IsUnit.of_mul_eq_one alphaAddOneInv alphaAddOne_mul_inv

/-- The unit adjacent to the Eisenstein axis. -/
def eisensteinAxisUnit : SevenRealCubicInt :=
  eisensteinAxis + 1

def eisensteinAxisUnitInv : SevenRealCubicInt :=
  ⟨-1, 0, 1⟩

theorem eisensteinAxisUnit_eq :
    eisensteinAxisUnit = alpha - 2 := by
  change eisensteinAxisUnit = alpha - ofInt 2
  ext <;> norm_num [eisensteinAxisUnit, eisensteinAxis, alpha]

theorem eisensteinAxisUnit_mul_inv :
    eisensteinAxisUnit * eisensteinAxisUnitInv = 1 := by
  ext <;>
    norm_num [eisensteinAxisUnit, eisensteinAxis, eisensteinAxisUnitInv,
      alpha, mul]

theorem eisensteinAxisUnit_isUnit : IsUnit eisensteinAxisUnit :=
  IsUnit.of_mul_eq_one eisensteinAxisUnitInv
    eisensteinAxisUnit_mul_inv

/-- The norm-friendly axis from RAMIFIED-009 and the Eisenstein axis differ
by the displayed product of two explicit units. -/
theorem ramifiedAxis_eq_eisensteinAxis_mul_units :
    ramifiedAxis =
      -eisensteinAxis * alpha * (1 + alpha) := by
  ext <;>
    norm_num [ramifiedAxis, eisensteinAxis, alpha, mul, pow_two]

theorem ramifiedAxis_associated_eisensteinAxis :
    Associated ramifiedAxis eisensteinAxis := by
  rw [ramifiedAxis_eq_eisensteinAxis_mul_units]
  rw [show -eisensteinAxis * alpha * (1 + alpha) =
      eisensteinAxis * (-(alpha * (1 + alpha))) by ring]
  exact associated_mul_unit_left _ _
    ((alpha_isUnit.mul alphaAddOne_isUnit).neg)


end SevenRealCubicInt

end

end DkMath.FLT.Seven
