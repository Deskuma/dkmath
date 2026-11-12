/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Modified for DkMath: local namespaces, current Mathlib API and characteristic-zero specialization.
Adapted from anthropics/fermats-last-theorem, Definitions/Def_WeierstrassCurve_EDSEngine.lean.
-/

import DkMath.Lib.NumberTheory.EllipticDivisionSequence

#print "file: DkMath.Lib.NumberTheory.EllipticDivisionUniversal"

/-!
# 標数0の普遍Weierstrass曲線と、その点の特殊化

五つの係数を有理数体上の独立変数とし、座標環の分数体に普遍点を置く。
座標環の関係式そのものが曲線方程式なので、任意の方程式を満たす点へ評価できる。
有理係数を使うのは、次章でy座標の分子を2で割って定義するためである。
この選択により一般環の2除算を扱う大きな補完列の実装を省ける。
適用先は標数0の曲線に限定する。正標数の場合の幾何学的providerは別の課題となる。
-/
namespace DkMath.Lib.NumberTheory.EllipticDivision

open scoped WeierstrassCurve.Affine
section PortEllSequenceUniversal

noncomputable section

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

open _root_.WeierstrassCurve

inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

namespace Affine.CoordinateRing

open _root_.WeierstrassCurve.Affine.CoordinateRing

lemma algebraMap_injective' {R : Type*} [CommRing R] (W : Affine R) :
    Function.Injective (algebraMap R W.CoordinateRing) := by
  have h : Function.Injective (algebraMap (Polynomial R) W.CoordinateRing) :=
    (injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
      smul_basis_eq_zero (W' := W) (q := 0) <| by
        rw [smul, smul, mul_one, Polynomial.C_0, map_zero, zero_mul, add_zero]
        exact hp
  exact h.comp Polynomial.C_injective

end Affine.CoordinateRing

namespace Univ

open scoped Polynomial Polynomial.Bivariate
open Coeff

open MvPolynomial (X) in
/-- 五つの独立な有理係数を持つ普遍Weierstrass曲線。 -/
def curve : Affine (MvPolynomial Coeff ℚ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

abbrev Poly : Type := (MvPolynomial Coeff ℚ)[X][Y]

protected abbrev Ring : Type := curve.CoordinateRing

protected abbrev Field : Type := FractionRing Univ.Ring

instance : CommRing Poly := Polynomial.commRing

lemma Poly.two_ne_zero : (2 : Poly) ≠ 0 :=
  Polynomial.C_ne_zero.mpr <| Polynomial.C_ne_zero.mpr fun h ↦ two_ne_zero' (α := ℚ) <|
    MvPolynomial.C_injective _ _ <| by rwa [← MvPolynomial.C_0] at h

def polyToField : Poly →+* Univ.Field := (algebraMap Univ.Ring _).comp <| AdjoinRoot.mk _

lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Univ.Ring _ (AdjoinRoot.mk _ p) := rfl

lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℚ) Univ.Field = polyToField.comp (algebraMap _ _) := rfl

lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℚ) Univ.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl

@[simp] lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℚ) Univ.Field) :=
  (IsFractionRing.injective Univ.Ring Univ.Field).comp
    (Affine.CoordinateRing.algebraMap_injective' _)

abbrev pointedCurve : WeierstrassCurve Univ.Field :=
  baseChange curve Univ.Field

instance : pointedCurve.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by
    simpa only [pointedCurve, _root_.WeierstrassCurve.baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
      using Δ_curve_ne_zero

open Polynomial in
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  simp_rw [Affine.Equation, pointedCurve, baseChange, algebraMap_field_eq_comp, ← _root_.WeierstrassCurve.map_map,
    Affine.map_polynomial, map_mapRingHom_evalEval, evalEval, eval_map,
    eval_C_X_eval₂_map_C_X, polyToField_polynomial]

open Polynomial Affine in
/-- 普遍曲線の座標環の分数体上に存在する実際の非特異な点。 -/
def Affine.point : curve⟮Univ.Field⟯ :=
  .some (polyToField (C X)) (polyToField Y)
    ((pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
      (by simpa only [pointedCurve, _root_.WeierstrassCurve.baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
        using Δ_curve_ne_zero)).mp equation_point)

def Jacobian.point : Jacobian.Point (WeierstrassCurve.baseChange curve Univ.Field) :=
  Jacobian.Point.fromAffine Affine.point

open Polynomial (CC)

@[simp] lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl
@[simp] lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := rfl
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl
@[simp] lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := rfl
@[simp] lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl

abbrev curvePoly : WeierstrassCurve Poly := WeierstrassCurve.baseChange curve Poly

abbrev curveRing : WeierstrassCurve Univ.Ring :=
  WeierstrassCurve.baseChange curve Univ.Ring

abbrev curveField : WeierstrassCurve Univ.Field :=
  WeierstrassCurve.baseChange curve Univ.Field

lemma curveField_eq : curveField = pointedCurve := rfl

end Univ

def cusp : Affine ℚ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma cusp_equation_one_one : cusp.Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]

open Univ
variable {R} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)

/-- 独立な五係数を、対象の曲線の実際の五係数へ評価する準同型。 -/
def specialize : MvPolynomial Coeff ℚ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

lemma map_specialize : WeierstrassCurve.map Univ.curve (specialize W) = W := by
  simp [specialize, curve, map]

namespace Univ

variable (x y : R)

open Polynomial (eval₂RingHom) in
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom (specialize W) x) y

open Polynomial in
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom (specialize W)).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : Affine.Equation W x y)

open Polynomial in
/-- 曲線方程式を満たす点への評価は、座標環の剰余関係を保つ。 -/
def ringEval : Univ.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom (specialize W) x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rw [← Affine.map_polynomial]
    simpa only [Affine.map, map_specialize, Affine.Equation, evalEval, coe_evalRingHom] using eqn

lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = (specialize W) := by
  ext <;> simp [polyEval]

lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = (specialize W) := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

protected lemma Field.two_ne_zero : (2 : Univ.Field) ≠ 0 := by
  rw [← map_ofNat (algebraMap Univ.Ring _), map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  intro h; replace h := congr(ringEval cusp_equation_one_one $h)
  rw [map_ofNat, map_zero] at h; norm_num at h

lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W := by
  rw [curveRing, WeierstrassCurve.baseChange, map_map, ringEval_comp_eq_specialize, map_specialize]

end Univ

end WeierstrassCurve

end

end PortEllSequenceUniversal


end DkMath.Lib.NumberTheory.EllipticDivision
