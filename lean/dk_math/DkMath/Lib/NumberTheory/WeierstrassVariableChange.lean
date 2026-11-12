/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean.
Upstream blob: 93376fed97aefdb39c2ff3173013fbb5c1288d12
Modified for DkMath: explicit owner namespace, thin imports and textbook documentation.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

#print "file: DkMath.Lib.NumberTheory.WeierstrassVariableChange"

/-!
# 変数変換の座標と実際の点の往復

[DkMath.Lib] C=(u,r,s,t)は、変換後の点から元の点へ
x=u²x'+r、y=u³y'+u²sx'+tで戻す。逆方向はuの逆数を使う。
曲線方程式の差はu⁶倍であり、偏微分のu³・u⁴倍の公式から非特異性も同値となる。
Oを保つ実際の点の同値を構成する。加法性は次の所有者で証明する。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassVariableChange
open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K]

section Formulas

variable (C : VariableChange K) (W : WeierstrassCurve.Affine K)

/-- [DkMath.Lib] 変換後のx座標から元のx座標へ戻す。 -/
def vcX (x' : K) : K := (C.u : K) ^ 2 * x' + C.r

/-- [DkMath.Lib] 変換後の二座標から元のy座標へ戻す。 -/
def vcY (x' y' : K) : K := (C.u : K) ^ 3 * y' + (C.u : K) ^ 2 * C.s * x' + C.t

/-- [DkMath.Lib] 元のx座標を変換後のx座標へ送る。 -/
def vcXInv (x : K) : K := ((C.u⁻¹ : Kˣ) : K) ^ 2 * (x - C.r)

/-- [DkMath.Lib] 元の二座標を変換後のy座標へ送る。 -/
def vcYInv (x y : K) : K := ((C.u⁻¹ : Kˣ) : K) ^ 3 * (y - C.t - C.s * (x - C.r))

variable {C W}

/-- [DkMath.Lib] 変数変換の倍率は単元なので非零。 -/
private lemma u_ne_zero : (C.u : K) ≠ 0 := C.u.ne_zero
/-- [DkMath.Lib] 倍率の全ての自然数冪も非零。 -/
private lemma u_pow_ne_zero (n : ℕ) : ((C.u : K)) ^ n ≠ 0 := pow_ne_zero n C.u.ne_zero

/-- [DkMath.Lib] x座標の逆変換の後で元へ戻すと元の値。 -/
@[simp] lemma vcX_vcXInv (x : K) : vcX C (vcXInv C x) = x := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

/-- [DkMath.Lib] y座標についても逆変換と変換が相殺する。 -/
@[simp] lemma vcY_vcYInv (x y : K) : vcY C (vcXInv C x) (vcYInv C x y) = y := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcY, vcXInv, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

/-- [DkMath.Lib] 変換後のx座標について逆順の往復も恒等。 -/
@[simp] lemma vcXInv_vcX (x' : K) : vcXInv C (vcX C x') = x' := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

/-- [DkMath.Lib] 変換後のy座標について逆順の往復も恒等。 -/
@[simp] lemma vcYInv_vcY (x' y' : K) : vcYInv C (vcX C x') (vcY C x' y') = y' := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

/-- [DkMath.Lib] 曲線方程式の差は、変換後の差のu⁶倍。 -/
private lemma equation_aux (x' y' : K) :
    vcY C x' y' ^ 2 + W.a₁ * vcX C x' * vcY C x' y' + W.a₃ * vcY C x' y'
      - (vcX C x' ^ 3 + W.a₂ * vcX C x' ^ 2 + W.a₄ * vcX C x' + W.a₆)
    = (C.u : K) ^ 6 *
      (y' ^ 2 + (C • W).a₁ * x' * y' + (C • W).a₃ * y'
        - (x' ^ 3 + (C • W).a₂ * x' ^ 2 + (C • W).a₄ * x' + (C • W).a₆)) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp; ring

/-- [DkMath.Lib] x偏微分とs倍のy偏微分の和は、変換後のx偏微分のu⁴倍。 -/
lemma partialX_aux (x' y' : K) :
    W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄)
      + C.s * (2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃)
    = (C.u : K) ^ 4 *
      ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp; ring

/-- [DkMath.Lib] y偏微分は変換後のy偏微分のu³倍。 -/
lemma partialY_aux (x' y' : K) :
    2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃
      = (C.u : K) ^ 3 * (2 * y' + (C • W).a₁ * x' + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp; ring

/-- [DkMath.Lib] 同じ実際の座標変換は曲線方程式を満たす条件と同値。 -/
lemma equation_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Equation x' y' ↔ W.Equation (vcX C x') (vcY C x' y') := by
  rw [equation_iff', equation_iff', equation_aux x' y', mul_eq_zero,
    or_iff_right (u_pow_ne_zero 6)]

/-- [DkMath.Lib] 二つの偏微分が共に零となる条件も同値。 -/
private lemma partials_zero_iff (x' y' : K) :
    ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄) = 0
        ∧ 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0)
      ↔ (W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄) = 0
        ∧ 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0) := by
  constructor
  · rintro ⟨hX', hY'⟩
    have hY : 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0 := by
      rw [partialY_aux x' y', hY', mul_zero]
    refine ⟨?_, hY⟩
    have hX := partialX_aux (C := C) (W := W) x' y'
    rw [hX', mul_zero, hY, mul_zero, add_zero] at hX
    exact hX
  · rintro ⟨hX, hY⟩
    have hY' : 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0 := by
      have h := partialY_aux (C := C) (W := W) x' y'
      rw [hY] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (u_pow_ne_zero 3)
    refine ⟨?_, hY'⟩
    have h := partialX_aux (C := C) (W := W) x' y'
    rw [hX, hY, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (u_pow_ne_zero 4)

/-- [DkMath.Lib] 方程式と偏微分の比較から、非特異性を正確に輸送する。 -/
lemma nonsingular_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Nonsingular x' y' ↔ W.Nonsingular (vcX C x') (vcY C x' y') := by
  rw [nonsingular_iff', nonsingular_iff', equation_variableChange_iff x' y']
  refine and_congr_right fun _ => not_iff_not.mp ?_
  push Not
  exact partials_zero_iff x' y'

end Formulas

section PointEquiv

variable (C : VariableChange K) (W : WeierstrassCurve.Affine K)


/-- [DkMath.Lib] 変換後の実点を元の曲線の実点へ戻す。OはOへ送る。 -/
def vcFun : (C • W).toAffine.Point → W.Point
  | 0 => 0
  | .some x' y' h => .some (vcX C x') (vcY C x' y')
      ((nonsingular_variableChange_iff x' y').mp h)

/-- [DkMath.Lib] 元の実点を変換後の曲線の実点へ送る。 -/
def vcInvFun : W.Point → (C • W).toAffine.Point
  | 0 => 0
  | .some x y h => .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv]))

variable {C W}

/-- [DkMath.Lib] 元へ戻す点関数はOを保つ。 -/
@[simp] lemma vcFun_zero : vcFun C W 0 = 0 := rfl
/-- [DkMath.Lib] 変換後へ送る点関数もOを保つ。 -/
@[simp] lemma vcInvFun_zero : vcInvFun C W 0 = 0 := rfl

/-- [DkMath.Lib] 二座標が一致する非特異点は同じ実点である。 -/
private lemma some_eq_some {W' : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

/-- [DkMath.Lib] 点の変換と逆変換の左逆性。 -/
lemma vcFun_leftInverse : Function.LeftInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x', y', h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcXInv_vcX x') (vcYInv_vcY x' y')

/-- [DkMath.Lib] 点の変換と逆変換の右逆性。 -/
lemma vcFun_rightInverse : Function.RightInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcX_vcXInv x) (vcY_vcYInv x y)

variable (C W) in
/-- [DkMath.Lib] 同じ曲線の二つのWeierstrass表示の間の実点の同値。 -/
noncomputable def variableChangeEquiv : (C • W).toAffine.Point ≃ W.Point :=
  ⟨vcFun C W, vcInvFun C W, vcFun_leftInverse, vcFun_rightInverse⟩

/-- [DkMath.Lib] 変換後モデルの等式を指定した実点の同値。 -/
noncomputable def equivOfVariableChangeEq {V : WeierstrassCurve.Affine K}
    (h : C • W = V) : V.Point ≃ W.Point := by
  subst h; exact variableChangeEquiv C W


end PointEquiv

end DkMath.Lib.NumberTheory.WeierstrassVariableChange
