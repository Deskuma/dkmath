/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_Point_vcInvFun_add.lean.
Upstream blob: 1f15a16634107da49dcfd4ffe712cd5beeb61138
Modified for DkMath: explicit owner namespace, thin imports and textbook documentation.
-/

import DkMath.Lib.NumberTheory.WeierstrassVariableChange

#print "file: DkMath.Lib.NumberTheory.WeierstrassVariableChangeHom"

/-!
# 変数変換による実点の加法同型

[DkMath.Lib] 反対点ではOへ落ち、他の二点では弦または接線の傾きを使う。
傾き・和の二座標を変換公式へ一致させることで、座標の同値を加法同型へ昇格する。
一般の体上で成立し、代数閉性や楕円性、主因子の追加仮定は不要。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassVariableChange
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {K : Type*} [Field K]

section Formulas

variable (C : VariableChange K) (W : WeierstrassCurve.Affine K)

variable {C W}

/-- [DkMath.Lib] 単元倍率の非零性を加法公式でも使用する。 -/
theorem vcAdd_u_ne_zero : (C.u : K) ≠ 0 := C.u.ne_zero

/-- [DkMath.Lib] x座標の変換は単射。 -/
theorem vcX_injective : Function.Injective (vcX C) := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX] at h
  have : (C.u : K) ^ 2 * a = (C.u : K) ^ 2 * b := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 2 hu) this

/-- [DkMath.Lib] xを固定したy座標の変換も単射。 -/
theorem vcY_injective (x' : K) : Function.Injective (vcY C x') := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcY] at h
  have : (C.u : K) ^ 3 * a = (C.u : K) ^ 3 * b := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 3 hu) this

/-- [DkMath.Lib] 反転のy座標公式は変数変換と可換。 -/
theorem negY_variableChange (x' y' : K) :
    W.negY (vcX C x') (vcY C x' y') = vcY C x' ((C • W).toAffine.negY x' y') := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- [DkMath.Lib] 二点が反対点になる条件を両方向に輸送する。 -/
theorem Yeq_variableChange_iff (x₁' x₂' y₁' y₂' : K) :
    (vcX C x₁' = vcX C x₂' ∧ vcY C x₁' y₁' = W.negY (vcX C x₂') (vcY C x₂' y₂'))
      ↔ (x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂') := by
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : x₁' = x₂' := vcX_injective hx
    subst hx'
    refine ⟨rfl, ?_⟩
    rw [negY_variableChange x₁' y₂'] at hy
    exact vcY_injective x₁' hy
  · rintro ⟨hx, hy⟩
    subst hx
    exact ⟨rfl, by rw [negY_variableChange x₁' y₂', hy]⟩

/-- [DkMath.Lib] 弦・接線の傾きはu倍してsを加えた値になる。 -/
theorem slope_variableChange [DecidableEq K] (x₁' x₂' y₁' y₂' : K)
    (h₁ : (C • W).toAffine.Equation x₁' y₁') (h₂ : (C • W).toAffine.Equation x₂' y₂')
    (hxy : ¬(x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂')) :
    W.slope (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') (vcY C x₂' y₂')
      = (C.u : K) * (C • W).toAffine.slope x₁' x₂' y₁' y₂' + C.s := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  by_cases hx : x₁' = x₂'
  · have hy : y₁' ≠ (C • W).toAffine.negY x₂' y₂' := fun h => hxy ⟨hx, h⟩
    have hyy : y₁' = y₂' := (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    subst hx
    subst hyy
    have hyW : vcY C x₁' y₁' ≠ W.negY (vcX C x₁') (vcY C x₁' y₁') := by
      intro h
      exact hy ((Yeq_variableChange_iff x₁' x₁' y₁' y₁').mp ⟨rfl, h⟩).2
    rw [slope_of_Y_ne rfl hyW, slope_of_Y_ne rfl hy]
    have hd : vcY C x₁' y₁' - W.negY (vcX C x₁') (vcY C x₁' y₁')
        = (C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁') := by
      rw [negY_variableChange x₁' y₁']
      simp only [vcY]
      ring
    have hPYden : y₁' - (C • W).toAffine.negY x₁' y₁'
        = 2 * y₁' + (C • W).a₁ * x₁' + (C • W).a₃ := by
      simp only [negY]
      ring
    have hn : 3 * vcX C x₁' ^ 2 + 2 * W.a₂ * vcX C x₁' + W.a₄ - W.a₁ * vcY C x₁' y₁'
        = (C.u : K) ^ 4 * (3 * x₁' ^ 2 + 2 * (C • W).a₂ * x₁'
            + (C • W).a₄ - (C • W).a₁ * y₁')
          + C.s * ((C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁')) := by
      have hX := partialX_aux (C := C) (W := W) x₁' y₁'
      have hY := partialY_aux (C := C) (W := W) x₁' y₁'
      rw [hPYden]
      linear_combination (-1 : K) * hX + C.s * hY
    have hden' : y₁' - (C • W).toAffine.negY x₁' y₁' ≠ 0 := sub_ne_zero_of_ne hy
    rw [hd, hn]
    field_simp
  · have hxW : vcX C x₁' ≠ vcX C x₂' := fun h => hx (vcX_injective h)
    rw [slope_of_X_ne hxW, slope_of_X_ne hx]
    have hd : vcX C x₁' - vcX C x₂' = (C.u : K) ^ 2 * (x₁' - x₂') := by
      simp only [vcX]; ring
    have hn : vcY C x₁' y₁' - vcY C x₂' y₂'
        = (C.u : K) ^ 3 * (y₁' - y₂') + (C.u : K) ^ 2 * C.s * (x₁' - x₂') := by
      simp only [vcY]; ring
    rw [hd, hn]
    have hxne : x₁' - x₂' ≠ 0 := sub_ne_zero_of_ne hx
    field_simp

/-- [DkMath.Lib] 傾きの変換を代入すると、和のx座標も同じ変換に従う。 -/
theorem addX_variableChange (x₁' x₂' L : K) :
    W.addX (vcX C x₁') (vcX C x₂') ((C.u : K) * L + C.s)
      = vcX C ((C • W).toAffine.addX x₁' x₂' L) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [addX, vcX, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- [DkMath.Lib] 和のy座標も同じ変換に従う。 -/
theorem addY_variableChange (x₁' x₂' y₁' L : K) :
    W.addY (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') ((C.u : K) * L + C.s)
      = vcY C ((C • W).toAffine.addX x₁' x₂' L) ((C • W).toAffine.addY x₁' x₂' y₁' L) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [addY, negAddY, addX, negY, vcX, vcY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

end Formulas


variable {C : VariableChange K} {W : WeierstrassCurve.Affine K}

/-- [DkMath.Lib] 二座標の一致を同じ実点の一致へ戻す。 -/
theorem some_of_eq_of_eq {V : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  rfl

variable [DecidableEq K]

/-- [DkMath.Lib] 反対点・弦・接線を区別し、同じ点の変換が加法を保つことを証明する。 -/
theorem vcFun_add (P Q : (C • W).toAffine.Point) :
    vcFun C W (P + Q) = vcFun C W P + vcFun C W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2, vcFun_zero]
    change (0 : W.Point) = Point.some (vcX C x₁) (vcY C x₁ y₁) _ + Point.some (vcX C x₂) (vcY C x₂ y₂) _
    have hxyW := (Yeq_variableChange_iff (W := W) x₁ x₂ y₁ y₂).mpr hxy
    exact (add_of_Y_eq hxyW.1 hxyW.2).symm
  · have hxyW : ¬(vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = W.negY (vcX C x₂) (vcY C x₂ y₂)) :=
      fun h => hxy ((Yeq_variableChange_iff x₁ x₂ y₁ y₂).mp h)
    have hslope := slope_variableChange (W := W) x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    rw [add_some hxy]
    change Point.some _ _ _ = Point.some (vcX C x₁) (vcY C x₁ y₁) _ + Point.some (vcX C x₂) (vcY C x₂ y₂) _
    rw [add_some hxyW]
    refine some_of_eq_of_eq ?_ ?_
    · rw [hslope, addX_variableChange]
    · rw [hslope, addY_variableChange]

/-- [DkMath.Lib] 逆の点関数の加法性は、単射な順方向へ戻して証明する。 -/
theorem vcInvFun_add (P Q : W.Point) :
    vcInvFun C W (P + Q) = vcInvFun C W P + vcInvFun C W Q := by
  apply vcFun_leftInverse.injective
  rw [vcFun_add, vcFun_rightInverse P, vcFun_rightInverse Q, vcFun_rightInverse (P + Q)]



/-- [DkMath.Lib] 変換後から元への点の同値は、実際の加法同型である。 -/
noncomputable def variableChangeAddEquiv (C : VariableChange K) (W : WeierstrassCurve K) :
    (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  { variableChangeEquiv C W with map_add' := vcFun_add }

/-- [DkMath.Lib] 変数変換の点加法同型は、同じ座標変換をそのまま使用する。 -/
theorem variableChangeAddEquiv_apply (C : VariableChange K) (W : WeierstrassCurve K)
    (P : (C • W).toAffine.Point) : variableChangeAddEquiv C W P = vcFun C W P := rfl

end DkMath.Lib.NumberTheory.WeierstrassVariableChange
