/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Valuation.Basic

#print "file: DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel"

/-!
# 共通分母とWeierstrass重みによる、明示的な整数係数モデル

[DkMath.Lib] 五つの有理係数の分母の積dは非零であり、各係数をd倍すれば整数になる。
重み1,2,3,4,6に従い、a_iをd^i倍する。この操作は倍率u=d⁻¹の変数変換である。
整数モデルを係数ごとに構成し、そのℚへの写像が同じ変数変換と一致することを証明する。
判別式はd¹²倍、c₄はd⁴倍となる。整数モデルの判別式は非零だが、ℤ上の単元とは限らない。
最小モデルや、dを割る素数での還元保持を主張しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
open WeierstrassCurve

/-- [DkMath.Lib] 五つの係数の分母の積。最小分母を選ぶ追加の探索を要求しない。 -/
def commonDenominator (W : WeierstrassCurve ℚ) : ℕ :=
  W.a₁.den * W.a₂.den * W.a₃.den * W.a₄.den * W.a₆.den

/-- [DkMath.Lib] 有理数の分母は正なので、同じ共通分母も非零。 -/
theorem commonDenominator_ne_zero (W : WeierstrassCurve ℚ) : commonDenominator W ≠ 0 := by
  simp only [commonDenominator, ne_eq, mul_eq_zero, Rat.den_ne_zero, or_self, not_false_eq_true]

/-- [DkMath.Lib] 五つの係数の分母は、それぞれ同じ共通分母を割る。 -/
theorem denominators_dvd (W : WeierstrassCurve ℚ) :
    W.a₁.den ∣ commonDenominator W ∧ W.a₂.den ∣ commonDenominator W ∧
    W.a₃.den ∣ commonDenominator W ∧ W.a₄.den ∣ commonDenominator W ∧
    W.a₆.den ∣ commonDenominator W := by
  unfold commonDenominator
  refine ⟨⟨W.a₂.den * W.a₃.den * W.a₄.den * W.a₆.den, ?_⟩,
    ⟨W.a₁.den * W.a₃.den * W.a₄.den * W.a₆.den, ?_⟩,
    ⟨W.a₁.den * W.a₂.den * W.a₄.den * W.a₆.den, ?_⟩,
    ⟨W.a₁.den * W.a₂.den * W.a₃.den * W.a₆.den, ?_⟩,
    ⟨W.a₁.den * W.a₂.den * W.a₃.den * W.a₄.den, ?_⟩⟩ <;> ring

/-- [DkMath.Lib] 分母がdを割る係数の重み付き整数化。自然数の除算は整数の構成段階に置く。 -/
def weightedCoefficient (q : ℚ) (d w : ℕ) : ℤ :=
  (d : ℤ) ^ (w - 1) * (d / q.den : ℕ) * q.num

/-- [DkMath.Lib] 重み付き整数係数をℚへ戻すと、正確にd^w qになる。 -/
theorem weightedCoefficient_cast (q : ℚ) (d w : ℕ) (hd : q.den ∣ d) (hw : 1 ≤ w) :
    (weightedCoefficient q d w : ℚ) = (d : ℚ) ^ w * q := by
  have hq : (q.den : ℚ) * q = q.num := by
    calc
      (q.den : ℚ) * q = q.den * ((q.num : ℚ) / q.den) := congrArg (fun r : ℚ => q.den * r) q.num_div_den.symm
      _ = q.num := by field_simp
  unfold weightedCoefficient
  push_cast
  rw [← hq]
  calc
    (d : ℚ) ^ (w - 1) * (d / q.den : ℕ) * ((q.den : ℚ) * q) =
        (d : ℚ) ^ (w - 1) * ((d / q.den : ℕ) * (q.den : ℚ)) * q := by ring
    _ = (d : ℚ) ^ (w - 1) * d * q := by rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
    _ = (d : ℚ) ^ w * q := by rw [← pow_succ, Nat.sub_add_cancel hw]

/-- [DkMath.Lib] d⁻¹を倍率とし、平行移動・剪断を行わない同じ有理変数変換。 -/
noncomputable def clearingChange (W : WeierstrassCurve ℚ) : VariableChange ℚ :=
  ⟨(Units.mk0 (commonDenominator W : ℚ) (Nat.cast_ne_zero.mpr (commonDenominator_ne_zero W)))⁻¹, 0, 0, 0⟩

/-- [DkMath.Lib] 重み1,2,3,4,6の同じ五係数から構成する実際のℤモデル。 -/
def integerModel (W : WeierstrassCurve ℚ) : WeierstrassCurve ℤ where
  a₁ := weightedCoefficient W.a₁ (commonDenominator W) 1
  a₂ := weightedCoefficient W.a₂ (commonDenominator W) 2
  a₃ := weightedCoefficient W.a₃ (commonDenominator W) 3
  a₄ := weightedCoefficient W.a₄ (commonDenominator W) 4
  a₆ := weightedCoefficient W.a₆ (commonDenominator W) 6

/-- [DkMath.Lib] 整数モデルをℚへ写すと、同じ元の曲線の明示的変数変換になる。 -/
theorem integerModel_map (W : WeierstrassCurve ℚ) :
    (integerModel W).map (Int.castRingHom ℚ) = clearingChange W • W := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := denominators_dvd W
  ext <;> simp only [integerModel, map, clearingChange, variableChange_def, inv_inv, Units.val_mk0,
    mul_zero, zero_mul, sub_zero, add_zero, Int.coe_castRingHom] <;> norm_num
  · simpa only [pow_one] using weightedCoefficient_cast W.a₁ (commonDenominator W) 1 h₁ (by decide)
  · simpa only [pow_one] using weightedCoefficient_cast W.a₂ (commonDenominator W) 2 h₂ (by decide)
  · simpa only [pow_one] using weightedCoefficient_cast W.a₃ (commonDenominator W) 3 h₃ (by decide)
  · simpa only [pow_one] using weightedCoefficient_cast W.a₄ (commonDenominator W) 4 h₄ (by decide)
  · simpa only [pow_one] using weightedCoefficient_cast W.a₆ (commonDenominator W) 6 h₆ (by decide)

/-- [DkMath.Lib] 同じ整数モデルの判別式は、ℚ上でd¹²Δに一致する。 -/
theorem integerModel_discriminant (W : WeierstrassCurve ℚ) :
    ((integerModel W).Δ : ℚ) = (commonDenominator W : ℚ) ^ 12 * W.Δ := by
  have h := congrArg WeierstrassCurve.Δ (integerModel_map W)
  simpa only [map_Δ, Int.coe_castRingHom, variableChange_Δ, clearingChange, inv_inv, Units.val_mk0] using h

/-- [DkMath.Lib] 同じ整数モデルのc₄は、ℚ上でd⁴c₄に一致する。 -/
theorem integerModel_c4 (W : WeierstrassCurve ℚ) :
    ((integerModel W).c₄ : ℚ) = (commonDenominator W : ℚ) ^ 4 * W.c₄ := by
  have h := congrArg WeierstrassCurve.c₄ (integerModel_map W)
  simpa only [map_c₄, Int.coe_castRingHom, variableChange_c₄, clearingChange, inv_inv, Units.val_mk0] using h

/-- [DkMath.Lib] 同じ整数モデルのc₆は、ℚ上でd⁶c₆に一致する。 -/
theorem integerModel_c6 (W : WeierstrassCurve ℚ) :
    ((integerModel W).c₆ : ℚ) = (commonDenominator W : ℚ) ^ 6 * W.c₆ := by
  have h := congrArg WeierstrassCurve.c₆ (integerModel_map W)
  simpa only [map_c₆, Int.coe_castRingHom, variableChange_c₆, clearingChange, inv_inv, Units.val_mk0] using h

/-- [DkMath.Lib] 拡大係数dが付値1の場所では、同じ整数化モデルの判別式の付値は変わらない。
dを割る場所や、核による商を取る前後の比較はこの命題に含めない。 -/
theorem integerModel_discriminant_value {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (W : WeierstrassCurve ℚ) (v : Valuation ℚ Γ) (hd : v (commonDenominator W : ℚ) = 1) :
    v ((integerModel W).Δ : ℚ) = v W.Δ := by
  rw [integerModel_discriminant, map_mul, map_pow, hd, one_pow, one_mul]

/-- [DkMath.Lib] 同じ単元倍率の場所ではc₄の付値も正確に保存される。 -/
theorem integerModel_c4_value {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (W : WeierstrassCurve ℚ) (v : Valuation ℚ Γ) (hd : v (commonDenominator W : ℚ) = 1) :
    v ((integerModel W).c₄ : ℚ) = v W.c₄ := by
  rw [integerModel_c4, map_mul, map_pow, hd, one_pow, one_mul]

/-- [DkMath.Lib] 元が楕円曲線なら整数モデルの判別式も非零。整数上の単元性とは区別する。 -/
theorem integerModel_discriminant_ne_zero (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    (integerModel W).Δ ≠ 0 := by
  have h : ((integerModel W).Δ : ℚ) ≠ 0 := by
    rw [integerModel_discriminant]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (commonDenominator_ne_zero W)))
      (isUnit_iff_ne_zero.mp W.isUnit_Δ)
  exact Int.cast_ne_zero.mp h

/-- [DkMath.Lib] 同じ整数モデルのℚ係数曲線は楕円性を保つ。 -/
theorem integerModel_map_isElliptic (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ((integerModel W).map (Int.castRingHom ℚ)).IsElliptic := by
  rw [integerModel_map]
  infer_instance

end DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
