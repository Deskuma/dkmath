/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassIntegralModelTransport
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelHom

#print "file: DkMathTest.Lib.NumberTheory.WeierstrassIntegralModel"

/-!
分母を持つ実際の曲線y²=x³−x/16を用い、d=16による整数化と二捩れ点の輸送を検査する。
さらに前段の同じ非巡回9点核のℚ係数標的について、非零有理二捩れ像を整数モデルへ移す。
-/
namespace WeierstrassIntegralModelTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory WeierstrassRationalIntegralModel WeierstrassVariableChange
open EllipticTorsionRepresentation
noncomputable section

/-- 非自明な分母を持つ実際の有理係数曲線。 -/
def sample : WeierstrassCurve ℚ := ⟨0, 0, 0, -1 / 16, 0⟩

/-- 同じ曲線の判別式は1/64であり、楕円性を供給できる。 -/
theorem sample_discriminant : sample.Δ = 1 / 64 := by
  norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
local instance : sample.IsElliptic := ⟨by rw [sample_discriminant]; norm_num⟩

/-- 五係数の共通分母は実際に16であり、恒等変換だけの例ではない。 -/
theorem sample_denominator : commonDenominator sample = 16 := by
  norm_num [commonDenominator, sample]

/-- 同じ整数モデルはy²=x³−4096xになる。 -/
theorem sample_integer_model : integerModel sample = (⟨0, 0, 0, -4096, 0⟩ : WeierstrassCurve ℤ) := by
  ext <;> norm_num [integerModel, weightedCoefficient, commonDenominator, sample]

/-- 同じ整数判別式は16¹²/64であり非零。 -/
theorem sample_integer_discriminant : (integerModel sample).Δ = 4398046511104 := by
  rw [sample_integer_model]
  norm_num [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]

/-- 同じ曲線の実際の非零有理2捩れ点(1/4,0)。 -/
def samplePoint : sample.toAffine.Point := .some (1 / 4) 0 (by
  norm_num [sample, nonsingular_iff', equation_iff'])

/-- 整数化後の同じ非零有理点(64,0)。 -/
def integralPoint : (rationalModel sample).toAffine.Point := .some 64 0 (by
  norm_num [rationalModel, sample_integer_model, WeierstrassCurve.map, nonsingular_iff', equation_iff'])

/-- 実際の座標点(64,0)を元へ戻すと、同じ点(1/4,0)になる。 -/
theorem sample_point_transport : rationalPointEquiv sample integralPoint = samplePoint := by
  obtain ⟨h, he⟩ := rationalPointEquiv_some sample
    (show (rationalModel sample).toAffine.Nonsingular 64 0 from by
      norm_num [rationalModel, sample_integer_model, WeierstrassCurve.map, nonsingular_iff', equation_iff'])
  change rationalPointEquiv sample (Point.some _ _ _) = _
  rw [he]
  change Point.some _ _ _ = Point.some _ _ _
  congr 1 <;> norm_num [vcX, vcY, clearingChange, sample_denominator]

/-- 同じ整数化後の点は、実際の非零2捩れ点である。 -/
theorem integralPoint_nonzero_two_torsion : integralPoint ≠ 0 ∧ 2 • integralPoint = 0 := by
  refine ⟨Point.some_ne_zero _, ?_⟩
  change 2 • Point.some _ _ _ = 0
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  norm_num [negY, rationalModel, sample_integer_model, WeierstrassCurve.map]

/-- 同じ非零捩れ点の有理点の移送と幾何学的移送は、基底変換で一致する。 -/
theorem sample_baseChange_transport :
    geometricPointEquiv sample (baseChangePoint (rationalModel sample) integralPoint) =
      baseChangePoint sample samplePoint :=
  (geometricPointEquiv_baseChange sample integralPoint).trans
    (congrArg (baseChangePoint sample) sample_point_transport)

/-- dの付値1という条件下で、Δとc₄の付値が両方保持される。 -/
theorem sample_unit_place {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation ℚ Γ)
    (hd : v 16 = 1) :
    v ((integerModel sample).Δ : ℚ) = v sample.Δ ∧
      v ((integerModel sample).c₄ : ℚ) = v sample.c₄ := by
  have hd' : v (commonDenominator sample : ℚ) = 1 := by simpa only [sample_denominator, Nat.cast_ofNat] using hd
  exact ⟨integerModel_discriminant_value _ v hd', integerModel_c4_value _ v hd'⟩

/-- dが非単元となる2進場所では判別式付値が変わる。無条件の還元保持を防ぐ境界検査。 -/
theorem sample_dyadic_orders : padicValRat 2 sample.Δ = -6 ∧
    padicValRat 2 ((integerModel sample).Δ : ℚ) = 42 := by
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using padicValRat.self (by decide : 1 < 2)
  constructor
  · rw [sample_discriminant]
    have h : (1 / 64 : ℚ) = ((2 : ℚ) ^ 6)⁻¹ := by norm_num
    rw [h, padicValRat.inv, padicValRat.pow, h2]
    norm_num
  · rw [sample_integer_discriminant]
    have hv : padicValRat 2 ((2 : ℚ) ^ 42) = 42 := by
      rw [padicValRat.pow, h2]
      norm_num
    convert hv using 1
    norm_num

/-- 前段の同じ9点核のℚ係数標的の非零有理2捩れ像も、同じ整数化モデルへ運べる。 -/
theorem actual_kernel_target_integer_torsion :
    ∃ Q : (rationalModel EllipticFiniteKernelPointDescentTest.target).toAffine.Point,
      2 • Q = 0 ∧ Q ≠ 0 := by
  obtain ⟨R, _, hR, h2⟩ := EllipticFiniteKernelHomTest.actual_nonzero_rational_two_torsion
  obtain ⟨Q, hQ, hn, _⟩ := exists_nonzero_torsion_on_integerModel _ 2 R h2 hR
  exact ⟨Q, hQ, hn⟩

end
end WeierstrassIntegralModelTest
