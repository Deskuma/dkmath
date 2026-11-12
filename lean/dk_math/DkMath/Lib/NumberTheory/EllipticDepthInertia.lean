/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionDepth
import DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia

#print "file: DkMath.Lib.NumberTheory.EllipticDepthInertia"

/-!
# NOTE-031-002: 整数の尺度を持つ浅いtorsion点は慣性に固定される

中心からのX差を慣性固定の尺度bで割って単元にすると、慣性合同から座標差は元の深さより小さい。
中心傾きも整なので慣性で同じ枝に留まる。C5の鋭い差の評価と、差点のtorsion整性により、
非零の差点は矛盾する。一般の零成分部分群や新しい固定性のproviderを仮定しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticDepthInertia
open WeierstrassCurve EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections EllipticShallowSlope
open EllipticTorsionRepresentation ValuationInertia ValuationPrimeSupport

/-- 慣性固定の非零尺度bと同じ付値を持つxでは、慣性による差はxより厳密に小さい。
正規化したx/bは単元なので、付値群を実数や整数へ同一視せず合同を適用できる。 -/
theorem inertia_difference_of_fixed_scale {K F : Type*} [Field K] [Field F] [Algebra F K]
    (A : ValuationSubring K) (σ : K ≃ₐ[F] K) (hσ : σ ∈ inertiaSubgroupIn A F)
    {b x : K} (hb : b ≠ 0) (hfix : σ b = b) (hdepth : A.valuation x = A.valuation b) :
    A.valuation (σ x - x) < A.valuation x ∧ A.valuation (σ x) = A.valuation x := by
  have hvb : 0 < A.valuation b := (Valuation.pos_iff _).mpr hb
  have hu : A.valuation (x / b) = 1 := by rw [map_div₀, hdepth, div_self (ne_of_gt hvb)]
  have hcong := inertia_apply_sub_mem_nonunits A F σ hσ ((A.valuation_le_one_iff _).mp hu.le)
  have hc : A.valuation (σ (x / b) - x / b) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hcong
  have hid : σ x - x = (σ (x / b) - x / b) * b := by
    rw [map_div₀, hfix, sub_mul, div_mul_cancel₀ _ hb, div_mul_cancel₀ _ hb]
  have hd : A.valuation (σ x - x) < A.valuation x := by
    rw [hid, map_mul, hdepth]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hc hvb
  refine ⟨hd, ?_⟩
  have he : σ x = (σ x - x) + x := by ring
  rw [he, Valuation.map_add_eq_of_lt_right _ hd]

/-- 同じ深さ・同じ枝の単元位数torsion二点で、X差がその深さより小さければ二点は等しい。
差点が有限なら除法多項式から整性を供給し、鋭いX差の等式に反する。 -/
theorem torsion_eq_of_strict_depth_difference {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    {A : ValuationSubring K} (M : WeierstrassCurve A) (E : WeierstrassCurve K) (hmodel : M.map A.subtype = E)
    (C : CriticalCentre A E) (D : TangentDirections C) {n : ℕ} (hn : A.valuation (n : K) = 1)
    {x₁ y₁ x₂ y₂ : K} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (ht₁ : n • Affine.Point.some x₁ y₁ h₁ = 0) (ht₂ : n • Affine.Point.some x₂ y₂ h₂ = 0)
    (hX₁ : A.valuation (x₁ - C.x) < 1) (hX₂ : A.valuation (x₂ - C.x) < 1)
    (hlev : A.valuation (x₁ - C.x) = A.valuation (x₂ - C.x))
    (hsh : A.valuation (equationDefect E C.x C.y) < A.valuation (x₁ - C.x) ^ 2)
    (hbr : A.valuation (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) < 1)
    (hdiff : A.valuation (x₁ - x₂) < A.valuation (x₁ - C.x)) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  have hkill : n • (Affine.Point.some x₁ y₁ h₁ - Affine.Point.some x₂ y₂ h₂) = 0 := by
    rw [nsmul_sub, ht₁, ht₂, sub_self]
  cases hr : (Affine.Point.some x₁ y₁ h₁ - Affine.Point.some x₂ y₂ h₂) with
  | zero => exact sub_eq_zero.mp hr
  | some x y h =>
    have ht : n • Affine.Point.some x y h = 0 := hr ▸ hkill
    have hx := EllipticTorsionValuationIntegrality.torsion_x_mem A M E hmodel hn h ht
    have hsharp := (EllipticBranchComparison.sub_of_same_branch_of_model M E hmodel C D h₁ h₂ hX₁ hX₂ hlev hsh hbr).2 h hr hx
    exact (hdiff.ne hsharp).elim

/-- 同じ有理曲線の浅い有限torsion点で、中心が慣性固定かつX深さが有理尺度で表せれば、その点は固定される。
尺度・中心・点を全て同じまま保ち、二点の等号は実際の点群で結論する。 -/
theorem finite_point_fixed_of_rational_depth [DecidableEq (AlgebraicClosure ℚ)] (E : WeierstrassCurve ℚ) (n : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : WeierstrassCurve A)
    (hmodel : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (hn : A.valuation (n : AlgebraicClosure ℚ) = 1)
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (hfix : σ C.x = C.x ∧ σ C.y = C.y)
    {x y : AlgebraicClosure ℚ} (h : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (ht : n • Affine.Point.some x y h = 0) (hX : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect (E.baseChange (AlgebraicClosure ℚ)) C.x C.y) < A.valuation (x - C.x) ^ 2)
    (a : ℚ) (ha : a ≠ 0) (hdepth : A.valuation (x - C.x) = A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) a)) :
    Affine.Point.map σ.toAlgHom (Affine.Point.some x y h) = Affine.Point.some x y h := by
  classical
  have hscale : σ (algebraMap ℚ (AlgebraicClosure ℚ) a) = algebraMap ℚ (AlgebraicClosure ℚ) a := σ.commutes a
  have hab : algebraMap ℚ (AlgebraicClosure ℚ) a ≠ 0 := by
    intro hz
    apply ha
    apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    simpa only [map_zero] using hz
  obtain ⟨hd, hlev⟩ := inertia_difference_of_fixed_scale A σ hσ hab hscale hdepth
  rw [map_sub σ, hfix.1] at hd hlev
  have htint := (slope_mem_and_branches_of_shallow D h.1 hX hsh).1
  have htc := inertia_apply_sub_mem_nonunits A ℚ σ hσ htint
  have htval : A.valuation (σ (centreSlope C x y) - centreSlope C x y) < 1 :=
    (ValuationSubring.mem_nonunits_iff _).mp htc
  have htc_eq : σ (centreSlope C x y) = centreSlope C (σ x) (σ y) := by
    simp only [centreSlope, map_div₀, map_sub, hfix.1, hfix.2]
  rw [htc_eq] at htval
  have h₂ := (E.toAffine.baseChange_nonsingular σ.toAlgHom.injective x y).mpr h
  have ht₂ : n • Affine.Point.some (σ x) (σ y) h₂ = 0 := by
    have he := congrArg (Affine.Point.map σ.toAlgHom) ht
    rw [map_nsmul, Affine.Point.map_some, map_zero] at he
    exact he
  rw [Affine.Point.map_some]
  apply torsion_eq_of_strict_depth_difference M _ hmodel C D hn h₂ h ht₂ ht (by change A.valuation (σ x - C.x) < 1; rwa [hlev]) hX hlev
    (by change A.valuation (equationDefect _ C.x C.y) < A.valuation (σ x - C.x) ^ 2; rwa [hlev]) htval
  change A.valuation (σ x - x) < A.valuation (σ x - C.x)
  rw [hlev]
  simpa only [sub_sub_sub_cancel_right] using hd

end DkMath.Lib.NumberTheory.EllipticDepthInertia
