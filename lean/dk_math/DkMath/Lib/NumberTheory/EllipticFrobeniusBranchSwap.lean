/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight.lean,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Modified: same DkMath centre/directions and branch comparison; separate residue arithmetic
from shallow-point geometry; reuse proved centre fixedness and Frobenius existence APIs.
-/

import DkMath.Lib.NumberTheory.ValuationQuadraticFrobenius
import DkMath.Lib.NumberTheory.ValuationResidue
import DkMath.Lib.NumberTheory.EllipticDyadicGeometry
import DkMath.Lib.NumberTheory.EllipticBranchComparison

#print "file: DkMath.Lib.NumberTheory.EllipticFrobeniusBranchSwap"

/-!
# NOTE-032-003C: 非分裂接錐のFrobeniusと浅い点の枝交換

[DkMath.Lib] 剰余a₁=a₂=1、中心の剰余X座標=0なら、接線方向も浅い点の中心傾きも
z²+z=1を満たす。2乗Frobeniusの変化量は単元である。
中心は2上の分解群に固定されるので、方向は交換され、点の中心からの深さは保存される。
同じ深さ・異なる枝の二点の和の定理から、σP+Pは滑らかに還元する。

浅い点の条件はここでは明示する。捩れ点が浅いこととFrey係数の合同条件はconsumerで供給する。
零成分内の点や臨界側の点まで結論を拡張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFrobeniusBranchSwap
open WeierstrassCurve IsLocalRing ValuationInertia ValuationPrimeSupport ValuationFrobenius
open EllipticCriticalCentre EllipticTangentDirections EllipticCriticalCentreAlgebra
open EllipticGoodReductionSeparation EllipticShallowSlope ValuationTameCharacter.TameCharacter

/-- [DkMath.Lib] a₁=1,a₃=0の整な中心では、2が非単元ならX座標も非単元となる。
Y偏微分の等式x₀=−2y₀と、既存のY座標の整性だけを使う。 -/
theorem centre_x_small_of_normalized {L : Type*} [Field L] {A : ValuationSubring L}
    {V : WeierstrassCurve L} (C : CriticalCentre A V)
    (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (h2 : A.valuation (2 : L) < 1) :
    A.valuation C.x < 1 := by
  have hY := C.derivativeY
  rw [ha₁, ha₃, one_mul, add_zero] at hY
  have he : C.x = -(2 * C.y) := by linear_combination hY
  rw [he, Valuation.map_neg, map_mul]
  exact (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).mpr C.y_mem)).trans_lt h2

/-- [DkMath.Lib] 接錐の二次式の小ささを、同じ剰余体上のz²+z=1へ輸送する。
モデル一致、中心、係数と中心の剰余を全て明示する。 -/
theorem quadratic_residue_eq_one {L : Type*} [Field L] {A : ValuationSubring L}
    (M : WeierstrassCurve A) (V : WeierstrassCurve L) (hmodel : M.map A.subtype = V)
    (C : CriticalCentre A V)
    (ha₁ : (M.map (residue A)).a₁ = 1) (ha₂ : (M.map (residue A)).a₂ = 1)
    (hx₀ : residue A (⟨C.x, C.x_mem⟩ : A) = 0)
    {z : L} (hz : z ∈ A)
    (hsmall : A.valuation (z ^ 2 + V.a₁ * z - (V.a₂ + 3 * C.x)) < 1) :
    residue A (⟨z, hz⟩ : A) ^ 2 + residue A (⟨z, hz⟩ : A) = 1 := by
  subst V
  let x₀ : A := ⟨C.x, C.x_mem⟩
  let t : A := ⟨z, hz⟩
  let f : A := t ^ 2 + M.a₁ * t - (M.a₂ + 3 * x₀)
  have hf : residue A f = 0 := by
    apply (ValuationResidue.coe_mem_nonunits_iff_residue_eq_zero A f).mp
    rw [ValuationSubring.mem_nonunits_iff]
    exact hsmall
  change residue A M.a₁ = 1 at ha₁
  change residue A M.a₂ = 1 at ha₂
  change residue A x₀ = 0 at hx₀
  simp only [f, map_sub, map_add, map_pow, map_mul, map_ofNat,
    ha₁, ha₂, hx₀, mul_zero, add_zero, one_mul] at hf
  exact sub_eq_zero.mp hf

/-- [DkMath.Lib] 非分裂接錐の分離した二方向を、実際の2乗Frobenius元が交換する。
中心固定は分解群所属から供給し、方向交換は剰余二次式と同じ根の因数分解で証明する。 -/
theorem directions_swap_of_frobenius (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (M : WeierstrassCurve A) (hmodel : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (ha₁ : (M.map (residue A)).a₁ = 1) (ha₂ : (M.map (residue A)).a₂ = 1)
    (hx₀ : residue A (⟨C.x, C.x_mem⟩ : A) = 0)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : IsFrobeniusAt A σ 2) :
    σ D.α = D.β ∧ σ D.β = D.α := by
  have : CharP (ResidueField A) 2 := charP_residueField A Nat.prime_two hA
  have hfix := EllipticDyadicGeometry.decomposition_fixed E A C
    ((ValuationSubring.mem_nonunits_iff _).mp hA) σ hσ.mem_decompositionSubgroup
  have hroot := quadratic_residue_eq_one M _ hmodel C ha₁ ha₂ hx₀ D.α_mem
    (by rw [D.roots.1, map_zero]; exact zero_lt_one)
  have hval := ValuationQuadraticFrobenius.valuation_apply_sub_eq_one A hσ D.α_mem hroot
  have hne : σ D.α ≠ D.α := by
    intro he
    rw [he, sub_self, map_zero] at hval
    exact zero_ne_one hval
  have hr : (σ D.α) ^ 2 + (E.baseChange (AlgebraicClosure ℚ)).a₁ * σ D.α -
      ((E.baseChange (AlgebraicClosure ℚ)).a₂ + 3 * C.x) = 0 := by
    simpa [WeierstrassCurve.baseChange, map_ofNat, hfix.1] using congrArg σ D.roots.1
  have hfac : (σ D.α - D.α) * (σ D.α - D.β) = 0 := by
    linear_combination hr - σ D.α * D.sum_eq + D.product_eq
  have hα : σ D.α = D.β := sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne))
  have hsum := congrArg σ D.sum_eq
  have e₁ : σ (E.baseChange (AlgebraicClosure ℚ)).a₁ = (E.baseChange (AlgebraicClosure ℚ)).a₁ := by
    simp [WeierstrassCurve.baseChange]
  simp only [map_add, map_neg, e₁, hα] at hsum
  exact ⟨hα, by linear_combination hsum - D.sum_eq⟩

/-- [DkMath.Lib] 浅い点の中心傾きは同じ剰余二次式の根となり、Frobenius変化量は単元である。
捩れの位数を使わず、浅さからの傾き整性を先に供給する。 -/
theorem slope_difference_of_frobenius (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (M : WeierstrassCurve A) (hmodel : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (ha₁ : (M.map (residue A)).a₁ = 1) (ha₂ : (M.map (residue A)).a₂ = 1)
    (hx₀ : residue A (⟨C.x, C.x_mem⟩ : A) = 0)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : IsFrobeniusAt A σ 2)
    {x y : AlgebraicClosure ℚ} (h : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Equation x y)
    (hX : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect (E.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
      A.valuation (x - C.x) ^ 2) :
    A.valuation (σ (centreSlope C x y) - centreSlope C x y) = 1 := by
  have : CharP (ResidueField A) 2 := charP_residueField A Nat.prime_two hA
  have hz := (slope_mem_and_branches_of_shallow D h hX hsh).1
  have hsmall := quadratic_small_of_shallow C h hX hsh
  exact ValuationQuadraticFrobenius.valuation_apply_sub_eq_one A hσ hz
    (quadratic_residue_eq_one M _ hmodel C ha₁ ha₂ hx₀ hz hsmall)

/-- [DkMath.Lib] 浅い点とそのFrobenius像は深さが等しく枝が異なるので、和は零成分へ入る。
実際の点の座標作用と加法を使い、傾きの剰余作用を商での符号反転へ接続する。 -/
theorem add_smooth_of_frobenius [DecidableEq (AlgebraicClosure ℚ)] (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (M : WeierstrassCurve A) (hmodel : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (ha₁ : (M.map (residue A)).a₁ = 1) (ha₂ : (M.map (residue A)).a₂ = 1)
    (hx₀ : residue A (⟨C.x, C.x_mem⟩ : A) = 0)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : IsFrobeniusAt A σ 2)
    {x y : AlgebraicClosure ℚ} (h : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hX : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect (E.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
      A.valuation (x - C.x) ^ 2) :
    HasSmoothReduction M (Affine.Point.map σ.toAlgHom (Affine.Point.some x y h) + Affine.Point.some x y h) := by
  have hfix := EllipticDyadicGeometry.decomposition_fixed E A C
    ((ValuationSubring.mem_nonunits_iff _).mp hA) σ hσ.mem_decompositionSubgroup
  have hlev : A.valuation (σ x - C.x) = A.valuation (x - C.x) := by
    rw [show σ x - C.x = σ (x - C.x) by rw [map_sub, hfix.1]]
    exact valuation_apply_eq hσ.mem_decompositionSubgroup _
  have hslope : σ (centreSlope C x y) = centreSlope C (σ x) (σ y) := by
    simp only [centreSlope, map_div₀, map_sub, hfix.1, hfix.2]
  have hbr : A.valuation (centreSlope C (σ x) (σ y) - centreSlope C x y) = 1 := by
    rw [← hslope]
    exact slope_difference_of_frobenius E A hA M hmodel C D ha₁ ha₂ hx₀ hσ h.1 hX hsh
  rw [Affine.Point.map_some]
  exact (EllipticBranchComparison.add_of_opposite_branch_of_model M _ hmodel C D _ h
    (hlev ▸ hX) hX hlev (by rwa [hlev]) hbr).1

end DkMath.Lib.NumberTheory.EllipticFrobeniusBranchSwap
