/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelSpecialization
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelPoles
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelModel

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelSpecialization"

/-!
同じy²=x³−x、H={O,(1,0)}、R=(−1,0)で実点への特殊化を検査する。
一般座標の値、実点の有限和、方程式、2捩れ三次式の根への着地を確認する。
自明核では実際の標的楕円性を供給して全点写像の零ファイバーと軌道不変性を検査する。
三根判定は相異なる0,1,−1で閉じ、特異曲線では分離条件が欠落することも検査する。
-/
namespace EllipticFiniteKernelSpecializationTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation EllipticFunctionField
open EllipticPointEvaluation WeierstrassTwoTorsionSeparation
open EllipticFiniteKernelTest EllipticFiniteKernelPolesTest
open scoped BigOperators
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : DecidableEq (Points curve) := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype kernel := Fintype.ofFinset {0, Q} (fun P => by simp [kernel])

/-- 一般座標を同じ実点Rで評価すると、(−1,0)へ戻る。 -/
theorem actual_generic_values :
    value curve R (genericX curve (AlgebraicClosure ℚ))
      (pointValuation_genericX_le_one curve R (Point.some_ne_zero _)) = -1 ∧
    value curve R (genericY curve (AlgebraicClosure ℚ))
      (pointValuation_genericY_le_one curve R (Point.some_ne_zero _)) = 0 := by
  rw [value_genericX curve R (Point.some_ne_zero _),
    value_genericY curve R (Point.some_ne_zero _)]
  constructor
  · change algebraMap ℚ (AlgebraicClosure ℚ) (-1 : ℚ) = -1
    simp
  · change algebraMap ℚ (AlgebraicClosure ℚ) (0 : ℚ) = 0
    simp

/-- 源の実際の群法でR+(1,0)の二座標は0となる。 -/
theorem R_add_Q_coordinates : (R + Q).xc = 0 ∧ (R + Q).yc = 0 := by
  let T : curve.toAffine.Point := .some 0 0 (by norm_num [curve, nonsingular_iff', equation_iff])
  have hs : rationalR + rationalQ = T := by
    have h₁ : curve.toAffine.Nonsingular (-1) 0 := by norm_num [curve, nonsingular_iff', equation_iff]
    have h₂ : curve.toAffine.Nonsingular 1 0 := by norm_num [curve, nonsingular_iff', equation_iff]
    exact (Point.add_of_X_ne (W := curve.toAffine) (h₁ := h₁) (h₂ := h₂)
      (by norm_num : (-1 : ℚ) ≠ 1)).trans (by
        dsimp only [T]
        refine Eq.mpr (Point.some.injEq _ _ _ _ _ _) ?_
        norm_num [addX, addY, WeierstrassCurve.Affine.slope, negY, curve, T])
  have he := (baseChangePointHom curve).map_add rationalR rationalQ
  change baseChangePoint curve (rationalR + rationalQ) = R + Q at he
  rw [← he, hs]
  constructor <;> change algebraMap ℚ (AlgebraicClosure ℚ) (0 : ℚ) = 0 <;> exact map_zero _

/-- 同じ二元核・同じ実点の特殊化座標を、実点和から具体値として計算する。 -/
theorem actual_kernel_values :
    kernelXAt curve kernel R R_outside = -2 ∧ kernelYAt curve kernel R R_outside = 0 := by
  rw [kernelXAt_eq_sum, kernelYAt_eq_sum, sum_kernel, sum_kernel, sum_kernel, sum_kernel]
  have hx : R.xc = -1 := by change algebraMap ℚ (AlgebraicClosure ℚ) (-1 : ℚ) = -1; simp
  have hy : R.yc = 0 := by change algebraMap ℚ (AlgebraicClosure ℚ) (0 : ℚ) = 0; simp
  simp only [AddSubgroup.coe_zero, add_zero, hx, hy, R_add_Q_coordinates.1,
    R_add_Q_coordinates.2]
  have hxQ : Q.xc = 1 := rfl
  have hyQ : Q.yc = 0 := by change algebraMap ℚ (AlgebraicClosure ℚ) (0 : ℚ) = 0; simp
  rw [hxQ, hyQ]
  change (-1 - (0 + 1) : AlgebraicClosure ℚ) = -2 ∧ (0 - (0 + 0) : AlgebraicClosure ℚ) = 0
  norm_num

/-- 得られた(−2,0)は、同じ標的方程式の実際の解である。 -/
theorem actual_specialized_equation : (kernelModel curve kernel).toAffine.Equation (-2) 0 := by
  have h := kernelAt_equation curve kernel R R_outside
  rwa [actual_kernel_values.1, actual_kernel_values.2] at h

/-- Rは反転固定点であり、その特殊化x=−2は標的2捩れ三次式の根である。 -/
theorem actual_twoTorsion_root :
    (kernelModel curve kernel).twoTorsionPolynomial.toPoly.eval (-2) = 0 := by
  have hn : -R = R := by
    change -Point.some _ _ _ = Point.some _ _ _
    simp only [Point.neg_some]
    congr 1
    norm_num [negY, curve, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have h := kernelAt_twoTorsion_root curve kernel R R_outside hn
  rwa [actual_kernel_values.1] at h

/-- H上の極には、有限評価の正則性証明を供給できない。 -/
theorem evaluation_pole_guard : ¬pointValuation curve Q (veluX curve kernel) ≤ 1 := by
  exact not_le.mpr ((velu_pole_support curve kernel Q).1.mpr (Or.inr rfl))

/-- 三つの相異なる反転固定解による判別式判定を、元の実曲線で検査する。 -/
theorem three_roots_discriminant : curve.Δ ≠ 0 := by
  apply discriminant_ne_zero_of_three_fixed_solutions curve (by norm_num)
    ![0, 1, -1] ![0, 0, 0]
  · intro i; fin_cases i <;> norm_num [curve, equation_iff]
  · intro i; fin_cases i <;> norm_num [curve]
  · intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *

/-- 尖点曲線では、三つの相異なる反転固定解という入力を供給できない。 -/
theorem cusp_separation_guard :
    ¬∃ x y : Fin 3 → ℚ,
      (∀ i, (EllipticFiniteKernelModelTest.cusp ℚ).toAffine.Equation (x i) (y i)) ∧
      (∀ i, y i = -y i) ∧ Function.Injective x := by
  rintro ⟨x, y, he, hn, hx⟩
  have h := discriminant_ne_zero_of_three_fixed_solutions
    (EllipticFiniteKernelModelTest.cusp ℚ) (by norm_num) x y he (by simpa [EllipticFiniteKernelModelTest.cusp] using hn) hx
  exact h (EllipticFiniteKernelModelTest.cusp_discriminant ℚ)


local instance : Fintype (⊥ : AddSubgroup (Points curve)) := Fintype.ofFinite _
local instance : (kernelModel curve ⊥).IsElliptic := by
  rw [EllipticFiniteKernelModelTest.trivial_model]
  infer_instance

/-- 自明核では標的楕円性を実際に供給でき、全点写像の零ファイバーは{O}になる。 -/
theorem trivial_zero_fiber (P : Points curve) : kernelPointMap curve ⊥ P = 0 ↔ P = 0 := by
  simpa only [AddSubgroup.mem_bot] using kernelPointMap_eq_zero_iff curve ⊥ P

/-- 同じ二元核の有限値は、RとR+Qで一致する。標的楕円性を入力しない。 -/
theorem actual_orbit_values :
    kernelXAt curve kernel (R + Q) (add_not_mem_kernel curve kernel R R_outside ⟨Q, Or.inr rfl⟩) = -2 ∧
    kernelYAt curve kernel (R + Q) (add_not_mem_kernel curve kernel R R_outside ⟨Q, Or.inr rfl⟩) = 0 := by
  rw [kernelXAt_translation curve kernel R R_outside ⟨Q, Or.inr rfl⟩,
    kernelYAt_translation curve kernel R R_outside ⟨Q, Or.inr rfl⟩]
  exact actual_kernel_values

/-- RのH軌道全体が、標的2捩れ三次式の同じ根へ着地する。 -/
theorem actual_orbit_twoTorsion_root :
    (kernelModel curve kernel).twoTorsionPolynomial.toPoly.eval
      (kernelXAt curve kernel (R + Q)
        (add_not_mem_kernel curve kernel R R_outside ⟨Q, Or.inr rfl⟩)) = 0 := by
  have h := kernelAt_twoTorsion_root_translation curve kernel R R_outside
    (by
      change -Point.some _ _ _ = Point.some _ _ _
      simp only [Point.neg_some]
      congr 1
      norm_num [negY, curve, WeierstrassCurve.baseChange, WeierstrassCurve.map])
    ⟨Q, Or.inr rfl⟩
  exact h

/-- 偶数核では異なる実点R,R+Qのx像が一致する。
三つの2捩れ像の分離を任意の有限核へ無条件に拡張してはならない。 -/
theorem even_kernel_collision :
    R + Q ≠ R ∧ kernelXAt curve kernel (R + Q)
      (add_not_mem_kernel curve kernel R R_outside ⟨Q, Or.inr rfl⟩) = kernelXAt curve kernel R R_outside := by
  constructor
  · intro h
    have he : R + Q = R + 0 := h.trans (add_zero R).symm
    exact point_data.1 (add_left_cancel he)
  · exact kernelXAt_translation curve kernel R R_outside ⟨Q, Or.inr rfl⟩

end
end EllipticFiniteKernelSpecializationTest
