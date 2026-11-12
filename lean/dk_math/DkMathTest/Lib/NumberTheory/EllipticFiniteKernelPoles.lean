/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelPoles
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernel

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelPoles"

/-!
005C₂bの実曲線検査。前回と同じE:y²=x³−x、Q=(1,0)、H={O,Q}を使う。
O,Qでの位数−2,−3、外側R=(−1,0)での正則性、総極位数4,6を検査する。
等しい値の二項なら相殺し得ることと、定数関数には極がないことも確認する。
-/
namespace EllipticFiniteKernelPolesTest
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation EllipticFunctionField
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFiniteKernelTest
open scoped BigOperators
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : DecidableEq (Points curve) := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype kernel := Fintype.ofFinset {0, Q} (fun P => by simp [kernel])

/-- 前回と同じ二元核のO,Qでは、二つの正規化関数の値はexp(2),exp(3)。
整数位数の符号は負となることも同じQで確認する。 -/
theorem actual_kernel_orders :
    pointValuation curve 0 (veluX curve kernel) = exp (2 : ℤ) ∧
    pointValuation curve 0 (veluY curve kernel) = exp (3 : ℤ) ∧
    pointValuation curve Q (veluX curve kernel) = exp (2 : ℤ) ∧
    pointValuation curve Q (veluY curve kernel) = exp (3 : ℤ) ∧
    pointOrder curve Q (veluX curve kernel) (veluX_ne_zero curve kernel) = -2 ∧
    pointOrder curve Q (veluY curve kernel) (veluY_ne_zero curve kernel) = -3 :=
  ⟨veluX_valuation_zero curve kernel, veluY_valuation_zero curve kernel,
    veluX_valuation_of_mem curve kernel Q (Or.inr rfl),
    veluY_valuation_of_mem curve kernel Q (Or.inr rfl),
    velu_orders_of_mem curve kernel Q (Or.inr rfl)⟩

/-- 実際の極集合は二点。極位数の総和は4,6であり、点の個数と区別する。 -/
theorem actual_total_poles :
    Nat.card {P : Points curve // 1 < pointValuation curve P (veluX curve kernel)} = 2 ∧
    Nat.card {P : Points curve // 1 < pointValuation curve P (veluY curve kernel)} = 2 ∧
    (∑ P : kernel, -pointOrder curve P.val (veluX curve kernel) (veluX_ne_zero curve kernel)) = 4 ∧
    (∑ P : kernel, -pointOrder curve P.val (veluY curve kernel) (veluY_ne_zero curve kernel)) = 6 := by
  have hc := card_velu_pole_support curve kernel
  have ht := velu_total_pole_orders curve kernel
  rw [degree_two.1] at hc ht
  exact ⟨hc.1, hc.2, by norm_num at ht; simpa only [Finset.sum_neg_distrib] using ht⟩

/-- 同じ曲線の別の有理2捩れ点(−1,0)。 -/
def rationalR : curve.toAffine.Point :=
  .some (-1) 0 (by norm_num [curve, nonsingular_iff', equation_iff])

/-- Rは同じ実点群へ基底変換した点である。 -/
def R : Points curve := baseChangePoint curve rationalR

/-- Rは実際に核Hの外にある。位数2というだけでは同じ二元部分群に所属しない。 -/
theorem R_outside : R ∉ kernel := by
  intro hR
  rcases hR with hz | he
  · exact Point.some_ne_zero _ hz
  · have h := congrArg Point.xc he
    have hRxc : R.xc = -1 := by
      change algebraMap ℚ (AlgebraicClosure ℚ) (-1 : ℚ) = -1
      simp
    have hQxc : Q.xc = 1 := rfl
    rw [hRxc, hQxc] at h
    norm_num at h

/-- 核の外の同じ点Rでは二関数は正則であり、極の支持から排除される。 -/
theorem actual_outside_regular :
    pointValuation curve R (veluX curve kernel) ≤ 1 ∧
      pointValuation curve R (veluY curve kernel) ≤ 1 ∧
      ¬ 1 < pointValuation curve R (veluX curve kernel) ∧
      ¬ 1 < pointValuation curve R (veluY curve kernel) :=
  ⟨veluX_regular_outside curve kernel R R_outside,
    veluY_regular_outside curve kernel R R_outside,
    mt (velu_pole_support curve kernel R).1.mp R_outside,
    mt (velu_pole_support curve kernel R).2.mp R_outside⟩

/-- 構成した二関数は、代数閉包の任意の定数と異なる。 -/
theorem actual_nonconstant (c : AlgebraicClosure ℚ) :
    veluX curve kernel ≠ algebraMap (AlgebraicClosure ℚ)
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField c ∧
      veluY curve kernel ≠ algebraMap (AlgebraicClosure ℚ)
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField c :=
  ⟨veluX_ne_const curve kernel c, veluY_ne_const curve kernel c⟩

/-- 同じ二関数はそれぞれ超越的であり、各々への多項式代入が単射である。
二変数の代数的独立性を主張していない。 -/
theorem actual_transcendental :
    Transcendental (AlgebraicClosure ℚ) (veluX curve kernel) ∧
      Transcendental (AlgebraicClosure ℚ) (veluY curve kernel) ∧
      Function.Injective (Polynomial.aeval (R := AlgebraicClosure ℚ) (veluX curve kernel)) ∧
      Function.Injective (Polynomial.aeval (R := AlgebraicClosure ℚ) (veluY curve kernel)) :=
  ⟨veluX_transcendental curve kernel, veluY_transcendental curve kernel,
    transcendental_iff_injective.mp (veluX_transcendental curve kernel),
    transcendental_iff_injective.mp (veluY_transcendental curve kernel)⟩

/-- 同じ大きい値を持つ二項は相殺し得る。唯一の最大項という厳密性を外せない。 -/
theorem cancellation_boundary :
    pointValuation curve 0 (genericX curve (AlgebraicClosure ℚ)) =
      pointValuation curve 0 (-genericX curve (AlgebraicClosure ℚ)) ∧
    pointValuation curve 0 (genericX curve (AlgebraicClosure ℚ) +
      -genericX curve (AlgebraicClosure ℚ)) = 0 ∧
    1 < pointValuation curve 0 (genericX curve (AlgebraicClosure ℚ)) := by
  refine ⟨((pointValuation curve 0).map_neg _).symm, by rw [add_neg_cancel, map_zero], ?_⟩
  rw [pointValuation_zero_genericX, ← exp_zero, exp_lt_exp]
  norm_num

/-- 零関数の正規化和は零。元の関数に極があるという仮定は省けない。
零関数にpointOrderを付けて便宜的な値を数学的位数とはしない。 -/
theorem constant_boundary :
    pointValuation curve 0 (kernelTrace curve kernel 0 -
      algebraMap (AlgebraicClosure ℚ) (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField 0) = 0 := by
  simp [kernelTrace]

/-- 自明核での極の支持はOだけである。Q≠Oは極でなくなる。 -/
theorem trivial_support :
    letI : Fintype (⊥ : AddSubgroup (Points curve)) := Fintype.ofFinite _
    (1 < pointValuation curve 0 (veluX curve ⊥)) ∧
      ¬ 1 < pointValuation curve Q (veluX curve ⊥) := by
  let : Fintype (⊥ : AddSubgroup (Points curve)) := Fintype.ofFinite _
  exact ⟨(velu_pole_support curve ⊥ 0).1.mpr (AddSubgroup.zero_mem _),
    mt (velu_pole_support curve ⊥ Q).1.mp point_data.1⟩

end
end EllipticFiniteKernelPolesTest
