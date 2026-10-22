/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDoublingDepth
import DkMathTest.FLT.FreyShallowSlope

#print "file: DkMathTest.FLT.FreyDoublingDepth"

/-!
# NOTE-031-002C6a: 実際の2-torsionと倍点の相殺閾値

前章の点(3,33)はv(F₀)=v(X)⁴という閾値にあり、2PのX座標は−27/4になる。
この実例で相殺による厳密な上界を検査する。別の曲線y²=x³+x²+cにおける
c=7533と189は閾値の両側を実現する。曲線点と実際の倍点を省略しない。
-/
namespace FreyDoublingDepthTest
open WeierstrassCurve Affine DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticShallowSlope EllipticCriticalDepth EllipticDoublingDepth
open FreyShallowSlopeTest

/-- 同じ有理座標(3,y)を持つ実例用の整係数曲線族。 -/
def family (c : ℤ) : WeierstrassCurve ℚ := ⟨0, 1, 0, 0, c⟩

/-- c≠0かつ3∣cなら、原点は同じ曲線族の全臨界中心条件を満たす。 -/
def familyCentre (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) (c : ℤ) (hc : c ≠ 0) (hd : 3 ∣ c) :
    CriticalCentre A (family c) where
  x := 0
  y := 0
  x_mem := A.zero_mem
  y_mem := A.zero_mem
  derivativeY := by norm_num [family]
  derivativeX := by norm_num [family]
  node_unit := by
    norm_num [family, b₂]
    exact valuation_intCast_eq_one_of_not_dvd A (by decide) ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := 4) (by norm_num)
  defect_ne_zero := by simpa [equationDefect, family] using hc
  defect_small := by
    have hv := valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA) hd
    simpa [equationDefect, family] using hv
  defect_valuation := by
    have he : (family c).Δ = -(c : ℚ) * (16 * (4 + 27 * c) : ℤ) := by
      norm_num [family, Δ, b₂, b₄, b₆, b₈]
      ring
    have hu := valuation_intCast_eq_one_of_not_dvd A (by decide)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 16 * (4 + 27 * c)) (by omega)
    rw [he, map_mul, hu, mul_one]
    simp only [equationDefect, family, mul_zero, zero_add, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), add_zero, zero_sub]

/-- 前章の実際のP=(3,33)の2倍は(−27/4,−225/8)である。 -/
theorem threshold_double :
    ∃ h : curve.toAffine.Nonsingular (-27 / 4) (-225 / 8), 2 • point = .some _ _ h := by
  have h : curve.toAffine.Nonsingular (-27 / 4) (-225 / 8) := by
    norm_num [curve, nonsingular_iff, equation_iff]
  refine ⟨h, ?_⟩
  change 2 • Point.some 3 33 point_nonsingular = _
  rw [two_nsmul, Point.add_self_of_Y_ne (by norm_num [negY, curve]), Point.some.injEq]
  norm_num [addX, addY, negY, slope, curve]

/-- 前章の浅い点は厳密な倍点条件v(F₀)<v(X)⁴を満たさず、ちょうど等号の閾値にある。 -/
theorem cancellation_threshold (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    A.valuation (equationDefect curve (centre A hA).x (centre A hA).y) =
      A.valuation ((3 : ℚ) - (centre A hA).x) ^ 4 := by
  have hu := valuation_intCast_eq_one_of_not_dvd A (by decide)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 13) (by norm_num)
  change A.valuation (13 : ℚ) = 1 at hu
  norm_num only [centre, sub_zero]
  rw [defect_at_zero, Valuation.map_neg, show (1053 : ℚ) = 3 ^ 4 * 13 by norm_num, map_mul, map_pow, hu, mul_one]

/-- 閾値では倍点の深さが単純な平方より厳密に小さくなり、最大値との等号は使えない。 -/
theorem cancellation_strict (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    A.valuation ((-27 / 4 : ℚ) - (centre A hA).x) < A.valuation ((3 : ℚ) - (centre A hA).x) ^ 2 := by
  have h3 := (ValuationSubring.mem_nonunits_iff _).mp hA
  have hu := valuation_intCast_eq_one_of_not_dvd A (by decide) h3 (z := 4) (by norm_num)
  change A.valuation (4 : ℚ) = 1 at hu
  norm_num only [centre, sub_zero]
  rw [Valuation.map_neg, map_div₀, show (27 : ℚ) = 3 ^ 3 by norm_num, map_pow, hu, div_one]
  exact pow_lt_pow_right_of_lt_one₀ ((Valuation.pos_iff _).mpr (by norm_num)) h3 (by decide : 2 < 3)

/-- 相殺の閾値でも倍点定理は適用でき、実際の有限点と上界を返す。 -/
theorem threshold_rule (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    ∃ (x y : ℚ) (h : curve.toAffine.Nonsingular x y), 2 • point = .some x y h ∧
      A.valuation (x - (centre A hA).x) * A.valuation (3 : ℚ) ^ 2 ≤ A.valuation (3 : ℚ) ^ 4 := by
  obtain ⟨hn, hs⟩ := point_shallow A hA
  obtain ⟨x, y, h, he, hb, _, _⟩ := doubling_depth (centre A hA) point_nonsingular hn hs
  refine ⟨x, y, h, he, ?_⟩
  rw [cancellation_threshold A hA, max_self] at hb
  simpa only [centre, sub_zero] using hb

/-- 閾値の片側の実際の点。F₀=−7533は3進深さ5を持つ。 -/
theorem deeper_point : (family 7533).toAffine.Nonsingular 3 87 := by
  norm_num [family, nonsingular_iff, equation_iff]

/-- 反対側の実際の点。F₀=−189は3進深さ3を持つ。 -/
theorem shallower_point : (family 189).toAffine.Nonsingular 3 15 := by
  norm_num [family, nonsingular_iff, equation_iff]

private theorem defect_value (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) (c : ℤ) (k : ℕ)
    (u : ℤ) (hc : c = 3 ^ k * u) (hu : ¬ 3 ∣ u) :
    A.valuation (equationDefect (family c) 0 0) = A.valuation (3 : ℚ) ^ k := by
  have he : equationDefect (family c) 0 0 = -((3 : ℚ) ^ k * (u : ℚ)) := by simp [equationDefect, family, hc]
  rw [he, Valuation.map_neg, map_mul, map_pow,
    valuation_intCast_eq_one_of_not_dvd A (by decide) ((ValuationSubring.mem_nonunits_iff _).mp hA) hu, mul_one]

/-- v(F₀)<v(X)⁴の側では、実際の倍点のX深さがv(X)²となる。 -/
theorem deeper_rule (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    ∃ (x y : ℚ) (h : (family 7533).toAffine.Nonsingular x y),
      2 • Point.some 3 87 deeper_point = .some x y h ∧ A.valuation x = A.valuation (3 : ℚ) ^ 2 := by
  let C := familyCentre A hA 7533 (by norm_num) (by norm_num)
  have hf := defect_value A hA 7533 5 31 (by norm_num) (by norm_num)
  have hp : 0 < A.valuation (3 : ℚ) := (Valuation.pos_iff _).mpr (by norm_num)
  have hn := (ValuationSubring.mem_nonunits_iff _).mp hA
  change A.valuation (3 : ℚ) < 1 at hn
  have hsh : A.valuation (equationDefect (family 7533) C.x C.y) < A.valuation ((3 : ℚ) - C.x) ^ 2 := by
    change A.valuation (equationDefect (family 7533) 0 0) < A.valuation (3 - 0 : ℚ) ^ 2
    rw [hf, sub_zero]
    exact pow_lt_pow_right_of_lt_one₀ hp hn (by decide : 2 < 5)
  obtain ⟨x, y, h, he, _, hlt, _⟩ := doubling_depth C deeper_point (by simpa only [C, familyCentre, sub_zero] using hn) hsh
  refine ⟨x, y, h, he, ?_⟩
  have hstrict : A.valuation (equationDefect (family 7533) C.x C.y) < A.valuation ((3 : ℚ) - C.x) ^ 4 := by
    change A.valuation (equationDefect (family 7533) 0 0) < A.valuation (3 - 0 : ℚ) ^ 4
    rw [hf, sub_zero]
    exact pow_lt_pow_right_of_lt_one₀ hp hn (by decide : 4 < 5)
  simpa only [C, familyCentre, sub_zero] using hlt hstrict

/-- v(X)⁴<v(F₀)<v(X)²の側では、実際の倍点はN·v(X)²=v(F₀)を満たす。 -/
theorem shallower_rule (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    ∃ (x y : ℚ) (h : (family 189).toAffine.Nonsingular x y),
      2 • Point.some 3 15 shallower_point = .some x y h ∧
        A.valuation x * A.valuation (3 : ℚ) ^ 2 = A.valuation (3 : ℚ) ^ 3 := by
  let C := familyCentre A hA 189 (by norm_num) (by norm_num)
  have hf := defect_value A hA 189 3 7 (by norm_num) (by norm_num)
  have hp : 0 < A.valuation (3 : ℚ) := (Valuation.pos_iff _).mpr (by norm_num)
  have hn := (ValuationSubring.mem_nonunits_iff _).mp hA
  change A.valuation (3 : ℚ) < 1 at hn
  have hsh : A.valuation (equationDefect (family 189) C.x C.y) < A.valuation ((3 : ℚ) - C.x) ^ 2 := by
    change A.valuation (equationDefect (family 189) 0 0) < A.valuation (3 - 0 : ℚ) ^ 2
    rw [hf, sub_zero]
    exact pow_lt_pow_right_of_lt_one₀ hp hn (by decide : 2 < 3)
  obtain ⟨x, y, h, he, _, _, hgt⟩ := doubling_depth C shallower_point (by simpa only [C, familyCentre, sub_zero] using hn) hsh
  refine ⟨x, y, h, he, ?_⟩
  have hstrict : A.valuation ((3 : ℚ) - C.x) ^ 4 < A.valuation (equationDefect (family 189) C.x C.y) := by
    change A.valuation (3 - 0 : ℚ) ^ 4 < A.valuation (equationDefect (family 189) 0 0)
    rw [hf, sub_zero]
    exact pow_lt_pow_right_of_lt_one₀ hp hn (by decide : 3 < 4)
  simpa only [C, familyCentre, sub_zero, hf] using hgt hstrict

/-- 前章の実際の特異剰余点(−4,2)は、同じ代数閉包上の点群でも2倍零点である。 -/
theorem bad_point_two_torsion [DecidableEq (AlgebraicClosure ℚ)] :
    2 • Point.some (-4) 2 FreyNodalReductionTest.bad_point_nonsingular = 0 := by
  rw [two_nsmul, Point.add_self_of_Y_eq (by
    norm_num [negY, FreyValuationArithmeticTest.curve, FreyValuationArithmeticTest.curveInt, WeierstrassCurve.baseChange])]

/-- 前章の「浅くない」を強め、同じ任意の中心について臨界深さの等号を確定する。 -/
theorem bad_point_critical_depth
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (C : CriticalCentre A (FreyValuationArithmeticTest.curve.baseChange (AlgebraicClosure ℚ))) :
    A.valuation ((-4 : AlgebraicClosure ℚ) - C.x) ^ 2 =
      A.valuation (equationDefect (FreyValuationArithmeticTest.curve.baseChange (AlgebraicClosure ℚ)) C.x C.y) := by
  classical
  have h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A (by decide) ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := 2) (by norm_num)
  exact two_torsion_depth C h2 FreyNodalReductionTest.bad_point_nonsingular bad_point_two_torsion
    (FreyNodalReductionTest.bad_point_depth A hA C).1

/-- 相異なる実際の二つの2倍零点で、同じ中心のX深さと点同士のX深さを比較する。 -/
theorem bad_pair_separated
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (C : CriticalCentre A (FreyValuationArithmeticTest.curve.baseChange (AlgebraicClosure ℚ))) :
    A.valuation ((-1 / 4 : AlgebraicClosure ℚ) - (-4)) = A.valuation ((-4 : AlgebraicClosure ℚ) - C.x) := by
  classical
  have h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A (by decide) ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := 2) (by norm_num)
  have h4 : A.valuation (4 : AlgebraicClosure ℚ) = 1 := by
    rw [show (4 : AlgebraicClosure ℚ) = 2 * 2 by ring, map_mul, h2, one_mul]
  have hr : (FreyValuationArithmeticTest.curve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular (-1 / 4) (1 / 8) := by
    norm_num [FreyValuationArithmeticTest.curve, FreyValuationArithmeticTest.curveInt, WeierstrassCurve.baseChange, nonsingular_iff, equation_iff]
  have hrtor : 2 • Point.some _ _ hr = 0 := by
    rw [two_nsmul, Point.add_self_of_Y_eq (by
      norm_num [negY, FreyValuationArithmeticTest.curve, FreyValuationArithmeticTest.curveInt, WeierstrassCurve.baseChange])]
  have hδ : A.valuation ((-1 / 4 : AlgebraicClosure ℚ) - (-4)) < 1 := by
    rw [show (-1 / 4 : AlgebraicClosure ℚ) - (-4) = 15 / 4 by norm_num, map_div₀, h4, div_one]
    exact valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := 15) (by norm_num)
  have hn := (FreyNodalReductionTest.bad_point_depth A hA C).1
  have hrnear : A.valuation ((-1 / 4 : AlgebraicClosure ℚ) - C.x) < 1 := by
    rw [show (-1 / 4 : AlgebraicClosure ℚ) - C.x = ((-1 / 4) - (-4)) + ((-4) - C.x) by ring]
    exact Valuation.map_add_lt _ hδ hn
  exact two_torsion_separation C h2 FreyNodalReductionTest.bad_point_nonsingular hr
    bad_point_two_torsion hrtor hn hrnear (by norm_num)

end FreyDoublingDepthTest
