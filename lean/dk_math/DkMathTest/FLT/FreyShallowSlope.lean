/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyShallowSlope
import DkMathTest.FLT.FreyNodalReduction

#print "file: DkMathTest.FLT.FreyShallowSlope"

/-!
# NOTE-031-002C4: 実際に浅い有理点と、厳密な浅さの境界

y²=x³+x²+1053で中心(0,0)、方向±1、実際の点(3,33)を使う。
3上ではずれの深さ4に対してXの深さは1であり、厳密な浅さ4>2が成立する。
傾き11は−1の枝へ近づき、負号の点の傾き−11は+1へ近づく。
前章の2-torsion点にはこの厳密な浅さを適用できないことも検査する。
-/
namespace FreyShallowSlopeTest
open WeierstrassCurve DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections EllipticShallowSlope
open DkMath.Lib.Algebra.ValuationSeparatedRoots
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- ずれの3進深さ4を持ち、実際に浅い有理点を持つ曲線。 -/
def curve : WeierstrassCurve ℚ := ⟨0, 1, 0, 0, 1053⟩

/-- 判別式はずれ−1053と3上の単元454960の積であり、c₄=16である。 -/
theorem curve_invariants : curve.Δ = (-1053 : ℚ) * 454960 ∧ curve.c₄ = 16 := by
  norm_num [curve, Δ, c₄, b₂, b₄, b₆, b₈]

/-- 中心のずれは非零の−1053であり、曲線上の点ではない。 -/
theorem defect_at_zero : equationDefect curve 0 0 = -1053 := by norm_num [equationDefect, curve]

/-- 実際の有限座標(3,33)は同じ曲線の非特異点である。 -/
theorem point_nonsingular : curve.toAffine.Nonsingular 3 33 := by
  norm_num [curve, Affine.nonsingular_iff, Affine.equation_iff]

/-- 同じ曲線の実際の点群の元。 -/
def point : curve.toAffine.Point := .some 3 33 point_nonsingular

/-- 回帰の点は無限遠点でも2-torsion点でもない。 -/
theorem point_nonzero_not_two_torsion : point ≠ 0 ∧ 2 • point ≠ 0 := by
  refine ⟨Affine.Point.some_ne_zero _, ?_⟩
  intro hz
  have hn : point = -point := add_eq_zero_iff_eq_neg.mp (by simpa only [two_nsmul] using hz)
  change Affine.Point.some 3 33 point_nonsingular = -Affine.Point.some 3 33 point_nonsingular at hn
  rw [Affine.Point.neg_some, Affine.Point.some.injEq] at hn
  norm_num [Affine.negY, curve] at hn

/-- 3上の任意の付値環について、同じ有理座標(0,0)が全ての中心条件を満たす。 -/
def centre (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) : CriticalCentre A curve where
  x := 0
  y := 0
  x_mem := A.zero_mem
  y_mem := A.zero_mem
  derivativeY := by norm_num [curve]
  derivativeX := by norm_num [curve]
  node_unit := by
    norm_num [curve, b₂]
    exact valuation_intCast_eq_one_of_not_dvd A (by decide)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 4) (by norm_num)
  defect_ne_zero := by rw [defect_at_zero]; norm_num
  defect_small := by
    rw [defect_at_zero]
    exact valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := -1053) (by norm_num)
  defect_valuation := by
    have hu : A.valuation (454960 : ℚ) = 1 :=
      valuation_intCast_eq_one_of_not_dvd A (by decide)
        ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 454960) (by norm_num)
    rw [defect_at_zero, curve_invariants.1, map_mul, hu, mul_one]

/-- 同じ中心に対する実際の方向α=1、β=−1。差2は3上の単元である。 -/
def directions (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) : TangentDirections (centre A hA) where
  α := 1
  β := -1
  α_mem := A.one_mem
  β_mem := A.toSubring.neg_mem A.one_mem
  sum_eq := by norm_num [curve]
  product_eq := by norm_num [curve, centre]
  separated := by
    norm_num
    exact valuation_intCast_eq_one_of_not_dvd A (by decide)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 2) (by norm_num)

/-- v(F₀)=v(3)⁴、v(X)²=v(3)²なので、この同じ実際の点は厳密に浅い。 -/
theorem point_shallow (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    A.valuation ((3 : ℚ) - (centre A hA).x) < 1 ∧
      A.valuation (equationDefect curve (centre A hA).x (centre A hA).y) <
        A.valuation ((3 : ℚ) - (centre A hA).x) ^ 2 := by
  have h3 := (ValuationSubring.mem_nonunits_iff _).mp hA
  have h3pos : 0 < A.valuation (3 : ℚ) := (Valuation.pos_iff _).mpr (by norm_num)
  have h13 : A.valuation (13 : ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A (by decide) h3 (z := 13) (by norm_num)
  simp only [centre, sub_zero]
  refine ⟨h3, ?_⟩
  rw [defect_at_zero, Valuation.map_neg, show (1053 : ℚ) = 3 ^ 4 * 13 by norm_num,
    map_mul, map_pow, h13, mul_one]
  exact pow_lt_pow_right_of_lt_one₀ h3pos h3 (by decide : 2 < 4)

/-- 新しい枝分類を使い、実際の傾き11が第二方向−1へ近づく側を確定する。 -/
theorem point_on_second_branch (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    centreSlope (centre A hA) 3 33 = 11 ∧ centreSlope (centre A hA) 3 33 ∈ A ∧
      A.valuation (centreSlope (centre A hA) 3 33 - (directions A hA).α) = 1 ∧
      A.valuation (centreSlope (centre A hA) 3 33 - (directions A hA).β) < 1 := by
  obtain ⟨hn, hs⟩ := point_shallow A hA
  obtain ⟨ht, _, hb⟩ := slope_mem_and_branches_of_shallow (directions A hA) point_nonsingular.1 hn hs
  have hx : A.valuation (centreSlope (centre A hA) 3 33 - (directions A hA).α) = 1 := by
    norm_num [centreSlope, centre, directions]
    exact valuation_intCast_eq_one_of_not_dvd A (by decide)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 10) (by norm_num)
  refine ⟨by norm_num [centreSlope, centre], ht, hx, ?_⟩
  rcases hb with hb | hb
  · rw [hx] at hb
    exact (lt_irrefl _ hb.1).elim
  · exact hb.2

/-- 負号で枝が交換され、実際の傾き11と−11の差は単元となる。 -/
theorem negative_point_on_first_branch (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    let C := centre A hA
    let D := directions A hA
    A.valuation (centreSlope C 3 (curve.toAffine.negY 3 33) - D.α) < 1 ∧
      A.valuation (centreSlope C 3 (curve.toAffine.negY 3 33) - D.β) = 1 ∧
      A.valuation (centreSlope C 3 33 - centreSlope C 3 (curve.toAffine.negY 3 33)) = 1 := by
  obtain ⟨hn, hs⟩ := point_shallow A hA
  have hb := point_on_second_branch A hA
  obtain ⟨hα, hβ⟩ := negY_branch_distances (directions A hA) 3 33 (shallow_x_ne _ hs)
  exact ⟨hα.trans_lt hb.2.2.2, hβ.trans hb.2.2.1,
    opposite_slope_separated_of_shallow _ point_nonsingular.1 hn hs⟩

/-- 前章の実際の2-torsion点(−4,2)は、中心へ近づくが厳密には浅くない。
負号で点自身が変わらないため、浅い場合の傾きの単元分離と矛盾する。 -/
theorem old_two_torsion_not_shallow (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (C : CriticalCentre A (FreyValuationArithmeticTest.curve.baseChange (AlgebraicClosure ℚ))) :
    ¬ A.valuation (equationDefect (FreyValuationArithmeticTest.curve.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
      A.valuation ((-4 : AlgebraicClosure ℚ) - C.x) ^ 2 := by
  intro hs
  have hn := (FreyNodalReductionTest.bad_point_depth A hA C).1
  have hv := opposite_slope_separated_of_shallow C FreyNodalReductionTest.bad_point_nonsingular.1 hn hs
  have he : (FreyValuationArithmeticTest.curve.baseChange (AlgebraicClosure ℚ)).toAffine.negY (-4) 2 = 2 := by
    norm_num [Affine.negY, FreyValuationArithmeticTest.curve, FreyValuationArithmeticTest.curveInt, baseChange]
  rw [he, sub_self, map_zero] at hv
  exact zero_ne_one hv

/-- 差が単元でない二根では、積が小さくても両枝へ同時に近づき得る。 -/
theorem colliding_roots_both_near (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    A.valuation (((0 : ℚ) - 0) * (0 - 3)) < 1 ∧
      A.valuation ((0 : ℚ) - 0) < 1 ∧ A.valuation ((0 : ℚ) - 3) < 1 := by
  have h3 := (ValuationSubring.mem_nonunits_iff _).mp hA
  change A.valuation (3 : ℚ) < 1 at h3
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · simpa only [zero_sub, Valuation.map_neg] using h3

/-- 積の付値が1という境界では、どちらの根へも近づかない。厳密不等式を弱めない。 -/
theorem unit_product_no_near (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    A.valuation (((2 : ℚ) - 0) * (2 - 1)) = 1 ∧
      ¬ (A.valuation ((2 : ℚ) - 0) < 1 ∨ A.valuation ((2 : ℚ) - 1) < 1) := by
  have h2 : A.valuation (2 : ℚ) = 1 := valuation_intCast_eq_one_of_not_dvd A (by decide)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 2) (by norm_num)
  norm_num [h2]

/-- 同じSource 37の浅い有限点へ、同じ中心・方向を保って枝分類を輸送する。 -/
theorem source37_shallow (S : DkMath.FLT.Frey.Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))} (D : TangentDirections C)
    {x y : AlgebraicClosure ℚ} (h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hnear : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
      A.valuation (x - C.x) ^ 2) :
    centreSlope C x y ∈ A ∧ A.valuation (y - C.y) < 1 ∧
      ((A.valuation (centreSlope C x y - D.α) < 1 ∧ A.valuation (centreSlope C x y - D.β) = 1) ∨
        (A.valuation (centreSlope C x y - D.α) = 1 ∧ A.valuation (centreSlope C x y - D.β) < 1)) :=
  S.shallow_slope_mem_and_branches A D h hnear hsh

end FreyShallowSlopeTest
