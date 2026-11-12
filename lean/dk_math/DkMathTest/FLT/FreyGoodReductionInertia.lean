/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyGoodReductionInertia
import DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber
import DkMathTest.FLT.FreyValuationArithmetic

#print "file: DkMathTest.FLT.FreyGoodReductionInertia"

/-!
# NOTE-031-002B: 良還元での実際の9点と、悪い還元で単射性が破れる境界

y²=x³−xのE[3]は9点を持ち、5上の全慣性群で全点が固定される。
一方、前章の曲線上の異なる二つの2-torsion点は3上で同じ剰余座標になる。
指数が単元である条件だけでは還元の単射性は得られず、良還元条件も必要である。
-/
namespace FreyGoodReductionInertiaTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport EllipticTorsionRepresentation
open WeierstrassCurve IsLocalRing
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 良還元回帰の整モデル。 -/
def integerCurve : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 0⟩

/-- 同じ有理曲線y²=x³−x。 -/
def curve : WeierstrassCurve ℚ := integerCurve.map (Int.castRingHom ℚ)

/-- 判別式64は非零である。 -/
theorem elliptic : curve.IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [curve, integerCurve, Δ, b₂, b₄, b₆, b₈]

/-- 実際のE[3]は9点を持つ。空の点群による局所固定の回帰ではない。 -/
theorem card_three : Nat.card (Torsion curve 3) = 9 := by
  have := elliptic
  exact card_torsion_prime_sq curve 3

/-- 全ての5上の付値環と慣性元で、同じ実際のE[3]の9点が全て固定される。 -/
theorem nine_points_fixed_at_five
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 5)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ) :
    Nat.card (Torsion curve 3) = 9 ∧ ∀ P : Torsion curve 3, representation curve 3 σ P = P := by
  refine ⟨card_three, ?_⟩
  let W := integerCurve.map (Int.castRingHom A)
  have hm : W.map A.subtype = curve.baseChange (AlgebraicClosure ℚ) := by
    simp only [W, curve, baseChange, map_map]
    congr 1
  have hunit : IsUnit W.Δ := by
    apply (A.valuation_eq_one_iff _).mpr
    have hv := valuation_intCast_eq_one_of_not_dvd A (by decide)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 64) (by norm_num)
    have hd : W.Δ = (64 : A) := by norm_num [W, integerCurve, Δ, b₂, b₄, b₆, b₈]
    rw [hd]
    exact hv
  have hg : (W.map (residue A)).Δ ≠ 0 := by
    rw [map_Δ]
    exact (residue_ne_zero_iff_isUnit _).mpr hunit
  have hn : A.valuation (3 : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A (by decide)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)
  exact EllipticGoodReductionInertia.fixed_of_inertia_of_good_model curve 3 A W hm hg hn σ hσ

/-- 前章と同じ曲線上の第二の非零2-torsion点の非特異性。 -/
theorem other_nonsingular : FreyValuationArithmeticTest.curve.toAffine.Nonsingular (-4) 2 := by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff,
    FreyValuationArithmeticTest.curve, FreyValuationArithmeticTest.curveInt]

/-- 第二の実際の有理点。 -/
def otherPoint : FreyValuationArithmeticTest.curve.toAffine.Point := Affine.Point.some (-4) 2 other_nonsingular

/-- 第二の点も2倍零であり、第一の点とは異なる。 -/
theorem other_two_torsion : 2 • otherPoint = 0 ∧ FreyValuationArithmeticTest.point ≠ otherPoint := by
  constructor
  · have hn : -otherPoint = otherPoint := by
      rw [otherPoint, Affine.Point.neg_some, Affine.Point.some.injEq]
      norm_num [Affine.negY, FreyValuationArithmeticTest.curve, FreyValuationArithmeticTest.curveInt]
    rw [two_nsmul]
    calc otherPoint + otherPoint = -otherPoint + otherPoint := congrArg (fun T => T + otherPoint) hn.symm
      _ = 0 := neg_add_cancel _
  · intro he
    have hx := (Affine.Point.some.inj he).1
    norm_num at hx

private theorem mul_small (A : ValuationSubring ℚ) {a : ℚ} (ha : a ∈ A)
    (h3 : LiesOverPrime A 3) : a * 3 ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_mul]
  exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr ha)).trans_lt
    ((ValuationSubring.mem_nonunits_iff _).mp h3)

/-- 悪い素数3では、単元指数2の異なる実際のtorsion点が同じ剰余座標になる。 -/
theorem bad_reduction_not_injective (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    2 • FreyValuationArithmeticTest.point = 0 ∧ 2 • otherPoint = 0 ∧
      FreyValuationArithmeticTest.point ≠ otherPoint ∧
      (-1 / 4 : ℚ) - (-4) ∈ A.nonunits ∧ (1 / 8 : ℚ) - 2 ∈ A.nonunits := by
  obtain ⟨hx, hy⟩ := FreyValuationArithmeticTest.point_integral_at_three A hA
  refine ⟨FreyValuationArithmeticTest.point_nonzero_two_torsion.2,
    other_two_torsion.1, other_two_torsion.2, ?_, ?_⟩
  · convert mul_small A (A.toSubring.mul_mem (intCast_mem A (-5)) hx) hA using 1
    norm_num
  · convert mul_small A (A.toSubring.mul_mem (intCast_mem A (-5)) hy) hA using 1
    norm_num

/-- 同じSource 37の良い素数3で全ての残余点が固定される。 -/
theorem source37_good_fixed (S : DkMath.FLT.Frey.Source 37) (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 3)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (P : S.ResidualSpace) : S.residualRepresentation σ P = P :=
  S.residual_fixed_at_good_prime (by decide) (by decide) (by decide) hd A hA σ hσ P

end FreyGoodReductionInertiaTest
