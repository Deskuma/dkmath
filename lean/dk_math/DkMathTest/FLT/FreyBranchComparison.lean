/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyBranchComparison
import DkMathTest.FLT.FreyShallowSlope

#print "file: DkMathTest.FLT.FreyBranchComparison"

/-!
# NOTE-031-002C5: 同じ深さの実際の二点と、無限遠点の境界

前章のy²=x³+x²+1053を保ち、P=(3,33)とQ=(7107/169,−610401/2197)を使う。
3上で両者のX差の深さは等しく、中心傾きは異なる枝へ還元する。
P+Qは整な有限点で、滑らかな還元と鋭いX差の評価を実際の加法公式に接続する。
P−P=O、P+(−P)=Oも検査し、有限点の条件を落とさない。
-/
namespace FreyBranchComparisonTest
open WeierstrassCurve Affine DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections EllipticShallowSlope
open EllipticBranchComparison EllipticGoodReductionSeparation FreyShallowSlopeTest

/-- 前章と同じ有理曲線の整モデル。係数を変えずに任意の付値環へ持ち上げる。 -/
def model (A : ValuationSubring ℚ) : WeierstrassCurve A := ⟨0, 1, 0, 0, 1053⟩

/-- この整モデルの一般ファイバーは前章の同じ曲線である。 -/
theorem model_map (A : ValuationSubring ℚ) : (model A).map A.subtype = curve := by
  ext <;> rfl

private theorem fraction_unit (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) (m n : ℤ)
    (hm : ¬ 3 ∣ m) (hn : ¬ 3 ∣ n) : A.valuation ((m : ℚ) / (n : ℚ)) = 1 := by
  have h3 := (ValuationSubring.mem_nonunits_iff _).mp hA
  rw [map_div₀, valuation_intCast_eq_one_of_not_dvd A (by decide) h3 hm,
    valuation_intCast_eq_one_of_not_dvd A (by decide) h3 hn, div_self one_ne_zero]

/-- 二点目Qも同じ曲線上の実際の非特異点である。 -/
theorem second_nonsingular : curve.toAffine.Nonsingular (7107 / 169) (-610401 / 2197) := by
  norm_num [curve, Affine.nonsingular_iff, Affine.equation_iff]

/-- 分数座標から構成した二点目。曲線方程式の検査を省略しない。 -/
def secondPoint : curve.toAffine.Point := .some _ _ second_nonsingular

/-- P+Qの実際の有限座標も同じ曲線の非特異点である。 -/
theorem sum_nonsingular : curve.toAffine.Nonsingular (172961 / 10000) (80785959 / 1000000) := by
  norm_num [curve, Affine.nonsingular_iff, Affine.equation_iff]

/-- Mathlibの点加法でP+Qを実際に計算する。両点のX座標は異なる。 -/
theorem sum_coordinates : point + secondPoint = .some _ _ sum_nonsingular := by
  change Point.some 3 33 point_nonsingular + Point.some _ _ second_nonsingular = _
  rw [Point.add_of_X_ne (by norm_num : (3 : ℚ) ≠ 7107 / 169), Point.some.injEq]
  norm_num [Affine.addX, Affine.addY, Affine.negY, Affine.slope, curve]

/-- Qの中心からのX差は、PのX差と同じ深さを持つ。分母169は3上の単元。 -/
theorem equal_depth (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    A.valuation ((3 : ℚ) - (centre A hA).x) =
      A.valuation ((7107 / 169 : ℚ) - (centre A hA).x) := by
  have hu := fraction_unit A hA 2369 169 (by norm_num) (by norm_num)
  change A.valuation (3 - 0) = A.valuation (7107 / 169 - 0 : ℚ)
  norm_num only [sub_zero]
  rw [show (7107 / 169 : ℚ) = (2369 / 169) * 3 by norm_num, map_mul]
  change A.valuation ((2369 : ℚ) / 169) = 1 at hu
  rw [hu, one_mul]

/-- 二点の傾きの差は542234/30797であり、3上の単元である。 -/
theorem opposite_branches (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    A.valuation (centreSlope (centre A hA) 3 33 -
      centreSlope (centre A hA) (7107 / 169) (-610401 / 2197)) = 1 := by
  norm_num [centreSlope, centre]
  exact fraction_unit A hA 542234 30797 (by norm_num) (by norm_num)

/-- 同じ深さの異なる枝の定理を、実際のP+Qへ適用した滑らかな還元と鋭い深さ評価。 -/
theorem add_comparison (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    HasSmoothReduction (model A) (point + secondPoint) ∧
      (∀ {x y : ℚ} (h : curve.toAffine.Nonsingular x y), point + secondPoint = .some x y h →
        x ∈ A → A.valuation ((3 : ℚ) - 7107 / 169) = A.valuation ((3 : ℚ) - (centre A hA).x)) := by
  obtain ⟨hn, hs⟩ := point_shallow A hA
  have hd := equal_depth A hA
  exact add_of_opposite_branch_of_model (model A) curve (model_map A) (centre A hA) (directions A hA)
    point_nonsingular second_nonsingular hn (hd ▸ hn) hd hs (opposite_branches A hA)

/-- 実際に計算した和のX座標は整である。分母10000が単元なので逆数も付値環に属する。 -/
theorem sum_integral (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) : (172961 / 10000 : ℚ) ∈ A := by
  have hu := fraction_unit A hA 172961 10000 (by norm_num) (by norm_num)
  exact (A.valuation_le_one_iff _).mp hu.le

/-- 和の整性を供給して、比較定理の条件付き部分を実際のX差の等式へ閉じる。 -/
theorem sharp_depth (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    A.valuation ((3 : ℚ) - 7107 / 169) = A.valuation (3 : ℚ) := by
  simpa only [centre, sub_zero] using
    (add_comparison A hA).2 sum_nonsingular sum_coordinates (sum_integral A hA)

/-- Qを反転するとPと同じ枝になる。同じ深さの差P−(−Q)も実際の点群で比較する。 -/
theorem sub_comparison (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    HasSmoothReduction (model A) (point - (-secondPoint)) := by
  obtain ⟨hn, hs⟩ := point_shallow A hA
  have hd := equal_depth A hA
  have hneg : curve.toAffine.Nonsingular (7107 / 169) (610401 / 2197) := by
    norm_num [curve, Affine.nonsingular_iff, Affine.equation_iff]
  have hb : A.valuation (centreSlope (centre A hA) 3 33 -
      centreSlope (centre A hA) (7107 / 169) (610401 / 2197)) < 1 := by
    norm_num [centreSlope, centre]
    have hu : A.valuation (30797 : ℚ) = 1 :=
      valuation_intCast_eq_one_of_not_dvd A (by decide) ((ValuationSubring.mem_nonunits_iff _).mp hA)
        (z := 30797) (by norm_num)
    rw [hu, div_one]
    exact valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (z := 135300) (by norm_num)
  have res := (sub_of_same_branch_of_model (model A) curve (model_map A) (centre A hA) (directions A hA)
    point_nonsingular hneg hn (hd ▸ hn) hd hs hb).1
  have he : -secondPoint = Point.some _ _ hneg := by
    unfold secondPoint
    rw [Point.neg_some, Point.some.injEq]
    norm_num [Affine.negY, curve]
  rw [he]
  exact res

/-- 同じ点の差は無限遠点である。比較定理の有限結果の条件を外してはならない。 -/
theorem diagonal_zero (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    point - point = 0 ∧ HasSmoothReduction (model A) (point - point) := by
  obtain ⟨hn, hs⟩ := point_shallow A hA
  refine ⟨sub_self _, ?_⟩
  exact (sub_of_same_branch_of_model (model A) curve (model_map A) (centre A hA) (directions A hA)
    point_nonsingular point_nonsingular hn hn rfl hs (by rw [sub_self, map_zero]; exact zero_lt_one)).1

/-- 反対の点の和も無限遠点である。異なる枝であっても有限結果を強制しない。 -/
theorem inverse_zero (A : ValuationSubring ℚ) (hA : LiesOverPrime A 3) :
    point + (-point) = 0 ∧ HasSmoothReduction (model A) (point + (-point)) := by
  obtain ⟨hn, hs⟩ := point_shallow A hA
  have hneg := (Affine.nonsingular_neg (W' := curve.toAffine) 3 33).mpr point_nonsingular
  have hb := opposite_slope_separated_of_shallow (centre A hA) point_nonsingular.1 hn hs
  have res := (add_of_opposite_branch_of_model (model A) curve (model_map A) (centre A hA) (directions A hA)
    point_nonsingular hneg hn hn rfl hs hb).1
  refine ⟨add_neg_cancel _, ?_⟩
  change HasSmoothReduction (model A) (Point.some 3 33 point_nonsingular + (-Point.some 3 33 point_nonsingular))
  rw [Point.neg_some]
  exact res

end FreyBranchComparisonTest
