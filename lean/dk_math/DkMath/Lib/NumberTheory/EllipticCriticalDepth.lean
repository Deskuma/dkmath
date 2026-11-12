/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_WeierstrassCurve_valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt,
blob 4de142e4da82c3fd8d7f9c59dd9f3d986475304f.
Modified: arbitrary field, same DkMath CriticalCentre, explicit unit condition on 2;
separate point-group derivative, polynomial identity and valuation consequences.
-/

import DkMath.Lib.NumberTheory.EllipticShallowSlope
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

#print "file: DkMath.Lib.NumberTheory.EllipticCriticalDepth"

/-!
# NOTE-031-002C6a: 2-torsionの臨界深さと浅い点の接線分母

X=x−C.x、F₀=F(C.x,C.y)、B=b₂+12C.xとする。
実際の2倍零点では接線分母Ψ=2y+a₁x+a₃が零なので、X²(4X+B)=4F₀となる。
2が単元でv(X)<1なら4X+Bも単元であり、v(X)²=v(F₀)が従う。
これは前章の厳密な浅さv(F₀)<v(X)²との境界を正確に表す。
浅い点では逆にv(Ψ)=v(X)を得て、次章の実際の倍点の分母を制御する。
奇数torsionの全倍点の深さや慣性固定はここでは主張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticCriticalDepth
open WeierstrassCurve EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticShallowSlope
variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve L}

/-- 接線傾きの分母、すなわち曲線方程式のY偏微分。中心傾きY/Xの分母とは異なる。 -/
def tangentDenominator (W : WeierstrassCurve L) (x y : L) : L := 2 * y + W.a₁ * x + W.a₃

/-- 実際の有限2倍零点は自分の負号と一致するため、接線分母が零になる。 -/
theorem two_torsion_derivative [DecidableEq L] {x y : L} (h : W.toAffine.Nonsingular x y)
    (htor : 2 • Affine.Point.some x y h = 0) : tangentDenominator W x y = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at htor
  obtain ⟨_, hy⟩ := htor
  dsimp only [Affine.negY] at hy
  dsimp only [tangentDenominator]
  linear_combination hy

/-- 接線分母が零の曲線点に対する分母なし三次式。群構造や2の逆元は使わない。 -/
theorem critical_cubic (C : CriticalCentre A W) {x y : L} (h : W.toAffine.Equation x y)
    (hΨ : tangentDenominator W x y = 0) :
    (x - C.x) ^ 2 * (4 * (x - C.x) + (W.b₂ + 12 * C.x)) = 4 * equationDefect W C.x C.y := by
  rw [Affine.equation_iff] at h
  dsimp only [tangentDenominator] at hΨ
  simp only [equationDefect, b₂]
  linear_combination (2 * y + W.a₁ * x + W.a₃) * hΨ - 4 * h
    + (4 * (x - C.x)) * C.derivativeX
    - (2 * W.a₁ * (x - C.x)) * C.derivativeY
    - (2 * C.y + W.a₁ * C.x + W.a₃) * C.derivativeY

/-- 中心へ近いXに対し4X+Bは単元。4は常に整なので、この補題に2の単元性は不要。 -/
theorem node_factor_unit (C : CriticalCentre A W) {x : L} (hX : A.valuation (x - C.x) < 1) :
    A.valuation (4 * (x - C.x) + (W.b₂ + 12 * C.x)) = 1 := by
  have hv : A.valuation (4 * (x - C.x)) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (ofNat_mem A 4))).trans_lt hX
  rw [Valuation.map_add_eq_of_lt_right _ (by rwa [C.node_unit]), C.node_unit]

/-- 奇剰余標数の中心近傍で、有限2倍零点のX深さの平方はずれの深さに等しい。
判別式との等値も同じCに保持されているが、別の中心を選ぶことはない。 -/
theorem two_torsion_depth [DecidableEq L] (C : CriticalCentre A W)
    (h2 : A.valuation (2 : L) = 1) {x y : L} (h : W.toAffine.Nonsingular x y)
    (htor : 2 • Affine.Point.some x y h = 0) (hX : A.valuation (x - C.x) < 1) :
    A.valuation (x - C.x) ^ 2 = A.valuation (equationDefect W C.x C.y) := by
  have h4 : A.valuation (4 : L) = 1 := by
    rw [show (4 : L) = 2 * 2 by ring, map_mul, h2, one_mul]
  have hc := congrArg A.valuation (critical_cubic C h.1 (two_torsion_derivative h htor))
  rw [map_mul, map_pow, node_factor_unit C hX, mul_one, map_mul, h4, one_mul] at hc
  exact hc

/-- 中心へ近い相異なる2倍零点のX差は、それぞれの中心からのX差と同じ深さを持つ。
相異なるXという条件を残し、同一点の差の零を非零の深さへ同一視しない。 -/
theorem two_torsion_separation [DecidableEq L] (C : CriticalCentre A W)
    (h2 : A.valuation (2 : L) = 1) {x y x' y' : L}
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y')
    (htor : 2 • Affine.Point.some x y h = 0) (htor' : 2 • Affine.Point.some x' y' h' = 0)
    (hX : A.valuation (x - C.x) < 1) (hX' : A.valuation (x' - C.x) < 1) (hne : x' ≠ x) :
    A.valuation (x' - x) = A.valuation (x - C.x) := by
  have hc := critical_cubic C h.1 (two_torsion_derivative h htor)
  have hc' := critical_cubic C h'.1 (two_torsion_derivative h' htor')
  have heq : A.valuation (x' - C.x) = A.valuation (x - C.x) :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).mp
      ((two_torsion_depth C h2 h' htor' hX').trans (two_torsion_depth C h2 h htor hX).symm)
  have hx0 : x - C.x ≠ 0 := by
    intro hz
    have hv := two_torsion_depth C h2 h htor hX
    rw [hz, map_zero, zero_pow two_ne_zero] at hv
    exact C.defect_ne_zero ((Valuation.zero_iff _).mp hv.symm)
  have hfac : ((x - C.x) - (x' - C.x)) *
      (4 * ((x - C.x) ^ 2 + (x - C.x) * (x' - C.x) + (x' - C.x) ^ 2) +
        (W.b₂ + 12 * C.x) * ((x - C.x) + (x' - C.x))) = 0 := by
    linear_combination hc - hc'
  have hne' : (x - C.x) - (x' - C.x) ≠ 0 := by
    intro hz
    apply hne
    linear_combination -hz
  have hs : (W.b₂ + 12 * C.x) * ((x - C.x) + (x' - C.x)) =
      -(4 * ((x - C.x) ^ 2 + (x - C.x) * (x' - C.x) + (x' - C.x) ^ 2)) := by
    have hz := (mul_eq_zero.mp hfac).resolve_left hne'
    linear_combination hz
  have hsum : A.valuation ((x - C.x) + (x' - C.x)) ≤ A.valuation (x - C.x) ^ 2 := by
    have hv := congrArg A.valuation hs
    rw [map_mul, C.node_unit, one_mul, Valuation.map_neg, map_mul] at hv
    rw [hv]
    apply le_trans (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (ofNat_mem A 4)))
    apply Valuation.map_add_le
    · apply Valuation.map_add_le
      · exact (map_pow _ _ _).le
      · rw [map_mul, heq, sq]
    · rw [map_pow, heq]
  have hlt : A.valuation ((x - C.x) + (x' - C.x)) < A.valuation (2 * (x - C.x)) := by
    rw [map_mul, h2, one_mul]
    refine hsum.trans_lt ?_
    rw [sq]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hX ((Valuation.pos_iff _).mpr hx0)
  have hk := Valuation.map_sub_eq_of_lt_left A.valuation hlt
  rw [map_mul, h2, one_mul] at hk
  rw [show x' - x = -(2 * (x - C.x) - ((x - C.x) + (x' - C.x))) by ring, Valuation.map_neg, hk]

/-- 浅い点では接線分母の付値が中心からのX差の付値に等しい。
C4の反対傾きの単元分離を使い、同じ点の実際の倍点に使える分母を制御する。 -/
theorem shallow_denominator_valuation (C : CriticalCentre A W) {x y : L} (h : W.toAffine.Equation x y)
    (hX : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect W C.x C.y) < A.valuation (x - C.x) ^ 2) :
    A.valuation (tangentDenominator W x y) = A.valuation (x - C.x) := by
  have hx := shallow_x_ne C hsh
  have he : tangentDenominator W x y =
      (centreSlope C x y - centreSlope C x (W.toAffine.negY x y)) * (x - C.x) := by
    rw [centreSlope_negY C x y hx]
    dsimp only [tangentDenominator, centreSlope]
    field_simp [hx]
    linear_combination C.derivativeY
  rw [he, map_mul, opposite_slope_separated_of_shallow C h hX hsh, one_mul]

/-- 浅い有限点の実際の2倍は零でない。厳密な浅さと2-torsionの臨界深さを混同しない。 -/
theorem shallow_not_two_torsion [DecidableEq L] (C : CriticalCentre A W) {x y : L}
    (h : W.toAffine.Nonsingular x y) (hX : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect W C.x C.y) < A.valuation (x - C.x) ^ 2) :
    2 • Affine.Point.some x y h ≠ 0 := by
  intro hz
  have hv := shallow_denominator_valuation C h.1 hX hsh
  rw [two_torsion_derivative h hz, map_zero] at hv
  exact shallow_x_ne C hsh ((Valuation.zero_iff _).mp hv.symm)

end DkMath.Lib.NumberTheory.EllipticCriticalDepth
