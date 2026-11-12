/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Shallow-coordinate identity informed by S_WeierstrassCurve_slope_mem_of_shallow.lean,
blob 0b9d8a2eb9bfd9e038a8a875189907fdafd76f58, S04_n_slope and S04_n_neg.
Modified: arbitrary DkMath model and existing centre/directions; integrality and exclusive
branch classification reconstructed from the small product of separated roots.
-/

import DkMath.Lib.Algebra.ValuationSeparatedRoots
import DkMath.Lib.NumberTheory.EllipticTangentDirections
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

#print "file: DkMath.Lib.NumberTheory.EllipticShallowSlope"

/-!
# NOTE-031-002C4: 浅い点の中心傾きは整で、一意な接線方向へ近づく

X=x−x₀、Y=y−y₀、F₀=F(x₀,y₀)、t=Y/Xとする。
v(X)<1かつv(F₀)<v(X)²なら、t²+a₁t−(a₂+3x₀)=X−F₀/X²の付値は1未満。
既存の二方向で左辺を(t−α)(t−β)へ分解し、単元分離から整性と排他的な二択を得る。
中心は曲線上の点ではないため、このtはMathlibの二曲線点の加法用slopeとは区別する。
浅さの厳密不等式を等号の場合へ拡張せず、同じ深さでの点の和差はまだ扱わない。
-/
namespace DkMath.Lib.NumberTheory.EllipticShallowSlope
open WeierstrassCurve EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections
open DkMath.Lib.Algebra.ValuationSeparatedRoots
variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve L}

/-- 同じ中心から指定された有限座標への傾き。中心自体は曲線上の点ではない。
分母が零でないことは浅さから別途証明し、零除算の便宜値に幾何学的な意味を与えない。 -/
def centreSlope (C : CriticalCentre A W) (x y : L) : L := (y - C.y) / (x - C.x)

/-- 厳密な浅さの条件からX差は非零となる。 -/
theorem shallow_x_ne (C : CriticalCentre A W) {x : L}
    (hsh : A.valuation (equationDefect W C.x C.y) < A.valuation (x - C.x) ^ 2) : x - C.x ≠ 0 := by
  intro hx
  rw [hx, map_zero, zero_pow two_ne_zero] at hsh
  exact not_lt_zero hsh

/-- 曲線上の有限座標の中心傾きは、ずれF₀を残す二次式を満たす。 -/
theorem centreSlope_quadratic (C : CriticalCentre A W) {x y : L} (h : W.toAffine.Equation x y)
    (hx : x - C.x ≠ 0) :
    centreSlope C x y ^ 2 + W.a₁ * centreSlope C x y - (W.a₂ + 3 * C.x) =
      (x - C.x) - equationDefect W C.x C.y / (x - C.x) ^ 2 := by
  have hF : equationDefect W x y = 0 := sub_eq_zero.mpr ((Affine.equation_iff _ _).mp h)
  have he := C.translated_equation (x - C.x) (y - C.y)
  rw [show C.x + (x - C.x) = x by ring, show C.y + (y - C.y) = y by ring, hF] at he
  dsimp only [centreSlope]
  field_simp [hx]
  linear_combination -he

/-- 同じ接線方向による傾きの二次式の因数分解。 -/
theorem quadratic_factorization {C : CriticalCentre A W} (D : TangentDirections C) (t : L) :
    (t - D.α) * (t - D.β) = t ^ 2 + W.a₁ * t - (W.a₂ + 3 * C.x) := by
  linear_combination -t * D.sum_eq + D.product_eq

/-- 二次式の付値が1未満なら、一方の方向への近さと他方の単元距離が決まる。 -/
theorem branches_of_quadratic_small {C : CriticalCentre A W} (D : TangentDirections C) {t : L}
    (hsmall : A.valuation (t ^ 2 + W.a₁ * t - (W.a₂ + 3 * C.x)) < 1) :
    (A.valuation (t - D.α) < 1 ∧ A.valuation (t - D.β) = 1) ∨
      (A.valuation (t - D.α) = 1 ∧ A.valuation (t - D.β) < 1) :=
  branches_of_small_product A.valuation D.separated (by rwa [quadratic_factorization D])

/-- 同じ条件から傾きの整性も従う。整性を枝分類の入力として循環的に仮定しない。 -/
theorem mem_of_quadratic_small {C : CriticalCentre A W} (D : TangentDirections C) {t : L}
    (hsmall : A.valuation (t ^ 2 + W.a₁ * t - (W.a₂ + 3 * C.x)) < 1) : t ∈ A :=
  mem_of_small_product A D.α_mem D.β_mem D.separated (by rwa [quadratic_factorization D])

/-- 中心へ近づく浅い点の傾きは、接錐の二次式を剰余体で満たす。
分母の非零性と除算の付値を先に確認し、浅さを厳密な小ささへ輸送する。 -/
theorem quadratic_small_of_shallow (C : CriticalCentre A W) {x y : L} (h : W.toAffine.Equation x y)
    (hnear : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect W C.x C.y) < A.valuation (x - C.x) ^ 2) :
    A.valuation (centreSlope C x y ^ 2 + W.a₁ * centreSlope C x y - (W.a₂ + 3 * C.x)) < 1 := by
  have hx := shallow_x_ne C hsh
  have hvx : 0 < A.valuation (x - C.x) := (Valuation.pos_iff _).mpr hx
  rw [centreSlope_quadratic C h hx]
  apply Valuation.map_sub_lt
  · exact hnear
  · rw [map_div₀, map_pow]
    exact (div_lt_one₀ (pow_pos hvx 2)).mpr hsh

/-- 浅い点の傾きは整で、Y差も小さく、近づく方向は排他的に決まる。
既存のDを用い、同じ中心・同じ点のまま二次式の小ささから全てを供給する。 -/
theorem slope_mem_and_branches_of_shallow {C : CriticalCentre A W} (D : TangentDirections C)
    {x y : L} (h : W.toAffine.Equation x y) (hnear : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect W C.x C.y) < A.valuation (x - C.x) ^ 2) :
    centreSlope C x y ∈ A ∧ A.valuation (y - C.y) < 1 ∧
      ((A.valuation (centreSlope C x y - D.α) < 1 ∧ A.valuation (centreSlope C x y - D.β) = 1) ∨
        (A.valuation (centreSlope C x y - D.α) = 1 ∧ A.valuation (centreSlope C x y - D.β) < 1)) := by
  have hsmall := quadratic_small_of_shallow C h hnear hsh
  have ht := mem_of_quadratic_small D hsmall
  refine ⟨ht, ?_, branches_of_quadratic_small D hsmall⟩
  have he : y - C.y = centreSlope C x y * (x - C.x) := by
    rw [centreSlope, div_mul_cancel₀ _ (shallow_x_ne C hsh)]
  rw [he, map_mul]
  exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr ht)).trans_lt hnear

/-- 楕円曲線の負号は中心傾きtを−t−a₁へ移す。中心のY偏微分の零を使う。 -/
theorem centreSlope_negY (C : CriticalCentre A W) (x y : L) (hx : x - C.x ≠ 0) :
    centreSlope C x (W.toAffine.negY x y) = -centreSlope C x y - W.a₁ := by
  dsimp only [centreSlope, Affine.negY]
  field_simp [hx]
  linear_combination -C.derivativeY

/-- 負号で二つの方向への距離が交換される。どちらの枝に近いかを同じDで追跡できる。 -/
theorem negY_branch_distances {C : CriticalCentre A W} (D : TangentDirections C) (x y : L)
    (hx : x - C.x ≠ 0) :
    A.valuation (centreSlope C x (W.toAffine.negY x y) - D.α) = A.valuation (centreSlope C x y - D.β) ∧
      A.valuation (centreSlope C x (W.toAffine.negY x y) - D.β) = A.valuation (centreSlope C x y - D.α) := by
  rw [centreSlope_negY C x y hx]
  have hα : -centreSlope C x y - W.a₁ - D.α = -(centreSlope C x y - D.β) := by
    linear_combination -D.sum_eq
  have hβ : -centreSlope C x y - W.a₁ - D.β = -(centreSlope C x y - D.α) := by
    linear_combination -D.sum_eq
  rw [hα, hβ, Valuation.map_neg, Valuation.map_neg]
  exact ⟨rfl, rfl⟩

/-- 浅い点とその負号の中心傾きは、単元の差を持つ。
二次式が剰余体で消えることと節点量の単元性から、(2t+a₁)²の付値を1と確定する。
方向の選び方には依存せず、2-torsionの臨界深さとの境界にも使える。 -/
theorem opposite_slope_separated_of_shallow (C : CriticalCentre A W) {x y : L}
    (h : W.toAffine.Equation x y) (hnear : A.valuation (x - C.x) < 1)
    (hsh : A.valuation (equationDefect W C.x C.y) < A.valuation (x - C.x) ^ 2) :
    A.valuation (centreSlope C x y - centreSlope C x (W.toAffine.negY x y)) = 1 := by
  have hsmall := quadratic_small_of_shallow C h hnear hsh
  let t := centreSlope C x y
  have he : (2 * t + W.a₁) ^ 2 =
      4 * (t ^ 2 + W.a₁ * t - (W.a₂ + 3 * C.x)) + (W.b₂ + 12 * C.x) := by
    rw [b₂]
    ring
  have h4 : A.valuation (4 * (t ^ 2 + W.a₁ * t - (W.a₂ + 3 * C.x))) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (ofNat_mem A 4))).trans_lt hsmall
  have hp : A.valuation (2 * t + W.a₁) ^ 2 = 1 := by
    rw [← map_pow, he, Valuation.map_add_eq_of_lt_right _ (by rwa [C.node_unit]), C.node_unit]
  rw [centreSlope_negY C x y (shallow_x_ne C hsh)]
  have hid : centreSlope C x y - (-centreSlope C x y - W.a₁) = 2 * t + W.a₁ := by
    dsimp only [t]
    ring
  rw [hid]
  exact (pow_eq_one_iff_left two_ne_zero).mp hp

end DkMath.Lib.NumberTheory.EllipticShallowSlope
