/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Tangent-root construction adapted from
S_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction.lean,
blob e3a454fddddd39651f2791c4a538ec90c9e926d4, TFDisp.critical_center.
Modified: construct directions over an existing DkMath centre; use unit 2 for integrality
and the existing inertia square-root lemma for fixedness; preserve the same centre.
-/

import DkMath.Lib.NumberTheory.EllipticCriticalCentre

#print "file: DkMath.Lib.NumberTheory.EllipticTangentDirections"

/-!
# NOTE-031-002C3: 同じ臨界中心の二つの接線方向

前章の中心を選び直さず、二次形式Y²+a₁XY−(a₂+3x₀)X²を分解する。
方向α,βの差は単元なので、剰余体でも異なる二つの方向になる。
2が単元の場合に存在・整性を証明し、同じ有理曲線の慣性元は各方向を個別に固定する。
この方向は節点の接錐の根であり、まだ各torsion点への枝ラベルではない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTangentDirections
open WeierstrassCurve EllipticCriticalCentre EllipticCriticalCentreAlgebra

/-- 同じ臨界中心に属する順序付きの接線方向。
中心Cを型の添字に保ち、別の中心の根・整性・分離条件を混用しない。 -/
structure TangentDirections {L : Type*} [Field L] {A : ValuationSubring L}
    {W : WeierstrassCurve L} (C : CriticalCentre A W) where
  /-- 第一の接線方向。 -/
  α : L
  /-- 第二の接線方向。 -/
  β : L
  /-- 第一方向は付値環内にある。 -/
  α_mem : α ∈ A
  /-- 第二方向は付値環内にある。 -/
  β_mem : β ∈ A
  /-- 二次式の一次係数との関係。 -/
  sum_eq : α + β = -W.a₁
  /-- 二次式の定数項との関係。 -/
  product_eq : α * β = -(W.a₂ + 3 * C.x)
  /-- 剰余体で二方向が衝突しない。 -/
  separated : A.valuation (α - β) = 1

/-- 2が単元なら、任意の既存の臨界中心に二方向が存在する。
節点量n=b₂+12x₀の平方根rを取り、(−a₁±r)/2を使う。
中心を同時に選び直さず、Cの全ての不変条件を保持する。 -/
theorem exists_tangentDirections {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]
    (A : ValuationSubring L) (W : WeierstrassCurve L) (C : CriticalCentre A W)
    (ha₁ : W.a₁ ∈ A) (h2 : A.valuation (2 : L) = 1) : Nonempty (TangentDirections C) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (W.b₂ + 12 * C.x)
  have hvr : A.valuation r = 1 := by
    apply (pow_eq_one_iff_left two_ne_zero).mp
    rw [sq, ← map_mul, ← hr, C.node_unit]
  have hrA : r ∈ A := (A.valuation_le_one_iff _).mp hvr.le
  have hi2 : (2 : L)⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff, map_inv₀, h2, inv_one]
  let α : L := (-W.a₁ + r) / 2
  let β : L := (-W.a₁ - r) / 2
  have hab : α - β = r := by dsimp [α, β]; field_simp; ring
  refine ⟨{
    α := α
    β := β
    α_mem := by
      dsimp only [α]
      rw [div_eq_mul_inv]
      exact A.toSubring.mul_mem (A.toSubring.add_mem (A.toSubring.neg_mem ha₁) hrA) hi2
    β_mem := by
      dsimp only [β]
      rw [div_eq_mul_inv]
      exact A.toSubring.mul_mem (A.toSubring.sub_mem (A.toSubring.neg_mem ha₁) hrA) hi2
    sum_eq := by dsimp [α, β]; field_simp; ring
    product_eq := ?_
    separated := by rw [hab]; exact hvr }⟩
  dsimp only [α, β]
  have hb : W.b₂ = W.a₁ ^ 2 + 4 * W.a₂ := rfl
  linear_combination (1 / 4 : L) * hr - (1 / 4 : L) * hb

namespace TangentDirections
variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve L}
variable {C : CriticalCentre A W}

/-- 分離条件は実際の二方向の非等号を与える。 -/
theorem ne (D : TangentDirections C) : D.α ≠ D.β := by
  intro he
  have h := D.separated
  rw [he, sub_self, map_zero] at h
  exact zero_ne_one h

/-- 二方向の差の平方は、同じ中心の節点量に一致する。 -/
theorem difference_square (D : TangentDirections C) :
    (D.α - D.β) * (D.α - D.β) = W.b₂ + 12 * C.x := by
  have hb : W.b₂ = W.a₁ ^ 2 + 4 * W.a₂ := rfl
  linear_combination (D.α + D.β - W.a₁) * D.sum_eq - 4 * D.product_eq - hb

/-- 同じ中心と実際の方向を用いた、方程式の局所的な因数分解。
これは有限な多項式恒等式であり、点の位数や深さの漸化式はまだ使わない。 -/
theorem translated_equation (D : TangentDirections C) (X Y : L) :
    equationDefect W (C.x + X) (C.y + Y) = equationDefect W C.x C.y +
      (Y - D.α * X) * (Y - D.β * X) - X ^ 3 :=
  translated_defect_factor W C.x C.y X Y D.α D.β C.derivativeY C.derivativeX D.sum_eq D.product_eq

/-- 両方向は同じ接錐の二次式の実際の根である。 -/
theorem roots (D : TangentDirections C) :
    D.α ^ 2 + W.a₁ * D.α - (W.a₂ + 3 * C.x) = 0 ∧
      D.β ^ 2 + W.a₁ * D.β - (W.a₂ + 3 * C.x) = 0 := by
  constructor
  · linear_combination D.α * D.sum_eq - D.product_eq
  · linear_combination D.β * D.sum_eq - D.product_eq

/-- 実際の曲線方程式を満たす有限座標では、二つの枝座標の積がX³−F₀となる。
F₀は零でない中心のずれであり、接錐の因数分解を曲線そのものの二直線の和と誤読しない。 -/
theorem point_equation (D : TangentDirections C) {x y : L} (h : W.toAffine.Equation x y) :
    ((y - C.y) - D.α * (x - C.x)) * ((y - C.y) - D.β * (x - C.x)) =
      (x - C.x) ^ 3 - equationDefect W C.x C.y := by
  have hF : equationDefect W x y = 0 := sub_eq_zero.mpr ((Affine.equation_iff _ _).mp h)
  have he := D.translated_equation (x - C.x) (y - C.y)
  rw [show C.x + (x - C.x) = x by ring, show C.y + (y - C.y) = y by ring, hF] at he
  linear_combination -he

/-- 整な二方向の剰余値は異なる。単なる体内の非等号より強い分離である。 -/
theorem residue_ne (D : TangentDirections C) :
    IsLocalRing.residue A (⟨D.α, D.α_mem⟩ : A) ≠ IsLocalRing.residue A (⟨D.β, D.β_mem⟩ : A) := by
  intro he
  have hzero : IsLocalRing.residue A (⟨D.α, D.α_mem⟩ - ⟨D.β, D.β_mem⟩ : A) = 0 := by
    rw [map_sub, he, sub_self]
  have hsmall := (IsLocalRing.residue_eq_zero_iff _).mp hzero
  have hv := (ValuationSubring.mem_nonunits_iff A).mp (ValuationSubring.coe_mem_nonunits_iff.mpr hsmall)
  change A.valuation (D.α - D.β) < 1 at hv
  rw [D.separated] at hv
  exact lt_irrefl _ hv

end TangentDirections

open ValuationInertia ValuationPrimeSupport

/-- 奇素数の状況では、同じ中心の各接線方向も全慣性元に個別に固定される。
中心座標の固定後、単元α−βの平方の固定から符号を分離し、和と差から各方向を復元する。 -/
theorem TangentDirections.inertia_fixed (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))}
    (D : TangentDirections C) (h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ) :
    σ D.α = D.α ∧ σ D.β = D.β := by
  have ex := (C.inertia_fixed E A h2 σ hσ).1
  have eb : σ (E.baseChange (AlgebraicClosure ℚ)).b₂ = (E.baseChange (AlgebraicClosure ℚ)).b₂ := by simp [baseChange]
  have e₁ : σ (E.baseChange (AlgebraicClosure ℚ)).a₁ = (E.baseChange (AlgebraicClosure ℚ)).a₁ := by simp [baseChange]
  have ed := inertia_fixed_of_unit_square A ℚ h2 σ hσ D.separated (by
    rw [D.difference_square, map_add, map_mul, map_ofNat, eb, ex])
  have es := congrArg σ D.sum_eq
  simp only [map_add, map_neg, e₁] at es
  have ed' : σ D.α - σ D.β = D.α - D.β := by simpa only [map_sub] using ed
  constructor
  · linear_combination (1 / 2 : AlgebraicClosure ℚ) * es + (1 / 2 : AlgebraicClosure ℚ) * ed' -
      (1 / 2 : AlgebraicClosure ℚ) * D.sum_eq
  · linear_combination (1 / 2 : AlgebraicClosure ℚ) * es - (1 / 2 : AlgebraicClosure ℚ) * ed' -
      (1 / 2 : AlgebraicClosure ℚ) * D.sum_eq

end DkMath.Lib.NumberTheory.EllipticTangentDirections
