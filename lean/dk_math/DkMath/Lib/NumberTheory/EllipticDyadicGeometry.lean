/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.ValuationQuadraticRoot
import DkMath.Lib.NumberTheory.EllipticTangentDirections
import DkMath.Lib.NumberTheory.ValuationTameCharacter

#print "file: DkMath.Lib.NumberTheory.EllipticDyadicGeometry"

/-!
# NOTE-032-003A: 2上の臨界中心の一意性と接線方向

[DkMath.Lib] 両偏微分が零なら、X座標は6X²+b₂X+b₄=0を満たす。
2が非単元のとき、整な中心の節点条件v(b₂+12x₀)=1からv(b₂)=1が従う。
最高次係数6は非単元なので、前章の二次式の一意性により整な中心は一意である。
有理曲線の分解群は整性と偏微分の零を保存するから、中心を座標ごとに固定する。
これは2が単元であることを使う平方根の符号分離とは別の証明である。

接線方向にはモニック二次式の根の整性を使う。存在は2の単元性を要求しない。
中心固定後、慣性の剰余合同と二方向の分離から、各方向も個別に固定される。
分解群全体で各方向が固定されるとは主張しない。残る剰余作用が枝交換の候補となる。
-/
namespace DkMath.Lib.NumberTheory.EllipticDyadicGeometry
open DkMath.Lib.Algebra.ValuationQuadraticRoot
open WeierstrassCurve EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections
open ValuationInertia ValuationPrimeSupport
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve K}

/-- [DkMath.Lib] 任意の臨界中心のX座標は、分母を払った臨界二次式の根である。 -/
theorem criticalQuadratic_eq_zero (C : CriticalCentre A W) : criticalQuadratic W C.x = 0 := by
  have h := derivative_relation W C.x C.y
  rw [C.derivativeX, C.derivativeY, mul_zero, mul_zero, zero_sub] at h
  exact neg_eq_zero.mp h.symm

/-- [DkMath.Lib] 2が非単元なら、整な中心の節点条件はb₂の単元性を強制する。
12x₀が非単元なので、単元b₂+12x₀の付値を変えずに引き戻せる。 -/
theorem valuation_b2_eq_one (C : CriticalCentre A W) (h2 : A.valuation (2 : K) < 1) :
    A.valuation W.b₂ = 1 := by
  have h12 : A.valuation (12 : K) < 1 := by
    simpa using valuation_intCast_lt_one_of_dvd A h2 (z := 12) (by norm_num)
  have hsmall : A.valuation (12 * C.x) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).mpr C.x_mem)).trans_lt h12
  have he : W.b₂ = (W.b₂ + 12 * C.x) + -(12 * C.x) := by ring
  rw [he, Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_neg, C.node_unit]), C.node_unit]

/-- [DkMath.Lib] 2が非単元なら、整なX座標と偏微分の零だけで既存の中心と一致する。
比較相手の節点条件やずれの深さを要求せず、分解群像との比較へ適用できる形にする。 -/
theorem coordinates_eq_of_derivatives [CharZero K] (C : CriticalCentre A W)
    (h2 : A.valuation (2 : K) < 1) {x y : K} (hx : x ∈ A)
    (hY : 2 * y + W.a₁ * x + W.a₃ = 0)
    (hX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0) :
    x = C.x ∧ y = C.y := by
  have h6 : A.valuation (6 : K) < 1 := by
    simpa using valuation_intCast_lt_one_of_dvd A h2 (z := 6) (by norm_num)
  have hxroot : criticalQuadratic W x = 0 := by
    have h := derivative_relation W x y
    rw [hX, hY, mul_zero, mul_zero, zero_sub] at h
    exact neg_eq_zero.mp h.symm
  have ex : x = C.x := eq_of_integral_quadratic_roots A h6 (valuation_b2_eq_one C h2)
    hx C.x_mem hxroot (criticalQuadratic_eq_zero C)
  refine ⟨ex, ?_⟩
  rw [ex] at hY
  linear_combination (1 / 2 : K) * hY - (1 / 2 : K) * C.derivativeY

/-- [DkMath.Lib] 2上の同じ曲線の二つの臨界中心は座標ごとに一致する。
中心の存在と一意性を分離し、存在しない曲線へ存在を付け加えない。 -/
theorem coordinates_eq [CharZero K] (C C' : CriticalCentre A W)
    (h2 : A.valuation (2 : K) < 1) : C'.x = C.x ∧ C'.y = C.y :=
  coordinates_eq_of_derivatives C h2 C'.x_mem C'.derivativeY C'.derivativeX

/-- [DkMath.Lib] 有理曲線の2上の中心は、慣性より大きい分解群全体に固定される。
分解群は整性を保存し、有理係数の偏微分条件も保存するので、整な中心の一意性を使える。 -/
theorem decomposition_fixed (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ)))
    (h2 : A.valuation (2 : AlgebraicClosure ℚ) < 1)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    σ C.x = C.x ∧ σ C.y = C.y := by
  apply coordinates_eq_of_derivatives C h2
    ((ValuationTameCharacter.TameCharacter.apply_mem_iff hσ C.x).mpr C.x_mem)
  · simpa [WeierstrassCurve.baseChange, map_ofNat] using congrArg σ C.derivativeY
  · simpa [WeierstrassCurve.baseChange, map_ofNat] using congrArg σ C.derivativeX

/-- [DkMath.Lib] 実際の全ガロア群内の慣性所属から分解群所属へ戻し、2上の中心固定を得る。 -/
theorem inertia_fixed (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ)))
    (h2 : A.valuation (2 : AlgebraicClosure ℚ) < 1)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ) :
    σ C.x = C.x ∧ σ C.y = C.y := by
  obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.mp hσ
  exact decomposition_fixed E A C h2 τ τ.property

/-- [DkMath.Lib] 整係数と既存の中心から二方向を構成する。2の単元性は不要。
平方根を使う式の分母2は体内の計算だけに使い、根の整性はモニック二次式から証明する。 -/
theorem exists_tangentDirections [CharZero K] [IsAlgClosed K]
    (A : ValuationSubring K) (W : WeierstrassCurve K) (C : CriticalCentre A W)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) : Nonempty (TangentDirections C) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (W.b₂ + 12 * C.x)
  have hvr : A.valuation r = 1 := by
    apply (pow_eq_one_iff_left two_ne_zero).mp
    rw [sq, ← map_mul, ← hr, C.node_unit]
  let α : K := (-W.a₁ + r) / 2
  let β : K := -W.a₁ - α
  have hroot : α ^ 2 + W.a₁ * α - (W.a₂ + 3 * C.x) = 0 := by
    dsimp [α]
    have hb : W.b₂ = W.a₁ ^ 2 + 4 * W.a₂ := rfl
    linear_combination -(1 / 4 : K) * hr + (1 / 4 : K) * hb
  have hαA : α ∈ A := mem_of_monic_quadratic A ha₁
    (neg_mem (add_mem ha₂ (mul_mem (ofNat_mem A 3) C.x_mem))) (by simpa only [sub_eq_add_neg] using hroot)
  have hβA : β ∈ A := sub_mem (neg_mem ha₁) hαA
  have hab : α - β = r := by dsimp [α, β]; field_simp; ring
  refine ⟨{
    α := α
    β := β
    α_mem := hαA
    β_mem := hβA
    sum_eq := by dsimp [β]; ring
    product_eq := ?_
    separated := by rw [hab]; exact hvr }⟩
  dsimp [β]
  linear_combination -hroot

private theorem root_eq_of_near {a b z : K} (hsep : A.valuation (a - b) = 1)
    (hroot : (z - a) * (z - b) = 0) (hsmall : A.valuation (z - a) < 1) : z = a := by
  rcases mul_eq_zero.mp hroot with h | h
  · exact sub_eq_zero.mp h
  · have he : z = b := sub_eq_zero.mp h
    rw [he, Valuation.map_sub_swap, hsep] at hsmall
    exact (lt_irrefl _ hsmall).elim

/-- [DkMath.Lib] 中心のX座標を慣性が固定すれば、分離した二方向も個別に固定される。
慣性の剰余合同は方向の交換を禁じる。2が単元という仮定は不要である。
剰余作用を持つ分解群元は方向を交換し得るので、その群へ結論を拡張しない。 -/
theorem tangentDirections_inertia_fixed (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))} (D : TangentDirections C)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (hCx : σ C.x = C.x) : σ D.α = D.α ∧ σ D.β = D.β := by
  have hrα : (σ D.α) ^ 2 + (E.baseChange (AlgebraicClosure ℚ)).a₁ * σ D.α -
      ((E.baseChange (AlgebraicClosure ℚ)).a₂ + 3 * C.x) = 0 := by
    simpa [WeierstrassCurve.baseChange, map_ofNat, hCx] using congrArg σ D.roots.1
  have hrβ : (σ D.β) ^ 2 + (E.baseChange (AlgebraicClosure ℚ)).a₁ * σ D.β -
      ((E.baseChange (AlgebraicClosure ℚ)).a₂ + 3 * C.x) = 0 := by
    simpa [WeierstrassCurve.baseChange, map_ofNat, hCx] using congrArg σ D.roots.2
  have hα : (σ D.α - D.α) * (σ D.α - D.β) = 0 := by
    linear_combination hrα - (σ D.α) * D.sum_eq + D.product_eq
  have hβ : (σ D.β - D.β) * (σ D.β - D.α) = 0 := by
    linear_combination hrβ - (σ D.β) * D.sum_eq + D.product_eq
  exact ⟨root_eq_of_near D.separated hα ((ValuationSubring.mem_nonunits_iff A).mp
      (inertia_apply_sub_mem_nonunits A ℚ σ hσ D.α_mem)),
    root_eq_of_near (by rw [Valuation.map_sub_swap]; exact D.separated) hβ ((ValuationSubring.mem_nonunits_iff A).mp
      (inertia_apply_sub_mem_nonunits A ℚ σ hσ D.β_mem))⟩

end DkMath.Lib.NumberTheory.EllipticDyadicGeometry
