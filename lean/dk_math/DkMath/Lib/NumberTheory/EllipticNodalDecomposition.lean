/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionDepth
import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
import DkMath.Lib.NumberTheory.EllipticSmoothReduction
import DkMath.Lib.NumberTheory.ValuationTameCharacter

#print "file: DkMath.Lib.NumberTheory.EllipticNodalDecomposition"

/-!
# 臨界中心の分解群固定と、高次捩れの和差の二択

二つの臨界候補は節点平方根の符号で分かれる。ずれが小さく節点量が単元である
同じ中心は、分解群で反対の候補へ移れない。`432` は体内では約分するが、
付値では整数として1以下の因子に保つため、2・3上でも使える。

中心の固定と付値保存から同じ深さを得て、既存の浅い捩れ点の二枝比較へ接続する。
和差のどちらが滑らかになるかを、外部の二択 provider として仮定しない。
-/

namespace DkMath.Lib.NumberTheory.EllipticNodalDecomposition

open WeierstrassCurve EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticGoodReductionSeparation EllipticShallowSlope
open ValuationTameCharacter.TameCharacter EllipticTorsionRepresentation

noncomputable local instance instDecidableEqNodalDecomposition {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じ一般ファイバーで滑らかな還元を持つ点の実際の部分群。 -/
noncomputable def smoothSubgroupOfModel {K : Type*} [Field K]
    {A : ValuationSubring K} (M : WeierstrassCurve A) (V : WeierstrassCurve K)
    (hmodel : M.map A.subtype = V) : AddSubgroup V.toAffine.Point := by
  classical
  subst V
  exact EllipticSmoothReduction.zeroComponentSubgroup M

/-- 同じ点の所属は元の滑らかな還元条件そのもの。 -/
theorem mem_smoothSubgroupOfModel_iff {K : Type*} [Field K]
    {A : ValuationSubring K} (M : WeierstrassCurve A) (V : WeierstrassCurve K)
    (hmodel : M.map A.subtype = V) (P : V.toAffine.Point) :
    P ∈ smoothSubgroupOfModel M V hmodel ↔ HasSmoothReduction M P := by
  subst V
  rfl

/-- 任意の臨界中心での、節点量とずれの恒等式。 -/
theorem defect_identity {K : Type*} [Field K] [CharZero K]
    {A : ValuationSubring K} {V : WeierstrassCurve K} (C : CriticalCentre A V) :
    864 * equationDefect V C.x C.y = V.c₆ + V.c₄ * (V.b₂ + 12 * C.x) := by
  let n := V.b₂ + 12 * C.x
  have hx : centreX V n = C.x := by dsimp [centreX, n]; ring
  have hy : centreY V n = C.y := by
    dsimp [centreY]
    rw [hx]
    linear_combination (-1 / 2 : K) * C.derivativeY
  have h := defect_at_centre V (s := n) C.node_square
  rw [hx, hy] at h
  exact h

/-- 任意の素点で、同じ小さいずれを持つ臨界中心は分解群に固定される。 -/
theorem centre_decomposition_fixed (E : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ)))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    σ C.x = C.x ∧ σ C.y = C.y := by
  let V := E.baseChange (AlgebraicClosure ℚ)
  let n := V.b₂ + 12 * C.x
  let F := equationDefect V C.x C.y
  have hb : σ V.b₂ = V.b₂ := by simp [V, baseChange]
  have hc : σ V.c₄ = V.c₄ := by simp [V, baseChange]
  have hc6 : σ V.c₆ = V.c₆ := by simp [V, baseChange]
  have hn : n * n = V.c₄ := C.node_square
  have hs : σ n * σ n = n * n := by rw [← map_mul, hn, hc]
  have hfact : (σ n - n) * (σ n + n) = 0 := by linear_combination hs
  have hnfix : σ n = n := by
    rcases mul_eq_zero.mp hfact with he | he
    · exact sub_eq_zero.mp he
    · have hop : σ n = -n := eq_neg_of_add_eq_zero_left he
      have hF : 864 * F = V.c₆ + V.c₄ * n := defect_identity C
      have hFσ := congrArg σ hF
      simp only [map_mul, map_add, map_ofNat, hc6, hc, hop] at hFσ
      have hid : 432 * (F - σ F) = V.c₄ * n := by
        linear_combination (1 / 2 : AlgebraicClosure ℚ) * hF - (1 / 2 : AlgebraicClosure ℚ) * hFσ
      have hsmall : A.valuation (F - σ F) < 1 :=
        Valuation.map_sub_lt _ C.defect_small (by rw [valuation_apply_eq hσ]; exact C.defect_small)
      have h432 : A.valuation (432 : AlgebraicClosure ℚ) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (natCast_mem A 432)
      have hlt : A.valuation (432 * (F - σ F)) < 1 := by
        rw [map_mul]
        exact (mul_le_of_le_one_left' h432).trans_lt hsmall
      have hvc : A.valuation V.c₄ = 1 := by rw [← hn, map_mul, C.node_unit, one_mul]
      rw [hid, map_mul, hvc, C.node_unit, one_mul] at hlt
      exact (lt_irrefl 1 hlt).elim
  have hx : σ C.x = C.x := by
    dsimp [n] at hnfix
    rw [map_add, map_mul, map_ofNat, hb] at hnfix
    linear_combination (1 / 12 : AlgebraicClosure ℚ) * hnfix
  refine ⟨hx, ?_⟩
  have hy := congrArg σ C.derivativeY
  have h1 : σ (E.baseChange (AlgebraicClosure ℚ)).a₁ = (E.baseChange (AlgebraicClosure ℚ)).a₁ := by simp [baseChange]
  have h3 : σ (E.baseChange (AlgebraicClosure ℚ)).a₃ = (E.baseChange (AlgebraicClosure ℚ)).a₃ := by simp [baseChange]
  simp only [map_add, map_mul, map_ofNat, map_zero, h1, h3, hx] at hy
  linear_combination (1 / 2 : AlgebraicClosure ℚ) * hy - (1 / 2 : AlgebraicClosure ℚ) * C.derivativeY

private theorem branch_distance_of_model {K : Type*} [Field K]
    {A : ValuationSubring K} (M : WeierstrassCurve A) (V : WeierstrassCurve K)
    (hmodel : M.map A.subtype = V) (C : CriticalCentre A V) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : K} (h₁ : V.toAffine.Equation x₁ y₁) (h₂ : V.toAffine.Equation x₂ y₂)
    (hX₁ : A.valuation (x₁ - C.x) < 1) (hX₂ : A.valuation (x₂ - C.x) < 1)
    (hlev : A.valuation (x₁ - C.x) = A.valuation (x₂ - C.x))
    (hsh : A.valuation (equationDefect V C.x C.y) < A.valuation (x₁ - C.x) ^ 2) :
    A.valuation (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) < 1 ∨
      A.valuation (centreSlope C x₁ y₁ - centreSlope C x₂ y₂) = 1 := by
  subst V
  exact EllipticBranchComparison.branch_distance_dichotomy M C D h₁ h₂ hX₁ hX₂ hlev hsh

/-- 分解群像との差または和が滑らかになる。奇数単元次数なら素数冪でも使える。 -/
theorem sub_or_add_smooth_of_odd_torsion
    (E : WeierstrassCurve ℚ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : WeierstrassCurve A) (hmodel : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) (hunit : A.valuation (n : AlgebraicClosure ℚ) = 1)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ A.decompositionSubgroup ℚ)
    {P : Points E} (ht : n • P = 0) (hout : ¬ HasSmoothReduction M P) :
    HasSmoothReduction M (pointAction E σ P - P) ∨ HasSmoothReduction M (pointAction E σ P + P) := by
  classical
  cases P with
  | zero => exact (hout (hasSmoothReduction_zero M _)).elim
  | some x y h =>
    have hX := (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model M _ hmodel C h).mp hout
    have hsh := (EllipticTorsionDepth.odd_torsion_depth_of_model M _ hmodel C D hodd hn hunit h ht hX).1
    have hfix := centre_decomposition_fixed E A C σ hσ
    have hlev : A.valuation (σ x - C.x) = A.valuation (x - C.x) := by
      calc A.valuation (σ x - C.x) = A.valuation (σ (x - C.x)) := by rw [map_sub σ, hfix.1]
        _ = A.valuation (x - C.x) := valuation_apply_eq hσ _
    have hXσ : A.valuation (σ x - C.x) < 1 := hlev ▸ hX
    have hsσ := (E.toAffine.baseChange_nonsingular σ.toAlgHom.injective x y).mpr h
    have hshσ : A.valuation (equationDefect (E.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
        A.valuation (σ x - C.x) ^ 2 := by
      rw [hlev]; exact hsh
    change HasSmoothReduction M (Affine.Point.map σ.toAlgHom (.some x y h) - .some x y h) ∨ _
    rw [Affine.Point.map_some]
    rcases branch_distance_of_model M _ hmodel C D hsσ.1 h.1 hXσ hX hlev hshσ with hb | hb
    · exact Or.inl (EllipticBranchComparison.sub_of_same_branch_of_model M _ hmodel C D
        hsσ h hXσ hX hlev hshσ hb).1
    · exact Or.inr (EllipticBranchComparison.add_of_opposite_branch_of_model M _ hmodel C D
        hsσ h hXσ hX hlev hshσ hb).1

end DkMath.Lib.NumberTheory.EllipticNodalDecomposition
