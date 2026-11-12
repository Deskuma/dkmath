/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Proof structure informed by S_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn.lean,
blob 4671d1857e26c4967080e5f48c4ce2fbe56484ee.
Modified: Reconstruct smooth inertia differences with the same DkMath centre and directions;
use pointwise smooth-reduction predicates, existing branch comparison and actual subgroup closure.
-/

import DkMath.Lib.NumberTheory.EllipticNodalReductionKernel
import DkMath.Lib.NumberTheory.EllipticDepthInertia
import DkMath.Lib.NumberTheory.ValuationTameCharacter

#print "file: DkMath.Lib.NumberTheory.EllipticNodalInertia"

/-!
# NOTE-031-004 第2部: 節点還元での慣性変化量

慣性は中心を固定し、X方向の深さと浅い枝を保存する。
零成分外の点とその慣性像の差は、浅い場合は同じ枝の比較、臨界側では二点の和の補題により
滑らかに還元する。零成分内の場合は、深さによる分類と既に証明した加法閉性を使う。
ここでは位数が剰余標数と一致しても点自体の固定を主張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticNodalInertia
open WeierstrassCurve IsLocalRing EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticGoodReductionSeparation EllipticSmoothReduction
open ValuationInertia ValuationTameCharacter.TameCharacter EllipticShallowSlope

/-- 同じ一般ファイバーの二点の差について、モデルの一致を保って加法閉性を使う。 -/
theorem smooth_sub_of_model {L : Type*} [Field L] [DecidableEq L]
    {A : ValuationSubring L} (M : WeierstrassCurve A) (V : WeierstrassCurve L)
    (hmodel : M.map A.subtype = V) {P Q : V.toAffine.Point}
    (hP : HasSmoothReduction M P) (hQ : HasSmoothReduction M Q) :
    HasSmoothReduction M (P - Q) := by
  classical
  subst V
  rw [sub_eq_add_neg]
  exact (smooth_add_and_reduce M hP (smooth_neg M hQ)).1

/-- 臨界側の二点の和について、同じモデルと同じ中心・方向を輸送する。 -/
theorem critical_pair_smooth_of_model {L : Type*} [Field L] [DecidableEq L]
    {A : ValuationSubring L} (M : WeierstrassCurve A) (V : WeierstrassCurve L)
    (hmodel : M.map A.subtype = V) (C : CriticalCentre A V) (D : TangentDirections C)
    {x₁ y₁ x₂ y₂ : L} (h₁ : V.toAffine.Nonsingular x₁ y₁)
    (h₂ : V.toAffine.Nonsingular x₂ y₂)
    (hX₁ : A.valuation (x₁ - C.x) < 1)
    (hanti₁ : A.valuation (x₁ - C.x) ^ 2 ≤ A.valuation (equationDefect V C.x C.y))
    (hX₂ : A.valuation (x₂ - C.x) < 1)
    (hanti₂ : A.valuation (x₂ - C.x) ^ 2 ≤ A.valuation (equationDefect V C.x C.y)) :
    HasSmoothReduction M (Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂) := by
  subst V
  exact EllipticCriticalPair.critical_pair_smooth M C D h₁ h₂ hX₁ hanti₁ hX₂ hanti₂

/-- 同じ有理曲線の臨界中心を慣性が固定するなら、全ての点の慣性変化量は零成分へ入る。
全点の固定や、剰余標数と素なtorsion位数は仮定しない。 -/
theorem inertia_difference_smooth [DecidableEq (AlgebraicClosure ℚ)]
    (E : WeierstrassCurve ℚ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : WeierstrassCurve A) (hmodel : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (hfix : σ C.x = C.x ∧ σ C.y = C.y)
    (P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    HasSmoothReduction M (Affine.Point.map σ.toAlgHom P - P) := by
  classical
  have hdec := (mem_inertiaSubgroupIn_iff.mp hσ).1
  cases P with
  | zero =>
    change HasSmoothReduction M (0 - 0 : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point)
    rw [sub_self]
    exact hasSmoothReduction_zero M _
  | some x y h =>
    rw [Affine.Point.map_some]
    have h' := (E.toAffine.baseChange_nonsingular σ.toAlgHom.injective x y).mpr h
    have hlev : A.valuation (σ x - C.x) = A.valuation (x - C.x) := by
      calc A.valuation (σ x - C.x) = A.valuation (σ (x - C.x)) := by
              rw [map_sub σ, hfix.1]
             _ = A.valuation (x - C.x) := valuation_apply_eq hdec _
    by_cases hP : HasSmoothReduction M (Affine.Point.some x y h)
    · apply smooth_sub_of_model M _ hmodel ?_ hP
      by_contra hbad
      have hc := (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model
        M _ hmodel C h').mp hbad
      change A.valuation (σ x - C.x) < 1 at hc
      rw [hlev] at hc
      exact ((EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model
        M _ hmodel C h).mpr hc) hP
    · have hX := (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model
        M _ hmodel C h).mp hP
      have hX' : A.valuation (σ x - C.x) < 1 := hlev ▸ hX
      by_cases hsh : A.valuation (equationDefect (E.baseChange (AlgebraicClosure ℚ)) C.x C.y) <
          A.valuation (x - C.x) ^ 2
      · have ht := (slope_mem_and_branches_of_shallow D h.1 hX hsh).1
        have hb := ValuationPrimeSupport.inertia_apply_sub_mem_nonunits A ℚ σ hσ ht
        have hbr : A.valuation (centreSlope C (σ x) (σ y) - centreSlope C x y) < 1 := by
          have he : σ (centreSlope C x y) = centreSlope C (σ x) (σ y) := by
            simp only [centreSlope, map_div₀, map_sub, hfix.1, hfix.2]
          rw [ValuationSubring.mem_nonunits_iff, he] at hb
          exact hb
        exact (EllipticBranchComparison.sub_of_same_branch_of_model M _ hmodel C D h' h
          hX' hX hlev (by
            change A.valuation (equationDefect _ C.x C.y) < A.valuation (σ x - C.x) ^ 2
            rwa [hlev]) hbr).1
      · rw [sub_eq_add_neg, Affine.Point.neg_some]
        exact critical_pair_smooth_of_model M _ hmodel C D h'
          ((Affine.nonsingular_neg ..).mpr h) hX' (by
            change A.valuation (σ x - C.x) ^ 2 ≤ A.valuation (equationDefect _ C.x C.y)
            rw [hlev]
            exact not_lt.mp hsh)
          hX (not_lt.mp hsh)

end DkMath.Lib.NumberTheory.EllipticNodalInertia
