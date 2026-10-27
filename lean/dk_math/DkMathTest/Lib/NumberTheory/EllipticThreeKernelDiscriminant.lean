/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.Lib.NumberTheory.EllipticThreeKernelDiscriminant
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction

#print "file: DkMathTest.Lib.NumberTheory.EllipticThreeKernelDiscriminant"

/-! 実3点核の同じ商について、7・47の判別式の付値を検査する。 -/
namespace EllipticThreeKernelDiscriminantTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation EllipticGoodReductionSeparation
open EllipticFiniteKernelReductionTest EllipticThreeKernelDiscriminant
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
noncomputable local instance instDecidableEqThreeKernelDiscriminantTest {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
local instance : (source (1 : ℚ) 7).IsElliptic := ⟨by
  norm_num [source, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
noncomputable local instance instFintypeThreeKernelDiscriminantTest : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])

/-- 実際の同じ商標的が三次判別式の積公式を満たす。 -/
theorem sample_product_identity :
    (kernelModel sample sampleKernel).Δ * ((7 : AlgebraicClosure ℚ) ^ 2) ^ 4 =
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 3 := by
  change (@kernelModel ℚ _ (source (1 : ℚ) 7) _ _ sampleKernel instFintypeThreeKernelDiscriminantTest).Δ * ((7 : AlgebraicClosure ℚ) ^ 2) ^ 4 =
    ((source (1 : ℚ) 7).map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 3
  let R : sampleKernel := ⟨Q, Or.inr (Or.inl rfl)⟩
  have hR : R.val ≠ 0 := Point.some_ne_zero _
  have hx : R.val.xc = 0 := rfl
  have hy : R.val.yc = 0 := rfl
  simpa only [map_one, map_ofNat] using
    (@kernelModel_discriminant_product ℚ _ _ 1 7 _ sampleKernel instFintypeThreeKernelDiscriminantTest sampleKernel_card R hR hx hy)

/-- 47上では b=7 が単元なので、同じ商の判別式の付値は源の3乗。 -/
theorem sample_47_value (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    A.valuation (kernelModel sample sampleKernel).Δ =
      A.valuation (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 3 := by
  change A.valuation (@kernelModel ℚ _ (source (1 : ℚ) 7) _ _ sampleKernel instFintypeThreeKernelDiscriminantTest).Δ =
    A.valuation ((source (1 : ℚ) 7).map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 3
  let R : sampleKernel := ⟨Q, Or.inr (Or.inl rfl)⟩
  have hR : R.val ≠ 0 := Point.some_ne_zero _
  have hb : A.valuation (7 : AlgebraicClosure ℚ) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 47)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 7) (by norm_num)
  simpa only [map_one, map_ofNat] using
    (@kernelModel_value_of_b_unit ℚ _ _ 1 7 _ sampleKernel instFintypeThreeKernelDiscriminantTest sampleKernel_card R hR rfl rfl _ _ A.valuation (by simpa using hb))

/-- 7上では a³−27b=−188 が単元なので、源の判別式の付値は同じ商の3乗。 -/
theorem sample_7_value (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    A.valuation (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ =
      A.valuation (kernelModel sample sampleKernel).Δ ^ 3 := by
  change A.valuation ((source (1 : ℚ) 7).map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ =
    A.valuation (@kernelModel ℚ _ (source (1 : ℚ) 7) _ _ sampleKernel instFintypeThreeKernelDiscriminantTest).Δ ^ 3
  let R : sampleKernel := ⟨Q, Or.inr (Or.inl rfl)⟩
  have hR : R.val ≠ 0 := Point.some_ne_zero _
  have hc : A.valuation ((1 : AlgebraicClosure ℚ) ^ 3 - 27 * 7) = 1 := by
    have h := valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7)
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := -188) (by norm_num)
    norm_num at h ⊢
    exact h
  simpa only [map_one, map_ofNat] using
    (@kernelModel_value_of_complement_unit ℚ _ _ 1 7 _ sampleKernel instFintypeThreeKernelDiscriminantTest sampleKernel_card R hR rfl rfl _ _ A.valuation (by simpa using hc))

/-- 実3点核の47上では、核が滑らかで、同じ商の判別式の付値は源の3乗。 -/
theorem sample_47_smooth_and_depth (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    (∀ R : sampleKernel, HasSmoothReduction (localSource A) R.val) ∧
      A.valuation (kernelModel sample sampleKernel).Δ =
        A.valuation (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 3 :=
  ⟨sample_kernel_smooth_at_fortySeven A hA, sample_47_value A hA⟩

/-- 実3点核の7上では、非零核点が特異で、源の判別式の付値は同じ商の3乗。 -/
theorem sample_7_singular_and_depth (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    (∀ R : sampleKernel, R.val ≠ 0 → ¬ HasSmoothReduction (localSource A) R.val) ∧
      A.valuation (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ =
        A.valuation (kernelModel sample sampleKernel).Δ ^ 3 :=
  ⟨sample_kernel_singular_at_seven A hA, sample_7_value A hA⟩

/-- 7上の特異核点と c₄ の単元性から、同じ商の深さの関係を一般定理で直接導く。 -/
theorem sample_7_depth_from_singular_kernel (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 7) :
    A.valuation (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ =
      A.valuation (kernelModel sample sampleKernel).Δ ^ 3 := by
  change A.valuation ((source (1 : ℚ) 7).map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ =
    A.valuation (@kernelModel ℚ _ (source (1 : ℚ) 7) _ _ sampleKernel instFintypeThreeKernelDiscriminantTest).Δ ^ 3
  let R : sampleKernel := ⟨Q, Or.inr (Or.inl rfl)⟩
  have hR : R.val ≠ 0 := Point.some_ne_zero _
  have hc : A.valuation ((sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).c₄) = 1 := by
    have he : (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).c₄ = (-167 : AlgebraicClosure ℚ) := by
      norm_num [sample, WeierstrassCurve.map, c₄, b₂, b₄]
    rw [he]
    simpa only [Int.cast_neg, Int.cast_ofNat] using
      valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7)
        ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := -167) (by norm_num)
  exact @kernelModel_value_of_nonsmooth_origin ℚ _ _ 1 7 _ sampleKernel instFintypeThreeKernelDiscriminantTest
    sampleKernel_card R hR rfl rfl A (localSource A) (localSource_map A)
    (sample_kernel_singular_at_seven A hA R hR) hc

/-- 47上の滑らかな核点から、同じ商の深さの関係を一般定理で直接導く。 -/
theorem sample_47_depth_from_smooth_kernel (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) :
    A.valuation (kernelModel sample sampleKernel).Δ =
      A.valuation (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 3 := by
  change A.valuation (@kernelModel ℚ _ (source (1 : ℚ) 7) _ _ sampleKernel instFintypeThreeKernelDiscriminantTest).Δ =
    A.valuation ((source (1 : ℚ) 7).map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 3
  let R : sampleKernel := ⟨Q, Or.inr (Or.inl rfl)⟩
  have hR : R.val ≠ 0 := Point.some_ne_zero _
  exact @kernelModel_value_of_smooth_origin ℚ _ _ 1 7 _ sampleKernel instFintypeThreeKernelDiscriminantTest
    sampleKernel_card R hR rfl rfl A (localSource A) (localSource_map A)
    (sample_kernel_smooth_at_fortySeven A hA R)

end EllipticThreeKernelDiscriminantTest
