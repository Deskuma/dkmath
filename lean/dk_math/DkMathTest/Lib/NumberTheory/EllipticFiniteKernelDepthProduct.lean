/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDepthProduct
import DkMathTest.Lib.NumberTheory.EllipticThreeKernelDiscriminant

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelDepthProduct"

/-! 実3点核の半核の付値積と、一般の積公式に基づく深さの判定を検査する。 -/
namespace EllipticFiniteKernelDepthProductTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticGoodReductionSeparation EllipticCriticalCentre EllipticTangentDirections
open EllipticFiniteKernelReductionTest EllipticThreeKernelDiscriminantTest
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
noncomputable local instance instDecidableEqDepthProductTest {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
noncomputable local instance instFintypeDepthProductTest : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private theorem three_unit {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 := by
  apply valuation_intCast_eq_one_of_not_dvd A hq ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3)
  intro hd
  exact hq3 ((Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp (by exact_mod_cast hd))

/-- 滑らかな核の47上で、同じ半核の接線分母の平方の積は単元。 -/
theorem sample_47_tangent_product (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    A.valuation (∏ R : halfKernel sample sampleKernel, (2 * R.val.val.yc +
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * R.val.val.xc +
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) = 1 :=
  smooth_half_tangent_product_value_one sample sampleKernel 3 sample_killed A (localSource A) (localSource_map A)
    (three_unit (by decide) (by decide) A hA) (sampleKernel_card ▸ (by decide : Odd 3))
    (sample_kernel_smooth_at_fortySeven A hA)

/-- 特異核の7上で、同じ半核の付値積の3乗は源判別式の値の2乗。 -/
theorem sample_7_tangent_product (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7)
    (C : CriticalCentre A (sample.map (algebraMap ℚ (AlgebraicClosure ℚ)))) (D : TangentDirections C) :
    (∏ R : halfKernel sample sampleKernel, A.valuation (2 * R.val.val.yc +
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * R.val.val.xc +
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) ^ 3 =
      A.valuation (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 2 := by
  simpa using singular_half_tangent_product_value sample sampleKernel 3 sampleKernel_card (by decide)
    sample_killed A (localSource A) (localSource_map A) (three_unit (by decide) (by decide) A hA)
    C D (sample_kernel_singular_at_seven A hA)

/-- 実3点核の半核の接線分母の平方の積は49。番号付けで Q,−Q のどちらを
選んでも、反転で接線分母が符号だけ変わるため同じ値になる。 -/
theorem sample_half_tangent_product :
    (∏ R : halfKernel sample sampleKernel, (2 * R.val.val.yc +
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * R.val.val.xc +
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) = (7 : AlgebraicClosure ℚ) ^ 2 := by
  have ho : Odd (Nat.card sampleKernel) := sampleKernel_card ▸ (by decide : Odd 3)
  have hc := card_halfKernel sample sampleKernel ho
  rw [sampleKernel_card] at hc
  have hs : (halfKernel sample sampleKernel).card = 1 := by omega
  obtain ⟨R, hR⟩ := Finset.card_eq_one.mp hs
  have hr : R ∈ halfKernel sample sampleKernel := by rw [hR]; exact Finset.mem_singleton_self _
  have hn : R.val ≠ 0 := fun he => (mem_halfKernel sample sampleKernel R).mp hr |>.1 <| Subtype.ext he
  have hd : R.val = Q ∨ R.val = -Q := by
    rcases R.property with hz | hq | hq
    · exact (hn hz).elim
    · exact Or.inl hq
    · exact Or.inr hq
  have he := Finset.prod_coe_sort (halfKernel sample sampleKernel) (fun R : sampleKernel =>
    (2 * R.val.yc + (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * R.val.xc +
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2)
  rw [he, hR, Finset.prod_singleton]
  rcases hd with hd | hd
  · simp only [hd]
    norm_num [Q, q0, Point.xc, Point.yc, sample, WeierstrassCurve.map]
  · simp only [hd]
    unfold Q q0
    erw [Point.neg_some]
    norm_num [Point.xc, Point.yc, negY, sample, WeierstrassCurve.map]

/-- 実3点核が、一般定理の入力である同じ商判別式の積公式を満たす。 -/
theorem sample_half_discriminant_product :
    (kernelModel sample sampleKernel).Δ *
      (∏ R : halfKernel sample sampleKernel, (2 * R.val.val.yc +
        (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * R.val.val.xc +
        (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) ^ 4 =
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 3 := by
  rw [sample_half_tangent_product]
  exact sample_product_identity

/-- 実3点核の7上で、一般の特異核深さ定理と実際の積公式をつなぐ。 -/
theorem sample_7_value_via_general_product (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 7) (C : CriticalCentre A (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))))
    (D : TangentDirections C) :
    A.valuation (kernelModel sample sampleKernel).Δ ^ 3 =
      A.valuation (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ :=
  singular_discriminant_value_of_product_identity sample sampleKernel 3 sampleKernel_card (by decide)
    sample_killed A (localSource A) (localSource_map A) (three_unit (by decide) (by decide) A hA)
    C D (sample_kernel_singular_at_seven A hA) sample_half_discriminant_product

/-- 実3点核の47上で、一般の滑らかな核の深さ定理と実際の積公式をつなぐ。 -/
theorem sample_47_value_via_general_product (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 47) :
    A.valuation (kernelModel sample sampleKernel).Δ =
      A.valuation (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ 3 := by
  have hp : (kernelModel sample sampleKernel).Δ *
      (∏ R : halfKernel sample sampleKernel, (2 * R.val.val.yc +
        (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₁ * R.val.val.xc +
        (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).a₃) ^ 2) ^ 4 =
      (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ^ Nat.card sampleKernel := by
    rw [sampleKernel_card]
    exact sample_half_discriminant_product
  simpa only [sampleKernel_card] using
    (smooth_discriminant_value_of_product_identity sample sampleKernel 3 sample_killed
      A (localSource A) (localSource_map A) (three_unit (by decide) (by decide) A hA)
      (sampleKernel_card ▸ (by decide : Odd 3)) (sample_kernel_smooth_at_fortySeven A hA) hp)

end EllipticFiniteKernelDepthProductTest
