/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelCollision
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelCollision"

/-! 実3点核を持つy²+xy+7y=x³の47上で、核外の実点P=Q+Rを構成する。
x(R)=1/47なのでRは無限遠へ還元し、PとQの還元は一致する。
有限座標の分母が衝突するこのPの同じ商像が、実際にOへ還元することを検査する。 -/
namespace EllipticFiniteKernelCollisionTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelReductionTest EllipticGoodReductionSeparation WeierstrassModelReduction
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
local instance : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])

private theorem three_unit (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 :=
  valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 47)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)

/-- 47上の同じ実3点核と衝突する全滑らかな点について、同じ像の滑らかさと還元を検査。 -/
theorem actual_collision_image (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47)
    (P : Points sample) (hP : HasSmoothReduction (localSource A) P)
    (hr : modelReduce A (localSource A) _ (localSource_map A) P =
      modelReduce A (localSource A) _ (localSource_map A) Q) :
    HasSmoothReduction
        (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A) (localSource_map A)
          (three_unit A hA))
        (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) ∧
      modelReduce A _ _ (valuationKernelModel_map sample sampleKernel 3 sample_killed A
        (localSource A) (localSource_map A) (three_unit A hA)
        (sampleKernel_card ▸ (by decide : Odd 3)))
        (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) = 0 :=
  oddKernelPointMap_of_reduction_collision sample sampleKernel 3 sample_killed A
    (localSource A) (localSource_map A) (three_unit A hA) _ P ⟨Q, Or.inr (Or.inl rfl)⟩ hP
    (sample_kernel_smooth_at_fortySeven A hA _) hr

/-- 核外でも衝突は起こる。実際のP=Q+Rを構成し、P≠Qを核外性から保証する。 -/
theorem exists_actual_collision_outside_kernel
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    ∃ P : Points sample, P ∉ sampleKernel ∧ HasSmoothReduction (localSource A) P ∧
      modelReduce A (localSource A) _ (localSource_map A) P =
        modelReduce A (localSource A) _ (localSource_map A) Q := by
  let x : AlgebraicClosure ℚ := (47 : AlgebraicClosure ℚ)⁻¹
  have hx : x ∉ A := by
    intro hi
    have hv := (ValuationSubring.mem_nonunits_iff _).mp hA
    have hm : A.valuation (47 : AlgebraicClosure ℚ) * A.valuation x = 1 := by
      rw [← map_mul, show (47 : AlgebraicClosure ℚ) * x = 1 from mul_inv_cancel₀ (by norm_num), map_one]
    have hl := mul_le_of_le_one_right' (a := A.valuation (47 : AlgebraicClosure ℚ))
      ((A.valuation_le_one_iff _).mpr hi)
    rw [hm] at hl
    exact hv.not_ge hl
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((x + 7) ^ 2 + 4 * x ^ 3) (by decide : 0 < 2)
  have he : (sample.toAffine⁄(AlgebraicClosure ℚ)).Equation x ((z - x - 7) / 2) := by
    rw [equation_iff]
    norm_num [sample, WeierstrassCurve.map]
    linear_combination hz / 4
  let : (sample.toAffine⁄(AlgebraicClosure ℚ)).IsElliptic := ⟨by
    norm_num [sample, WeierstrassCurve.map, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
  let R : Points sample := Point.some x ((z - x - 7) / 2) (equation_iff_nonsingular.mp he)
  have hR : HasSmoothReduction (localSource A) R := hasSmoothReduction_of_notMem _ _ hx
  have hrR : modelReduce A (localSource A) _ (localSource_map A) R = 0 :=
    modelReduce_some_not_mem _ _ _ _ _ hx
  have hQ := sample_kernel_smooth_at_fortySeven A hA (⟨Q, Or.inr (Or.inl rfl)⟩ : sampleKernel)
  have hQR := smooth_add_of_model A (localSource A) _ (localSource_map A) hQ hR
  have hred : modelReduce A (localSource A) _ (localSource_map A) (Q + R) =
      modelReduce A (localSource A) _ (localSource_map A) Q :=
    (modelReduce_add A (localSource A) _ (localSource_map A) hQ hR).trans (by rw [hrR, add_zero])
  refine ⟨Q + R, ?_, hQR, hred⟩
  intro hm
  have hmR : R ∈ sampleKernel := by
    simpa only [add_sub_cancel_left] using sampleKernel.sub_mem hm (Or.inr (Or.inl rfl))
  exact not_mem_kernel_of_x_not_mem sample sampleKernel 3 sample_killed A (localSource A)
    (localSource_map A) (three_unit A hA) R hx hmR

/-- 核外の衝突点でも、同じ商像の実際の還元はOとなる。 -/
theorem exists_actual_collision_image
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 47) :
    ∃ P : Points sample, P ∉ sampleKernel ∧
      HasSmoothReduction
        (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A) (localSource_map A)
          (three_unit A hA))
        (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) ∧
      modelReduce A _ _ (valuationKernelModel_map sample sampleKernel 3 sample_killed A
        (localSource A) (localSource_map A) (three_unit A hA)
        (sampleKernel_card ▸ (by decide : Odd 3)))
        (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) = 0 := by
  obtain ⟨P, hn, hs, hr⟩ := exists_actual_collision_outside_kernel A hA
  exact ⟨P, hn, actual_collision_image A hA P hs hr⟩

end
end EllipticFiniteKernelCollisionTest
