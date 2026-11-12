/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelZeroComponent
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelZeroComponent"

/-!
既存の実3点核O,(0,0),(0,−7)を持つy²+xy+7y=x³を再利用する。
7上の特異核側で、中心の存在を内部供給し、全ての滑らかな実点の像を検査する。
x=1の非零実点も代数閉包で実際に構成し、この族がOだけでないことを確認する。
-/
namespace EllipticFiniteKernelZeroComponentTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelReductionTest EllipticGoodReductionSeparation EllipticCriticalCentre
open EllipticNodalReduction ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩

local instance : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])
local instance : (sample.toAffine⁄(AlgebraicClosure ℚ)).IsElliptic := ⟨by
  norm_num [sample, WeierstrassCurve.map, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩

private theorem three_unit (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    A.valuation (3 : AlgebraicClosure ℚ) = 1 := by
  exact valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7)
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := 3) (by norm_num)

private theorem has_centre (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    Nonempty (CriticalCentre A (sample.map (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
  let W := sample.map (algebraMap ℚ (AlgebraicClosure ℚ))
  have hd : W.Δ = (-64484 : AlgebraicClosure ℚ) := by
    norm_num [W, sample, WeierstrassCurve.map, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  have hc : W.c₄ = (-167 : AlgebraicClosure ℚ) := by
    norm_num [W, sample, WeierstrassCurve.map, c₄, b₂, b₄]
  have hv := (ValuationSubring.mem_nonunits_iff _).mp hA
  apply exists_criticalCentre A W
  · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₁]
    exact (localSource A).a₁.property
  · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₂]
    exact (localSource A).a₂.property
  · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₃]
    exact (localSource A).a₃.property
  · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₄]
    exact (localSource A).a₄.property
  · rw [show W = (localSource A).map A.subtype from (localSource_map A).symm, map_a₆]
    exact (localSource A).a₆.property
  · rw [hd]; norm_num
  · rw [hd]
    simpa only [Int.cast_neg, Int.cast_ofNat] using
      valuation_intCast_lt_one_of_dvd A hv (z := -64484) (by norm_num)
  · rw [hc]
    simpa only [Int.cast_neg, Int.cast_ofNat] using
      valuation_intCast_eq_one_of_not_dvd A (by decide : Nat.Prime 7) hv (z := -167) (by norm_num)

/-- 実際の3点核の同じ標的で、7上の全零成分の像の滑らかさを確認する。 -/
theorem actual_all_smooth_points (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7)
    (P : Points sample) (hP : HasSmoothReduction (localSource A) P) :
    HasSmoothReduction
      (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A) (localSource_map A)
        (three_unit A hA))
      (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) := by
  obtain ⟨C⟩ := has_centre A hA
  exact oddKernelPointMap_smooth_of_not_smooth_kernel sample sampleKernel A (localSource A)
    (localSource_map A) C 3 sample_killed (three_unit A hA) _ (sample_kernel_singular_at_seven A hA) P hP

private theorem exists_point_x (x : AlgebraicClosure ℚ) : ∃ P : Points sample, P.xc = x := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq ((x + 7) ^ 2 + 4 * x ^ 3) (by decide : 0 < 2)
  have he : (sample.toAffine⁄(AlgebraicClosure ℚ)).Equation x ((z - x - 7) / 2) := by
    rw [equation_iff]
    norm_num [sample, WeierstrassCurve.map]
    linear_combination hz / 4
  exact ⟨Point.some x ((z - x - 7) / 2) (equation_iff_nonsingular.mp he), rfl⟩

/-- x=1の非零実点を実際に構成する。y=√17−4で同じ源方程式を満たす。 -/
theorem exists_nonzero_point_x_one : ∃ P : Points sample, P ≠ 0 ∧ P.xc = 1 := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (17 : AlgebraicClosure ℚ) (by decide : 0 < 2)
  have he : (sample.toAffine⁄(AlgebraicClosure ℚ)).Equation 1 (z - 4) := by
    rw [equation_iff]
    norm_num [sample, WeierstrassCurve.map]
    linear_combination hz
  exact ⟨Point.some 1 (z - 4) (equation_iff_nonsingular.mp he), Point.some_ne_zero _, rfl⟩

/-- x=1の同じ実点は7上で滑らか。有限点の剰余非特異性も直接確認する。 -/
theorem smooth_at_seven_of_x_one (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7)
    (P : Points sample) (hx : P.xc = 1) : HasSmoothReduction (localSource A) P := by
  have hP : P ≠ 0 := by intro he; rw [he] at hx; exact zero_ne_one hx
  rw [Point.eq_some_xc_yc hP, hasSmoothReduction_some_iff]
  intro hxi hyi
  have h7 : (7 : ResidueField A) = 0 := by
    have h := (WeierstrassResidueModel.residue_zero_iff A (7 : A)).mpr
      ((ValuationSubring.mem_nonunits_iff _).mp hA)
    simpa only [map_ofNat] using h
  have hxres : residue A ⟨P.xc,hxi⟩ = 1 := by
    have he : (⟨P.xc,hxi⟩ : A) = 1 := Subtype.ext hx
    rw [he, map_one]
  have he := equation_residue (localSource A) (x := ⟨P.xc,hxi⟩) (y := ⟨P.yc,hyi⟩)
    ((localSource_map A).symm ▸ (Point.nonsingular_xc_yc hP).1)
  apply nonsingular_of_node_of_x_ne ((localSource A).map (residue A)) 0 0
  · norm_num [localSource, WeierstrassCurve.map, equation_iff', map_ofNat, h7]
  · norm_num [localSource, WeierstrassCurve.map, nonsingular_iff', equation_iff', map_ofNat, h7]
    exact h7
  · norm_num [localSource, WeierstrassCurve.map, b₂]
  · exact he
  · rw [hxres]; exact one_ne_zero

/-- Oだけに依らない、同じ零成分と同じ像の非空な例。 -/
theorem exists_actual_smooth_image (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    ∃ P : Points sample, P ≠ 0 ∧ HasSmoothReduction (localSource A) P ∧
      HasSmoothReduction
        (valuationKernelModel sample sampleKernel 3 sample_killed A (localSource A) (localSource_map A)
          (three_unit A hA))
        (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P) := by
  obtain ⟨P,hP,hx⟩ := exists_nonzero_point_x_one
  have hs := smooth_at_seven_of_x_one A hA P hx
  exact ⟨P,hP,hs,actual_all_smooth_points A hA P hs⟩

/-- 無限遠近傍では、実際の3点核による特殊化値の付値が正確に保存される。 -/
theorem actual_formal_value (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7)
    (P : Points sample) (hx : P.xc ∉ A) :
    A.valuation (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P).xc =
      A.valuation P.xc := by
  let ho : Odd (Nat.card sampleKernel) := sampleKernel_card ▸ (by decide : Odd 3)
  let := kernelModel_isElliptic_of_odd_card sample sampleKernel ho
  have hp := not_mem_kernel_of_x_not_mem sample sampleKernel 3 sample_killed A
    (localSource A) (localSource_map A) (three_unit A hA) P hx
  rw [show oddKernelPointMap sample sampleKernel ho P = Point.some _ _ (kernelAt_nonsingular sample sampleKernel P hp)
    from kernelPointMap_of_not_mem sample sampleKernel P hp, Point.xc_some]
  exact kernelXAt_value_of_x_not_mem sample sampleKernel 3 sample_killed A
    (localSource A) (localSource_map A) (three_unit A hA) ho P hx

/-- 無限遠近傍にも実際の非零点が存在し、同じ商写像がその近傍を保つ。 -/
theorem exists_actual_formal_image (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    ∃ P : Points sample, P.xc ∉ A ∧
      (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P).xc ∉ A := by
  obtain ⟨P,hP⟩ := exists_point_x (7 : AlgebraicClosure ℚ)⁻¹
  have hx : P.xc ∉ A := by
    rw [hP]
    intro hi
    have h7 := (ValuationSubring.mem_nonunits_iff _).mp hA
    have hm : A.valuation (7 : AlgebraicClosure ℚ) * A.valuation (7 : AlgebraicClosure ℚ)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
    have hl : A.valuation (7 : AlgebraicClosure ℚ) * A.valuation (7 : AlgebraicClosure ℚ)⁻¹ ≤
        A.valuation (7 : AlgebraicClosure ℚ) :=
      mul_le_of_le_one_right' ((A.valuation_le_one_iff _).mpr hi)
    rw [hm] at hl
    exact h7.not_ge hl
  exact ⟨P,hx,oddKernelPointMap_x_not_mem sample sampleKernel 3 sample_killed A
    (localSource A) (localSource_map A) (three_unit A hA) _ P hx⟩

end
end EllipticFiniteKernelZeroComponentTest
