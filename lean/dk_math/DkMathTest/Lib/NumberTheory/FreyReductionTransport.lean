/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelReductionSquare
import DkMath.Lib.NumberTheory.WeierstrassIntegerReductionTransport
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelZeroComponent

#print "file: DkMathTest.Lib.NumberTheory.FreyReductionTransport"

/-!
実3点核の7上の還元可換図式と、共通分母2を持つ実曲線の整数化を検査する。
単元条件のない拡大では非整点が整点へ移る反例も残し、仮定の境界を固定する。
-/
namespace FreyReductionTransportTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open WeierstrassVariableChange WeierstrassModelReduction WeierstrassRationalIntegralModel
open EllipticFiniteKernelReductionTest EllipticGoodReductionSeparation EllipticCriticalCentre
open ValuationInertia ValuationPrimeSupport ValuationRationalPrimeSupport
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : sample.IsElliptic := ⟨by norm_num [sample, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]⟩
local instance : Fintype sampleKernel := Fintype.ofFinset {0, Q, -Q} (by
  intro P
  change P ∈ ({0, Q, -Q} : Finset (Points sample)) ↔ P = 0 ∨ P = Q ∨ P = -Q
  simp only [Finset.mem_insert, Finset.mem_singleton])

private theorem nat_unit {q : ℕ} (hq : q.Prime) {r : ℕ} (hr : r.Prime) (hqr : q ≠ r)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (r : AlgebraicClosure ℚ) = 1 := by
  simpa only [Int.cast_natCast] using valuation_intCast_eq_one_of_not_dvd A hq
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := r) (by
      intro h
      exact hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp (by exact_mod_cast h)))

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

/-- 既存の実3点核と同じ剰余モデルで、7上の全零成分について実際の還元が可換。 -/
theorem actual_reduction_square (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7)
    (P : Points sample) (hP : HasSmoothReduction (localSource A) P) :
    pointEquivOfModelEq (sample_singular_branch_residue A hA)
      (modelReduce A _ _ (valuationKernelModel_map sample sampleKernel 3 sample_killed A
        (localSource A) (localSource_map A) (nat_unit (by decide) (by decide) (by decide) A hA)
        (sampleKernel_card ▸ (by decide : Odd 3)))
        (oddKernelPointMap sample sampleKernel (sampleKernel_card ▸ (by decide : Odd 3)) P)) =
      modelReduce A (localSource A) (sample.map (algebraMap ℚ (AlgebraicClosure ℚ))) (localSource_map A) P := by
  obtain ⟨C⟩ := has_centre A hA
  exact oddKernelPointMap_reduction_square sample sampleKernel 3 sample_killed A
    (localSource A) (localSource_map A) _ C _ (sample_kernel_singular_at_seven A hA) P hP

/-- 分母2を持つ曲線y²+y/2=x³。既存の整数化を実際に計算する。 -/
def toy : WeierstrassCurve ℚ := ⟨0, 0, 1 / 2, 0, 0⟩

/-- 同じ共通分母は2、同じ整数標的はy²+4y=x³。倍率を1にしていない。 -/
theorem toy_integer_model : commonDenominator toy = 2 ∧
    integerModel toy = (⟨0, 0, 4, 0, 0⟩ : WeierstrassCurve ℤ) := by
  constructor
  · norm_num [commonDenominator, toy]
  · ext <;> norm_num [integerModel, weightedCoefficient, commonDenominator, toy]

private theorem half_mem (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    (1 / 2 : AlgebraicClosure ℚ) ∈ A := by
  have h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1 :=
    nat_unit (by decide) Nat.prime_two (by decide) A hA
  apply (A.valuation_le_one_iff _).mp
  rw [one_div, map_inv₀, h2, inv_one]

/-- 同じ曲線の7上の整モデル。1/2の整性は住所から供給する。 -/
def localToy (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) : WeierstrassCurve A :=
  ⟨0, 0, ⟨1 / 2, half_mem A hA⟩, 0, 0⟩

/-- 同じ整数化同型を任意の実点で検査する。7上で倍率2が単元であることを使う。 -/
theorem actual_integer_smooth_iff (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7)
    (P : Points (rationalModel toy)) :
    HasSmoothReduction (integerValuationModel A (integerModel toy)) P ↔
      HasSmoothReduction (localToy A hA) (geometricPointEquiv toy P) := by
  apply geometricPointEquiv_smooth_iff
  · ext <;> norm_num [localToy, toy, WeierstrassCurve.map]
  · rw [toy_integer_model.1]
    exact nat_unit (by decide) Nat.prime_two (by decide) A hA

/-- 同じ倍率2の整数化で、非零の実点と滑らかな整数化後の像が実際に存在する。 -/
theorem exists_actual_integer_smooth_point (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 7) :
    ∃ Q : Points (rationalModel toy), Q ≠ 0 ∧
      HasSmoothReduction (integerValuationModel A (integerModel toy)) Q := by
  let h : (toy.toAffine⁄(AlgebraicClosure ℚ)).Nonsingular 0 0 := by
    norm_num [toy, WeierstrassCurve.map, nonsingular_iff', equation_iff']
  let P : Points toy := Point.some 0 0 h
  have hp : HasSmoothReduction (localToy A hA) P := by
    apply (hasSmoothReduction_some_iff (localToy A hA) h).mpr
    intro hx hy
    have h2 : A.valuation (2 : AlgebraicClosure ℚ) = 1 :=
      nat_unit (by decide) Nat.prime_two (by decide) A hA
    have hh : residue A (localToy A hA).a₃ ≠ 0 := by
      apply (WeierstrassResidueModel.residue_ne_zero_iff A _).mpr
      change A.valuation (1 / 2 : AlgebraicClosure ℚ) = 1
      rw [one_div, map_inv₀, h2, inv_one]
    have hzx : (⟨0, hx⟩ : A) = 0 := rfl
    simp only [hzx, map_zero]
    simpa [localToy, WeierstrassCurve.map, nonsingular_iff', equation_iff'] using hh
  let Q := (geometricPointEquiv toy).symm P
  refine ⟨Q, ?_, (actual_integer_smooth_iff A hA Q).mpr ?_⟩
  · intro hz
    have he := congrArg (geometricPointEquiv toy) hz
    rw [AddEquiv.apply_symm_apply, map_zero] at he
    exact Point.some_ne_zero h he
  · simpa only [Q, AddEquiv.apply_symm_apply] using hp

/-- 単元条件を外すと非整点が整になる。2上の1/2にx↦2²xを施す例。 -/
theorem nonunit_scale_boundary (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (2 : AlgebraicClosure ℚ)⁻¹ ∉ A ∧ (2 : AlgebraicClosure ℚ) ^ 2 * 2⁻¹ ∈ A := by
  constructor
  · intro hi
    have h2 := (ValuationSubring.mem_nonunits_iff _).mp hA
    have hm : A.valuation (2 : AlgebraicClosure ℚ) * A.valuation (2 : AlgebraicClosure ℚ)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
    have hl : A.valuation (2 : AlgebraicClosure ℚ) * A.valuation (2 : AlgebraicClosure ℚ)⁻¹ ≤
        A.valuation (2 : AlgebraicClosure ℚ) :=
      mul_le_of_le_one_right' ((A.valuation_le_one_iff _).mpr hi)
    rw [hm] at hl
    exact h2.not_ge hl
  · norm_num

end
end FreyReductionTransportTest
