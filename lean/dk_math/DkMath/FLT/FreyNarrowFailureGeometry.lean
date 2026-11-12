/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreySmoothStageAbsorption

#print "file: DkMath.FLT.FreyNarrowFailureGeometry"

/-!
# 狭い吸収失敗点の同じ局所幾何

p•y∈T と τy−y∉T を保持する。差は滑らかな捩れ点であり慣性固定だが、
元の段の生成元は特異な剰余円板へ落ちる。類群消滅はこの局所解析には不要。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticGoodReductionSeparation ValuationInertia
open EllipticCriticalCentre EllipticTangentDirections
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 失敗点と差点の次数上界、差点の滑らかさ・全慣性固定性、p倍の元の段への所属。 -/
theorem ResidualCyclicStage.narrow_failure_profile (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p • y ∈ T.carrier)
    (hfail : pointAction S.rationalCurve τ y - y ∉ T.carrier) :
    p ^ (n + 1 + 1) • y = 0 ∧
    p ^ (n + 1 + 1) • (pointAction S.rationalCurve τ y - y) = 0 ∧
    HasSmoothReduction (S.valuationModel A) (pointAction S.rationalCurve τ y - y) ∧
    (∀ σ ∈ inertiaSubgroupIn A ℚ, pointAction S.rationalCurve σ
      (pointAction S.rationalCurve τ y - y) = pointAction S.rationalCurve τ y - y) ∧
    p • (pointAction S.rationalCurve τ y - y) ∈ T.carrier ∧
    pointAction S.rationalCurve τ y - y ≠ 0 := by
  have hk : p ^ (n + 1 + 1) • y = 0 := by
    rw [pow_succ, mul_nsmul']
    exact T.killed _ hy
  have hd : p ^ (n + 1 + 1) • (pointAction S.rationalCurve τ y - y) = 0 := by
    rw [nsmul_sub, ← map_nsmul, hk, map_zero, sub_self]
  have hs := S.inertia_difference_smooth_at_bad_address hp5 hq haddr A hA τ hτ y
  refine ⟨hk, hd, hs, ?_, ?_, ?_⟩
  · intro σ hσ
    exact congrArg Subtype.val
      (EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction S.rationalCurve _ A
        (S.valuationModel A) (S.valuationModel_map A)
        (CyclotomicFrobenius.prime_power_valuation_eq_one hq hqp A hA (n + 1)) σ hσ
        ⟨pointAction S.rationalCurve τ y - y, hd⟩ hs)
  · rw [nsmul_sub, ← map_nsmul]
    exact T.carrier.sub_mem (T.stable τ _ hy) hy
  · intro he
    exact hfail (he ▸ T.carrier.zero_mem)

/-- 狭い吸収が失敗した同じ段の座標生成元は、滑らかに還元しない。 -/
theorem ResidualCyclicStage.generator_not_smooth_of_narrow_failure (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p • y ∈ T.carrier)
    (hfail : pointAction S.rationalCurve τ y - y ∉ T.carrier) :
    ¬ HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val := by
  intro hs
  have hsm := (T.le_iff_generator_mem (S.valuationSmoothSubgroup A)).mpr
    ((S.mem_valuationSmoothSubgroup_iff A _).mpr hs)
  exact hfail (T.preimage_absorbs_of_smooth hp5 hq hqp haddr A hA hsm τ hτ hy)

/-- 同じ非滑らかな生成元を、同じ臨界中心に対する実際の座標と付値不等式で記述する。 -/
theorem ResidualCyclicStage.exists_generator_depth_of_narrow_failure (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p • y ∈ T.carrier)
    (hfail : pointAction S.rationalCurve τ y - y ∉ T.carrier) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      Nonempty (TangentDirections C) ∧
      ∃ x z : AlgebraicClosure ℚ,
      ∃ h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x z,
        (T.coordinates 1).val = WeierstrassCurve.Affine.Point.some x z h ∧ A.valuation (x - C.x) < 1 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, hD⟩ := S.exists_geometry_at_bad_address hp5 haddr A hA
  refine ⟨C, hD, ?_⟩
  have hg := T.generator_not_smooth_of_narrow_failure hp5 hq hqp haddr A hA τ hτ hy hfail
  generalize he : (T.coordinates 1).val = P at hg ⊢
  cases P with
  | zero => exact (hg (hasSmoothReduction_zero (S.valuationModel A) _)).elim
  | some x z h =>
    exact ⟨x, z, h, rfl, (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model
      (S.valuationModel A) _ (S.valuationModel_map A) C h).mp hg⟩

end
end DkMath.FLT.Frey.Source
