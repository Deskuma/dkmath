/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNonresonantInertia
import DkMath.FLT.FreyCyclicTowerCharacter
import DkMath.Lib.NumberTheory.CyclotomicFrobeniusAll

#print "file: DkMath.FLT.FreySmoothStageAbsorption"

/-!
# 同じ巡回段の滑らかな配置から狭い吸収を導く

共鳴・非共鳴に依存しない配置判定。配置そのものは明示入力であり、
Cofixed 条件から全ての段が滑らかだとは結論しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticGoodReductionSeparation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 同じ段が部分群に入ることは、その実際の座標生成元の所属だけで判定できる。 -/
theorem ResidualCyclicStage.le_iff_generator_mem (T : S.ResidualCyclicStage L n)
    (H : AddSubgroup (Points S.rationalCurve)) :
    T.carrier ≤ H ↔ (T.coordinates 1).val ∈ H := by
  constructor
  · intro h
    exact h (T.coordinates 1).property
  · intro h x hx
    let z : T.carrier := ⟨x, hx⟩
    have he : ((T.coordinates.symm z).val) • T.coordinates 1 = z := by
      rw [← map_nsmul]
      simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, AddEquiv.apply_symm_apply]
    have hv := congrArg T.carrier.subtype he
    rw [map_nsmul] at hv
    change ((T.coordinates.symm z).val) • (T.coordinates 1).val = x at hv
    rw [← hv]
    exact H.nsmul_mem h _

/-- 滑らかな同じ巡回段は、同じ次数の滑らかな捩れ全体に一致する。 -/
theorem ResidualCyclicStage.eq_smooth_torsion_of_le (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hsm : T.carrier ≤ S.valuationSmoothSubgroup A) :
    T.carrier = AbsorbingTorsionFiltration.stage p (n + 1) (S.valuationSmoothSubgroup A) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, ⟨D⟩⟩ := S.exists_geometry_at_bad_address hp5 haddr A hA
  have hle : T.carrier ≤ AbsorbingTorsionFiltration.stage p (n + 1) (S.valuationSmoothSubgroup A) :=
    fun x hx => ⟨T.killed x hx, hsm hx⟩
  have hbound : Nat.card (AbsorbingTorsionFiltration.stage p (n + 1) (S.valuationSmoothSubgroup A)) ≤ p ^ (n + 1) := by
    apply EllipticNodalTorsionBound.card_le_of_injective_smooth_torsion (S.valuationModel A)
      _ (S.valuationModel_map A) C D (pow_pos (Fact.out : p.Prime).pos _)
      (CyclotomicFrobenius.prime_power_valuation_eq_one hq hqp A hA n) Subtype.val Subtype.val_injective
    · intro y
      exact (S.mem_valuationSmoothSubgroup_iff A y.val).mp y.property.2
    · intro y
      exact y.property.1
  let : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
  let : Finite (TorsionMultiplication.Kernel (Points S.rationalCurve) (p ^ (n + 1))) :=
    finite_torsion_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let : Finite (AbsorbingTorsionFiltration.stage p (n + 1) (S.valuationSmoothSubgroup A)) :=
    AbsorbingTorsionFiltration.finiteStage p (n + 1) (S.valuationSmoothSubgroup A)
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe, T.card]
  exact hbound

/-- 滑らかな配置なら、p•y∈T を保ったまま狭い慣性吸収が成立する。 -/
theorem ResidualCyclicStage.preimage_absorbs_of_smooth (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hsm : T.carrier ≤ S.valuationSmoothSubgroup A)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p • y ∈ T.carrier) :
    pointAction S.rationalCurve τ y - y ∈ T.carrier := by
  have hyt : p ^ (n + 1 + 1) • y = 0 := by
    rw [pow_succ, mul_nsmul']
    exact T.killed _ hy
  have htop : p ^ (n + 1) • y ∈ T.carrier := by
    rw [pow_succ, mul_nsmul']
    exact T.carrier.nsmul_mem hy _
  have hptop : p • (p ^ (n + 1) • y) = 0 := by rwa [← mul_nsmul', ← pow_succ']
  have hs : HasSmoothReduction (S.valuationModel A) (p ^ (n + 1) • y) :=
    (S.mem_valuationSmoothSubgroup_iff A _).mp (hsm htop)
  have hf : pointAction S.rationalCurve τ (p ^ (n + 1) • y) = p ^ (n + 1) • y :=
    congrArg Subtype.val (S.residual_fixed_of_smooth_reduction hq hqp A hA τ hτ
      (⟨p ^ (n + 1) • y, hptop⟩ : S.ResidualSpace) hs)
  rw [T.eq_smooth_torsion_of_le hp5 hq hqp haddr A hA hsm]
  refine ⟨?_, (S.mem_valuationSmoothSubgroup_iff A _).mpr
    (S.inertia_difference_smooth_at_bad_address hp5 hq haddr A hA τ hτ y)⟩
  change p ^ (n + 1) • (pointAction S.rationalCurve τ y - y) = 0
  rw [nsmul_sub, ← map_nsmul, hf, sub_self]

end
end DkMath.FLT.Frey.Source
