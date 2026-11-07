/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWildInertia
import DkMath.Lib.NumberTheory.ValuationWildNormality

#print "file: DkMath.FLT.FreyTameInertiaQuotient"

/-!
# 同じ野生合同部分群による実際の馴分岐商と連続差分準同型

元の慣性群を正規な野生合同部分群で割る。商の有限性は主張しない。
元の有限像と厳密位数を持つ値を保ち、Frobenius 共役冪関係を商元自体で証明する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation ValuationInertia ValuationWildRigidity
noncomputable section

/-- 同じ全非零元の野生合同部分群は、元の慣性群の中で正規。 -/
instance wildInertiaSubgroup_normal (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (wildInertiaSubgroup A).Normal := inertiaWild_normal A

/-- 今回の明示的な野生合同部分群による、元の慣性群の実際の商。 -/
abbrev tameInertiaQuotient (A : ValuationSubring (AlgebraicClosure ℚ)) :=
  (inertiaSubgroupIn A ℚ) ⧸ wildInertiaSubgroup A

variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 元の同じ差分準同型を、実際の馴分岐商へ降ろす。 -/
def ResidualCyclicStage.tameDifferenceCharacter
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    tameInertiaQuotient A →* Multiplicative T.upperQuotient :=
  QuotientGroup.lift (wildInertiaSubgroup A)
    (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x)
    (T.wildInertia_le_character_kernel hp5 hq hqp haddr A hA x)

/-- 同じ慣性元の像での値は、元の同じ商値と等しい。 -/
theorem ResidualCyclicStage.tameDifferenceCharacter_mk
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    T.tameDifferenceCharacter hp5 hq hqp haddr A hA x (QuotientGroup.mk σ) =
      T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ := rfl

/-- 元の Krull 部分群位相・標準商位相で、降下した同じ準同型は連続。 -/
theorem ResidualCyclicStage.tameDifferenceCharacter_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (T.tameDifferenceCharacter hp5 hq hqp haddr A hA x) := by
  apply continuous_quot_lift
  exact T.inertiaQuotientDifferenceCharacter_continuous hp5 hq hqp haddr A hA x

/-- 降下は同じ準同型の像を保つ。商群全体が有限であるとは結論しない。 -/
theorem ResidualCyclicStage.tameDifferenceCharacter_range
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    (T.tameDifferenceCharacter hp5 hq hqp haddr A hA x).range =
      (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x).range := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨σ, hw⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨QuotientGroup.mk σ, hσ⟩

end

/-- 実際の Frobenius 共役は、同じ馴分岐商の元自体で q 乗となる。 -/
theorem tameInertia_frobenius_power {q : ℕ}
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ q) (τ : inertiaSubgroupIn A ℚ) :
    ∃ hconj : φ * τ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
      (QuotientGroup.mk ⟨φ * τ.val * φ⁻¹, hconj⟩ : tameInertiaQuotient A) =
        (QuotientGroup.mk τ) ^ q := by
  obtain ⟨he, hw⟩ := frobenius_conjugate_error_wild A hφ τ.property
  have hc : φ * τ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ := by
    have hh := (inertiaSubgroupIn A ℚ).mul_mem he ((inertiaSubgroupIn A ℚ).pow_mem τ.property q)
    simpa only [inv_mul_cancel_right] using hh
  refine ⟨hc, ?_⟩
  let e : inertiaSubgroupIn A ℚ := ⟨φ * τ.val * φ⁻¹ * (τ.val ^ q)⁻¹, he⟩
  have hew : e ∈ wildInertiaSubgroup A := (isWildAt_iff A).mpr hw
  have hk : (QuotientGroup.mk e : tameInertiaQuotient A) = 1 := (QuotientGroup.eq_one_iff e).mpr hew
  have heq : e = (⟨φ * τ.val * φ⁻¹, hc⟩ : inertiaSubgroupIn A ℚ) * (τ ^ q)⁻¹ := rfl
  change (QuotientGroup.mk' (wildInertiaSubgroup A)) e = 1 at hk
  rw [heq, map_mul, map_inv, map_pow] at hk
  exact eq_of_mul_inv_eq_one hk

end DkMath.FLT.Frey.Source
