/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Frobenius error calculation adapted through DkMath ValuationTameCharacter from
S_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime.lean.
Modified: retain IsFrobeniusAt, actual Frey wild-kernel elimination, SAME character.
-/

import DkMath.FLT.FreyInertiaCharacterFiniteImage
import DkMath.Lib.NumberTheory.EllipticWildRigidity
import DkMath.Lib.NumberTheory.ValuationTameCharacter
import DkMath.Lib.RepresentationTheory.UnipotentDifferencePower

#print "file: DkMath.FLT.FreyWildInertia"

/-!
# Frey の実際の野生慣性消滅と差分値の Frobenius 共役公式

q≠p の同じ悪い住所で、野生合同と既存の節点積零性を結ぶ。
野生元の作用は有限 p 冪捩れ全体で自明。Frobenius 共役の野生誤差を実際に消す。
共役先は通常の慣性差分準同型で評価する。Galois 加群値の輸送や基点不変性とは区別する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia ValuationWildRigidity
open ValuationTameCharacter.TameCharacter
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 同じ全自己同型群の野生合同部分群を、元の慣性部分群へ引き戻す。 -/
def wildInertiaSubgroup (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Subgroup (inertiaSubgroupIn A ℚ) :=
  (wildSubgroup (K := ℚ) A).comap (inertiaSubgroupIn A ℚ).subtype

section Local
variable (n : ℕ) (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ野生慣性元は、実際の有限 p 冪捩れ群の全点を固定する。 -/
theorem prime_power_wild_inertia_fixed (σ : inertiaSubgroupIn A ℚ)
    (hwild : σ ∈ wildInertiaSubgroup A)
    (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    representation S.rationalCurve (p ^ (n + 1)) σ.val x = x := by
  let ρ := (representation S.rationalCurve (p ^ (n + 1))).comp (inertiaSubgroupIn A ℚ).subtype
  have hx : p ^ (n + 1) • x = 0 := by
    apply Subtype.ext
    exact x.property
  have hperiod := UnipotentDifferenceCharacter.fixed_by_pow_of_killed ρ
    (S.prime_power_inertia_difference_product_zero n hp5 hq hqp haddr A hA) σ x hx
  exact representation_fixed_of_wild_coprime_period S.rationalCurve A hq hA σ.val
    ((isWildAt_iff A).mp hwild)
    (((Nat.coprime_primes (Fact.out : p.Prime) hq).mpr hqp.symm).pow_left (n + 1)) x hperiod

end Local

/-- 同じ実際の Frobenius の共役冪誤差は、慣性に属し野生合同を満たす。 -/
theorem frobenius_conjugate_error_wild {q : ℕ}
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {φ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ q) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ inertiaSubgroupIn A ℚ ∧
      ∀ z : AlgebraicClosure ℚ, z ≠ 0 →
        (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹ - 1 ∈ A.nonunits := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  have hφD : φ ∈ A.decompositionSubgroup ℚ := hφ.mem_decompositionSubgroup
  have hτD : τ ∈ A.decompositionSubgroup ℚ := (mem_inertiaSubgroupIn_iff.mp hτ).1
  have hconj : φ * τ * φ⁻¹ ∈ inertiaSubgroupIn A ℚ := conj_mem_inertiaSubgroupIn hτ hφD
  have hpow : τ ^ q ∈ inertiaSubgroupIn A ℚ := Subgroup.pow_mem _ hτ q
  have hω : φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ inertiaSubgroupIn A ℚ :=
    Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hpow)
  refine ⟨hω, fun z hz => ?_⟩
  have hτqD : τ ^ q ∈ A.decompositionSubgroup ℚ := Subgroup.pow_mem _ hτD q
  have hτqiD : (τ ^ q)⁻¹ ∈ A.decompositionSubgroup ℚ := (A.decompositionSubgroup ℚ).inv_mem hτqD
  have hωD : φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ A.decompositionSubgroup ℚ :=
    (mem_inertiaSubgroupIn_iff.mp hω).1
  have h1 := theta_mul hconj hτqiD hz
  have h2 := theta_mul_theta_inv hpow hz
  rw [theta_pow hτ hz q] at h2
  have h3 := theta_frob_conj hφ hτ hz
  have hθω : rq A ((φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹) = 1 := by
    rw [h1, h3, h2]
  rw [← rq_one (A := A), rq_eq_rq_iff (apply_mul_inv_mem hωD hz).1 A.one_mem] at hθω
  exact hθω

section Stage
variable {S} {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ実際の差分準同型の核は、同じ野生慣性部分群を含む。 -/
theorem ResidualCyclicStage.wildInertia_le_character_kernel
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    wildInertiaSubgroup A ≤ (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x).ker := by
  intro σ hσ
  change Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ) = 0
  rw [T.inertiaQuotientDifferenceCharacter_apply hp5 hq hqp haddr A hA x σ,
    S.prime_power_wild_inertia_fixed (n + 1) hp5 hq hqp haddr A hA σ hσ x, sub_self, map_zero]

/-- 構成した同じ Frobenius 共役を、同じ固定基点の通常の慣性準同型で評価する。
野生誤差が核に入るため q 倍公式を得る。商作用による輸送公式は主張しない。 -/
theorem ResidualCyclicStage.exists_frobenius_character_power
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    ∃ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ValuationFrobenius.IsFrobeniusAt A φ q ∧ ∀ τ : inertiaSubgroupIn A ℚ,
      ∃ hconj : φ * τ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
        T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x
          ⟨φ * τ.val * φ⁻¹, hconj⟩ =
        (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x τ) ^ q := by
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime hq A hA
  refine ⟨φ, hφ, fun τ => ?_⟩
  obtain ⟨he, hw⟩ := frobenius_conjugate_error_wild A hφ τ.property
  have hc : φ * τ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ := by
    have hh := (inertiaSubgroupIn A ℚ).mul_mem he ((inertiaSubgroupIn A ℚ).pow_mem τ.property q)
    simpa only [inv_mul_cancel_right] using hh
  refine ⟨hc, ?_⟩
  let c := T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x
  let e : inertiaSubgroupIn A ℚ := ⟨φ * τ.val * φ⁻¹ * (τ.val ^ q)⁻¹, he⟩
  have hew : e ∈ wildInertiaSubgroup A := (isWildAt_iff A).mpr hw
  have hk : c e = 1 := T.wildInertia_le_character_kernel hp5 hq hqp haddr A hA x hew
  have heq : e = (⟨φ * τ.val * φ⁻¹, hc⟩ : inertiaSubgroupIn A ℚ) * (τ ^ q)⁻¹ := rfl
  rw [heq, map_mul, map_inv, map_pow] at hk
  exact eq_of_mul_inv_eq_one hk

end Stage
end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 同じ hclass と Cofixed 候補から、野生慣性を消す非自明な同じ差分準同型と共役冪公式を得る。 -/
theorem residual_exists_tame_inertia_character
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      c ⟨τ, h.inertia⟩ ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c ⟨τ, h.inertia⟩)) = p ∧
      wildInertiaSubgroup A ≤ c.ker ∧
      ∃ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ValuationFrobenius.IsFrobeniusAt A φ q ∧ ∀ γ : inertiaSubgroupIn A ℚ,
        ∃ hconj : φ * γ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
          c ⟨φ * γ.val * φ⁻¹, hconj⟩ = (c γ) ^ q := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  refine ⟨n, T, q, A, τ, y, h, (h.inertia_character_nontrivial hp5).1,
    (h.inertia_character_nontrivial hp5).2, ?_, ?_⟩
  · exact T.wildInertia_le_character_kernel hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  · exact T.exists_frobenius_character_power hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩

end
end DkMath.FLT.Frey.Source
