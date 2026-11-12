/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTameInertiaQuotient
import DkMath.Lib.Algebra.PrimeOrderResonance

#print "file: DkMath.FLT.FreyTameResonance"

/-!
# 同じ馴分岐商の非自明な値と共鳴二分岐

位数が正確に p の同じ値について、Frobenius 共役先の値が元と等しいことは
q=1 mod p と同値。q=-1 mod p では逆元へ動くが、それ自体を矛盾とはしない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.Algebra.PrimeOrderResonance
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}
    {T : S.ResidualCyclicStage L n} {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {y : Points S.rationalCurve}

/-- 同じ障害点の値は、実際の馴分岐商へ降ろしても非自明・厳密位数 p。 -/
theorem NarrowAbsorptionObstruction.tame_character_nontrivial
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let c := T.tameDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
    let t : tameInertiaQuotient A := QuotientGroup.mk ⟨τ, h.inertia⟩
    c t ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c t)) = p :=
  h.inertia_character_nontrivial hp5

/-- 同じ実際の Frobenius と同じ商元で、固定・反転・非不変性を正確に分類する。 -/
theorem NarrowAbsorptionObstruction.tame_resonant_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let c := T.tameDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
    let t : tameInertiaQuotient A := QuotientGroup.mk ⟨τ, h.inertia⟩
    Continuous c ∧ c t ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c t)) = p ∧
    ∃ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ValuationFrobenius.IsFrobeniusAt A φ q ∧
      ∃ hconj : φ * τ * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
      let t' : tameInertiaQuotient A := QuotientGroup.mk ⟨φ * τ * φ⁻¹, hconj⟩
      t' = t ^ q ∧ (c t' = c t ↔ (q : ZMod p) = 1) ∧
        ((q : ZMod p) = -1 → c t' = (c t)⁻¹ ∧ c t' ≠ c t) ∧
        (((q : ZMod p) = 1 ∧ c t' = c t) ∨
          ((q : ZMod p) = -1 ∧ c t' = (c t)⁻¹ ∧ c t' ≠ c t)) := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  let c := T.tameDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
  let t : tameInertiaQuotient A := QuotientGroup.mk ⟨τ, h.inertia⟩
  obtain ⟨hn, ho⟩ := h.tame_character_nontrivial hp5
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime h.prime A h.lies_over
  obtain ⟨hc, ht⟩ := tameInertia_frobenius_power A hφ ⟨τ, h.inertia⟩
  let t' : tameInertiaQuotient A := QuotientGroup.mk ⟨φ * τ * φ⁻¹, hc⟩
  have hct : c t' = (c t) ^ q := by
    change c (QuotientGroup.mk ⟨φ * τ * φ⁻¹, hc⟩) = _
    rw [ht, map_pow]
  have hfix : c t' = c t ↔ (q : ZMod p) = 1 := by
    rw [hct]
    exact pow_eq_self_iff ho
  have hinv : (q : ZMod p) = -1 → c t' = (c t)⁻¹ ∧ c t' ≠ c t := by
    intro hneg
    rw [hct]
    exact ⟨pow_eq_inv ho hneg, pow_ne_self_of_negative (by omega) ho hneg⟩
  refine ⟨T.tameDifferenceCharacter_continuous hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over x, hn, ho, φ, hφ, hc, ht, hfix, hinv, ?_⟩
  rcases h.resonance with hpos | hneg
  · exact Or.inl ⟨hpos, hfix.mpr hpos⟩
  · exact Or.inr ⟨hneg, hinv hneg⟩

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
/-- 同じ hclass と Cofixed 候補から、同じ馴分岐商上の連続指標と共鳴分岐の証明書を得る。 -/
theorem residual_exists_resonant_tame_character
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let c := T.tameDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      let t : tameInertiaQuotient A := QuotientGroup.mk ⟨τ, h.inertia⟩
      Continuous c ∧ c t ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c t)) = p ∧
      ∃ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ValuationFrobenius.IsFrobeniusAt A φ q ∧
        ∃ hconj : φ * τ * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
        let t' : tameInertiaQuotient A := QuotientGroup.mk ⟨φ * τ * φ⁻¹, hconj⟩
        t' = t ^ q ∧ (c t' = c t ↔ (q : ZMod p) = 1) ∧
          ((q : ZMod p) = -1 → c t' = (c t)⁻¹ ∧ c t' ≠ c t) ∧
        (((q : ZMod p) = 1 ∧ c t' = c t) ∨
          ((q : ZMod p) = -1 ∧ c t' = (c t)⁻¹ ∧ c t' ≠ c t)) := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.tame_resonant_profile hp5⟩

end
end DkMath.FLT.Frey.Source
