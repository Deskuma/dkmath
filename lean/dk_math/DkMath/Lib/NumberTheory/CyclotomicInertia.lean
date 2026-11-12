/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Cyclotomic ramification argument adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow.lean,
blob 394ae95ec48cc4d879df49e06a7b8ff8493d6bc9.
Modified: reuse DkMath finite inertia lifting and place conjugacy; avoid a second
valuation/ramification dictionary; return the actual DkMath cyclotomic character.
-/

import DkMath.Lib.NumberTheory.CyclotomicRootModule
import DkMath.Lib.NumberTheory.IntegralClosureInertiaLift
import DkMath.Lib.NumberTheory.ValuationInertiaLift
import DkMath.Lib.NumberTheory.ValuationPlaceConjugacy
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.Cyclotomic.Gal

#print "file: DkMath.Lib.NumberTheory.CyclotomicInertia"

/-!
# 指定した `p` 上の慣性群での円分指標の全射性

有限円分体で `p` は完全分岐する。従ってその慣性群は全 Galois 群である。
指定した指標値を持つ有限自己同型を実際の絶対慣性元へ持ち上げる。
まず得られる付値環を指定された同じ `A` へ共役で移す。
円分指標の値域は可換なので、この共役で指標値は変わらない。

有限慣性の持ち上げ、付値環の存在、共役輸送は既存の DkMath 定理で供給する。
これらを provider として追加しない。剰余体の有限性を `A` に仮定することもない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicInertia

open CyclotomicRootModule ValuationInertia
open scoped NumberField Pointwise

noncomputable section

variable {p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 800000 in
-- Finite cyclotomic fields, residue fields and integral inertia lifts are elaborated together.
/-- 任意の `p` 上の付値環で、円分指標の慣性への制限は全射。 -/
theorem exists_inertia_cyclotomic_eq
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p)
    (a : (ZMod p)ˣ) :
    ∃ σ ∈ inertiaSubgroupIn A ℚ, cyclotomicCharacter p σ = a := by
  have hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {ζ}
  let : FiniteDimensional ℚ L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  let : IsCyclotomicExtension {p} ℚ L := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p} ℚ L
  let : NumberField L := ⟨⟩
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζL : IsPrimitiveRoot ζL p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L (AlgebraicClosure ℚ)) hζ
      (algebraMap L (AlgebraicClosure ℚ)).injective
  have hχ : Function.Bijective (hζL.autToPow ℚ) := by
    apply (Nat.bijective_iff_injective_and_card _).mpr
    refine ⟨hζL.autToPow_injective ℚ, ?_⟩
    rw [IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank (K := ℚ) (n := p) L
        (Polynomial.cyclotomic.irreducible_rat hp.pos),
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  obtain ⟨τ, hτ⟩ := hχ.2 a
  have hτζ : τ ζL = ζL ^ (a : ZMod p).val := by
    rw [← hτ]
    exact (hζL.autToPow_spec ℚ τ).symm
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  let : I.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := NumberField.RingOfIntegers L) I
  let := hQmax
  let := hQover
  have hpQ : (p : NumberField.RingOfIntegers L) ∈ Q := by
    have h : (p : ℤ) ∈ I := Ideal.subset_span rfl
    have h' := hQover.over ▸ h
    simpa using h'
  let : Field (ℤ ⧸ I) := Ideal.Quotient.field I
  let : Finite (ℤ ⧸ I) := Finite.of_equiv _ (Int.quotientSpanEquivZMod p).symm.toEquiv
  let : PerfectField (ℤ ⧸ I) := PerfectField.ofFinite
  have htop : Q.inertia (L ≃ₐ[ℚ] L) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) I Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx I Q (L ≃ₐ[ℚ] L),
      IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p L Q,
      IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank (K := ℚ) (n := p) L
        (Polynomial.cyclotomic.irreducible_rat hp.pos), Nat.totient_prime hp]
  have hτI : τ ∈ Q.inertia (L ≃ₐ[ℚ] L) := htop ▸ Subgroup.mem_top τ
  obtain ⟨σ, hres, 𝔔, h𝔔max, hp𝔔, hσ𝔔⟩ :=
    IntegralClosureInertiaLift.exists_lift_mem_inertia_integralClosure L Q hpQ τ hτI
  let := h𝔔max
  obtain ⟨A₁, hA₁, hσA₁⟩ :=
    ValuationInertiaLift.exists_valuation_inertia_of_integral_congruence 𝔔 hp hp𝔔 σ hσ𝔔
  have hσζ : σ ζ = ζ ^ (a : ZMod p).val := by
    have h : ((AlgEquiv.restrictNormalHom L σ) ζL : AlgebraicClosure ℚ) = σ ζ :=
      @AlgEquiv.restrictNormalHom_apply ℚ _ _ _ _ L inferInstance σ ζL
    rw [hres, hτζ] at h
    exact h.symm.trans (map_pow (algebraMap L (AlgebraicClosure ℚ)) ζL _)
  have hσχ : cyclotomicCharacter p σ = a := by
    apply Units.ext
    apply ZMod.val_injective p
    apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    let z : rootsOfUnity p (AlgebraicClosure ℚ) :=
      ⟨Units.mk0 ζ (hζ.ne_zero hp.ne_zero), (mem_rootsOfUnity p _).mpr (Units.ext hζ.pow_eq_one)⟩
    have hs := cyclotomicCharacter_spec (K := ℚ) p σ z
    exact hs.symm.trans hσζ
  obtain ⟨g, hg⟩ := ValuationPlaceConjugacy.exists_smul_eq hp hA₁ hA
  refine ⟨g * σ * g⁻¹, ?_, ?_⟩
  · simpa only [hg] using ValuationPlaceConjugacy.conj_mem_inertia_smul A₁ g σ hσA₁
  · erw [map_mul, map_mul, map_inv, hσχ]
    simp [mul_comm]

end
end DkMath.Lib.NumberTheory.CyclotomicInertia
