/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem, P2M/Sol/S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean.
Upstream blob: 184332c9dba26f74e44b61e9e2fc1a4a86cd36ab
Modified for DkMath: named arithmetic interfaces, textbook explanations,
separate absolute-inertia layers, and current Mathlib APIs.
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.CharP.Lemmas
import DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration
import DkMath.Lib.NumberTheory.IntegralClosureInertiaLift
import DkMath.Lib.NumberTheory.ValuationInertiaLift

#print "file: DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration"

/-!
# NOTE-031-001B: 全ての有限素点の絶対慣性を含む開部分群は全群

Krull位相の開部分群Hは、ある有限正規中間体Lの固定部分群を含む。
Lの各有限慣性元を、整数閉包と付値環を通じて絶対慣性元へ持ち上げる。
従ってHのLへの制限像は全有限慣性群を含み、031-001AによりGal(L/ℚ)全体となる。
制限の核もHに含まれるのでH自体が全絶対ガロア群となる。

開性を省いて稠密部分群と全群を混同しない。また、有限慣性元の持ち上げを
providerとして仮定せず、この章より前の二つの算術証明を実際に使う。
-/
namespace DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration
open ValuationInertia

/-- 有限正規中間体の慣性元を、指定された素数q上のある付値環の絶対慣性へ持ち上げる。
整数閉包の合同と付値環全体の慣性の間の比較を合成した公開入口。 -/
theorem exists_lift_mem_valuation_inertia
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsMaximal] {q : ℕ}
    (hq : q.Prime) (hqQ : (q : NumberField.RingOfIntegers L) ∈ Q)
    (τ : L ≃ₐ[ℚ] L) (hτ : τ ∈ Q.inertia (L ≃ₐ[ℚ] L)) :
    ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      AlgEquiv.restrictNormalHom L σ = τ ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ),
        LiesOverPrime A q ∧ σ ∈ inertiaSubgroupIn A ℚ := by
  obtain ⟨σ, hστ, 𝔔, hmax, hq𝔔, hσ⟩ :=
    IntegralClosureInertiaLift.exists_lift_mem_inertia_integralClosure L Q hqQ τ hτ
  have := hmax
  obtain ⟨A, hA, hσA⟩ :=
    ValuationInertiaLift.exists_valuation_inertia_of_integral_congruence 𝔔 hq hq𝔔 σ hσ
  exact ⟨σ, hστ, A, hA, hσA⟩

open scoped Pointwise NumberField

/-- 全ての素数qとq上の全ての付値環の絶対慣性群を含む開部分群は全群である。
有限正規レベルへの制限と核の両方をH内に保って、実際の絶対ガロア群で結論する。 -/
theorem subgroup_eq_top_of_inertia_le
    (H : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)))
    (hopen : IsOpen (H : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))))
    (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → inertiaSubgroupIn A ℚ ≤ H) : H = ⊤ := by
  classical
  have hnorm : Normal ℚ (AlgebraicClosure ℚ) := by
    have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h
  obtain ⟨L, hLfin, hLnorm, hLH'⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ (AlgebraicClosure ℚ) _).mp (hopen.mem_nhds H.one_mem)
  have := hLfin
  have := hLnorm
  have : IsGalois ℚ L := @IsGalois.mk ℚ _ L _ _ inferInstance hLnorm
  have hLH : L.fixingSubgroup ≤ H := fun σ hσ => hLH' hσ
  let res := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L
  have : NumberField L := NumberField.mk
  have htop : H.map res = ⊤ := by
    apply NumberFieldInertiaGeneration.subgroup_eq_top_of_inertia_le
    intro Q hQ τ hτ
    have := hQ
    obtain ⟨q, hqchar⟩ := CharP.exists (𝓞 L ⧸ Q)
    have := hqchar
    have : Finite (𝓞 L ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient
      (Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField L))
    let : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
    have hqprime : q.Prime := CharP.char_is_prime (𝓞 L ⧸ Q) q
    have hqQ : (q : 𝓞 L) ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact CharP.cast_eq_zero (𝓞 L ⧸ Q) q
    obtain ⟨σ, hστ, A, hA, hσA⟩ :=
      exists_lift_mem_valuation_inertia L Q hqprime hqQ τ hτ
    exact ⟨σ, hunr q hqprime A hA hσA, hστ⟩
  rw [Subgroup.eq_top_iff']
  intro σ
  have hmem : res σ ∈ H.map res := htop ▸ Subgroup.mem_top _
  obtain ⟨h, hh, hres⟩ := hmem
  have hker : h⁻¹ * σ ∈ L.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv]
    change (res h)⁻¹ * res σ = 1
    rw [hres, inv_mul_cancel]
  have : h * (h⁻¹ * σ) ∈ H := H.mul_mem hh (hLH hker)
  simpa using this

end DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration
