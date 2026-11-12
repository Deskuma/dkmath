/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerLocalValuation
import DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic
import DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration

#print "file: DkMath.Lib.NumberTheory.CyclotomicKummerSelmer"

/-!
# 同じ円分 Kummer 根の絶対慣性固定性から Selmer 所属へ

実際の有限整数環の相対慣性元を、同じ正規中間体を保ったまま絶対慣性へ持ち上げる。
相対元が円分体を固定するため、その絶対持ち上げも円分指標の核に入る。
同じ根の固定性から e=1 と全素点の指数の p 可除性を得る。
局所 p 乗性、類群・単元消滅、共鳴住所の吸収は結論しない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicKummerSelmer

open CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField CyclicKummer
open CyclotomicKummerWeight KummerSelmer KummerLocalValuation ValuationInertia
open scoped NumberField
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] {C : Type*} [AddCommGroup C] [Module (ZMod p) C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd)

local instance instRootNumberField : NumberField (rootField ζ) := rootField_numberField ζ
variable (P : (letI := extensionAlgebra ψ hζ;
  Presentation p (rootField ζ) (characterField ψ)))

/-- 元の同じ絶対慣性固定性。q=p を含む全有限住所を量化する。
Frey では p 上の分解群固定性と p 外の慣性固定性から内部で供給する。 -/
def AbsoluteInertiaFixesRadical : Prop :=
  letI := extensionAlgebra ψ hζ
  ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
    ∀ g : (cyclotomicCharacter (K := ℚ) p).ker,
      kernelEquiv hζ g ∈ inertiaSubgroupIn A (rootField ζ) →
        kernelEquiv hζ g P.radical.val = P.radical.val

include hopen hweight in
/-- 同じ有限相対慣性元を実際の絶対慣性へ持ち上げ、同じ根の固定性を戻す。 -/
theorem finite_inertia_fixes_radical [NumberField (characterField ψ)]
    (hlocal : AbsoluteInertiaFixesRadical ψ hζ P)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ)))
    (τ : (letI := extensionAlgebra ψ hζ;
      (characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)))
    (hτ : letI := extensionAlgebra ψ hζ
      τ ∈ w.asIdeal.inertia ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ))) :
    letI := extensionAlgebra ψ hζ
    τ P.radical = P.radical := by
  let := extensionAlgebra ψ hζ
  let : IsScalarTower ℚ (rootField ζ) (characterField ψ) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let : IsGalois ℚ (characterField ψ) := characterField_isGalois ψ hopen hweight
  have : w.asIdeal.IsMaximal := w.isMaximal
  let : Field (𝓞 (characterField ψ) ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 (characterField ψ) ⧸ w.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  obtain ⟨q, hqchar⟩ := CharP.exists (𝓞 (characterField ψ) ⧸ w.asIdeal)
  have := hqchar
  have hq : q.Prime := CharP.char_is_prime (𝓞 (characterField ψ) ⧸ w.asIdeal) q
  have hqmem : (q : 𝓞 (characterField ψ)) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  have hτQ : τ.restrictScalars ℚ ∈ w.asIdeal.inertia ((characterField ψ) ≃ₐ[ℚ] (characterField ψ)) := by
    apply AddSubgroup.mem_inertia.mpr
    intro a
    exact (AddSubgroup.mem_inertia.mp hτ) a
  obtain ⟨σ, hστ, A, hA, hσA⟩ := AbsoluteInertiaGeneration.exists_lift_mem_valuation_inertia
    (characterField ψ) w.asIdeal hq hqmem (τ.restrictScalars ℚ) hτQ
  have hres (a : characterField ψ) : σ a.val = (τ a).val := by
    calc
      σ a.val = ((σ.restrictNormal (characterField ψ)) a).val :=
        (AlgEquiv.restrictNormal_commutes σ (characterField ψ) a).symm
      _ = ((τ.restrictScalars ℚ) a).val := congrArg (fun f => (f a).val) hστ
      _ = (τ a).val := rfl
  have hσζ : σ ζ = ζ := by
    have he := hres (algebraMap (rootField ζ) (characterField ψ) (baseRoot ζ))
    rw [τ.commutes] at he
    exact he
  let g : (cyclotomicCharacter (K := ℚ) p).ker :=
    ⟨σ, (character_eq_one_iff_fix_root hζ σ).mpr hσζ⟩
  have hg : kernelEquiv hζ g ∈ inertiaSubgroupIn A (rootField ζ) :=
    (kernelEquiv_mem_inertia_iff hζ A g).mpr hσA
  apply Subtype.ext
  exact (hres P.radical).symm.trans (hlocal q hq A hA g hg)

include hopen hweight in
/-- 同じ根の絶対慣性固定性から、元の同じ定数ベクトルの全有限素点の Selmer 条件へ。 -/
theorem constantVector_mem_valuationSpace_of_absolute_inertia
    (hlocal : AbsoluteInertiaFixesRadical ψ hζ P) :
    constantVector ψ hζ P ∈ valuationSpace (R := 𝓞 (rootField ζ)) p := by
  let := extensionAlgebra ψ hζ
  let : NumberField (characterField ψ) := characterField_numberField ψ hopen
  let : IsScalarTower ℚ (rootField ζ) (characterField ψ) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let : IsGalois (rootField ζ) (characterField ψ) := relative_isGalois ψ hζ hopen hweight
  apply (mem_valuationSpace_mk_iff p (constantUnit ψ hζ P)).mpr
  intro v
  obtain ⟨W, hWmax, hWv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 (rootField ζ)) (𝓞 (characterField ψ)))]; exact bot_le)
  have : W.IsMaximal := hWmax
  have : W.LiesOver v.asIdeal := ⟨hWv.symm⟩
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ)) :=
    ⟨W, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot W⟩
  exact count_dvd_of_inertia_fixes_radical P v w (Fact.out : p.Prime).one_lt
    (finite_inertia_fixes_radical ψ hζ hopen hweight P hlocal w)

end
end DkMath.Lib.NumberTheory.CyclotomicKummerSelmer
