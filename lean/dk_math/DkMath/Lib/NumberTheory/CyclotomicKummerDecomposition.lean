/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerDecomposition
import DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic
import DkMath.Lib.NumberTheory.AbsoluteDecompositionLift

#print "file: DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition"

/-!
# 同じ円分 Kummer 根の p 上の有限分解群

絶対分解群の固定性を同じ M/F の有限分解群へ移す。
素点の剰余体作用を恒等にする慣性の持ち上げでは足りないので、
分解群そのものの持ち上げを使う。hbad はこの章の入力ではない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition

open CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField CyclicKummer
open CyclotomicKummerWeight KummerSelmer KummerDecomposition ValuationInertia
open scoped NumberField Pointwise
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

/-- p 上の全絶対分解群が同じ根を固定するという元の局所性。 -/
def AbsoluteDecompositionFixesRadicalAtP : Prop :=
  letI := extensionAlgebra ψ hζ
  ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A p →
    ∀ g : (cyclotomicCharacter (K := ℚ) p).ker,
      kernelEquiv hζ g ∈ A.decompositionSubgroup (rootField ζ) →
        kernelEquiv hζ g P.radical.val = P.radical.val

include hopen hweight in
/-- p を含む同じ有限素点の分解群は同じ根を固定する。
絶対元への制限で ζ と α の双方を同じまま追跡する。 -/
theorem finite_decomposition_fixes_radical_at_p [NumberField (characterField ψ)]
    (hlocal : AbsoluteDecompositionFixesRadicalAtP ψ hζ P)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ)))
    (hpw : (p : 𝓞 (characterField ψ)) ∈ w.asIdeal)
    (τ : (letI := extensionAlgebra ψ hζ;
      (characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)))
    (hτ : letI := extensionAlgebra ψ hζ
      τ ∈ MulAction.stabilizer ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)) w.asIdeal) :
    letI := extensionAlgebra ψ hζ
    τ P.radical = P.radical := by
  let := extensionAlgebra ψ hζ
  let : IsScalarTower ℚ (rootField ζ) (characterField ψ) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let : IsGalois ℚ (characterField ψ) := characterField_isGalois ψ hopen hweight
  have : w.asIdeal.IsMaximal := w.isMaximal
  have hτQ : τ.restrictScalars ℚ ∈ MulAction.stabilizer ((characterField ψ) ≃ₐ[ℚ] (characterField ψ)) w.asIdeal := hτ
  obtain ⟨σ, hστ, A, hA, hσA⟩ := AbsoluteDecompositionLift.exists_lift_mem_valuation_decomposition
    (characterField ψ) w.asIdeal (Fact.out : p.Prime) hpw (τ.restrictScalars ℚ) hτQ
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
  have hg : kernelEquiv hζ g ∈ A.decompositionSubgroup (rootField ζ) :=
    (kernelEquiv_mem_decomposition_iff hζ A g).mpr hσA
  apply Subtype.ext
  exact (hres P.radical).symm.trans (hlocal A hA g hg)

include hopen hweight in
/-- 同じ有限素点の分解群自明性。局所次数1や完備体への降下はまだ結論しない。 -/
theorem finite_decomposition_eq_bot_at_p [NumberField (characterField ψ)]
    (hlocal : AbsoluteDecompositionFixesRadicalAtP ψ hζ P)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ)))
    (hpw : (p : 𝓞 (characterField ψ)) ∈ w.asIdeal) :
    letI := extensionAlgebra ψ hζ
    MulAction.stabilizer ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)) w.asIdeal = ⊥ := by
  let := extensionAlgebra ψ hζ
  apply subgroup_eq_bot_of_fixes_radical P
  exact finite_decomposition_fixes_radical_at_p ψ hζ hopen hweight P hlocal w hpw

include hopen hweight in
/-- p 上の同じ v,w に対する実際の e=f=1。分解群固定性だけを使う。 -/
theorem ramification_and_inertiaDeg_eq_one_at_p [NumberField (characterField ψ)]
    (hlocal : AbsoluteDecompositionFixesRadicalAtP ψ hζ P)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (rootField ζ)))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ)))
    (hvw : letI := extensionAlgebra ψ hζ; w.asIdeal.LiesOver v.asIdeal)
    (hpv : (p : 𝓞 (rootField ζ)) ∈ v.asIdeal) :
    letI := extensionAlgebra ψ hζ
    v.asIdeal.ramificationIdx' w.asIdeal = 1 ∧ w.asIdeal.inertiaDeg (𝓞 (rootField ζ)) = 1 := by
  let := extensionAlgebra ψ hζ
  let : IsScalarTower ℚ (rootField ζ) (characterField ψ) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let : IsGalois (rootField ζ) (characterField ψ) := relative_isGalois ψ hζ hopen hweight
  have := hvw
  have hpw : (p : 𝓞 (characterField ψ)) ∈ w.asIdeal := by
    rw [← map_natCast (algebraMap (𝓞 (rootField ζ)) (𝓞 (characterField ψ))) p]
    exact (Ideal.mem_of_liesOver w.asIdeal v.asIdeal _).mp hpv
  exact ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical P v w
    (finite_decomposition_fixes_radical_at_p ψ hζ hopen hweight P hlocal w hpw)

end
end DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition
