/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclicKummer
import DkMath.Lib.NumberTheory.CyclotomicCharacterField

#print "file: DkMath.Lib.NumberTheory.CyclotomicCharacterKummer"

/-!
# 指標の同じ固定体の Kummer 根

開核・全射性・逆指標の共役則から、同じ `M/F` に Kummer 表示を与える。
元の指標の核は同じ根の固定群と一致する。この段階では
Kummer 根の円分共役の重み、整数化、類群・単数の消滅は未実装である。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicCharacterKummer

open CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField CyclicKummer
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] {C : Type*} [AddCommGroup C] [Module (ZMod p) C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)

/-- 指定した原始根を同じ底体の元として使う。原始根の provider は増やさない。 -/
theorem rootField_primitiveRoots {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    (primitiveRoots p (rootField ζ)).Nonempty := by
  let z : rootField ζ := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hz : IsPrimitiveRoot z p := hζ.of_map_of_injective (rootField ζ).val.injective
  exact ⟨z, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hz⟩

/-- 元の指標の核の固定体に、実際の非自明 Kummer 表示を構成する。 -/
theorem exists_presentation {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hsurj : Function.Surjective ψ) (hC : Nat.card C = p)
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd) :
    letI := extensionAlgebra ψ hζ
    Nonempty (Presentation p (rootField ζ) (characterField ψ)) := by
  let := extensionAlgebra ψ hζ
  let : IsScalarTower ℚ (rootField ζ) (characterField ψ) :=
    IsScalarTower.of_algebraMap_eq' (by ext q; rfl)
  let : FiniteDimensional ℚ (characterField ψ) := characterField_finite ψ hopen
  let : FiniteDimensional (rootField ζ) (characterField ψ) :=
    Module.Finite.of_restrictScalars_finite ℚ (rootField ζ) (characterField ψ)
  let : IsGalois (rootField ζ) (characterField ψ) := relative_isGalois ψ hζ hopen hweight
  let : IsCyclic ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)) :=
    relative_isCyclic ψ hζ hopen hsurj hC hweight
  exact CyclicKummer.exists_presentation ((relative_finrank ψ hζ hopen hsurj).trans hC)
    (rootField_primitiveRoots hζ)

omit [Module (ZMod p) C] in
/-- 元の指標核と根の固定群は一致する。単なる別の巡回拡大への移行ではない。
逆向きは `F(α)=M` と開核の正確な Galois 対応を使う。 -/
theorem character_eq_one_iff_fix_radical {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (P : letI := extensionAlgebra ψ hζ; Presentation p (rootField ζ) (characterField ψ))
    (g : (cyclotomicCharacter (K := ℚ) p).ker) :
    letI := extensionAlgebra ψ hζ
    ψ g = 1 ↔ kernelEquiv hζ g P.radical.val = P.radical.val := by
  let := extensionAlgebra ψ hζ
  constructor
  · intro hg
    exact (IntermediateField.mem_fixedField_iff (kernelInGalois ψ) P.radical.val).mp
      P.radical.property g.val ((mem_kernelInGalois ψ g).mpr hg)
  · intro hg
    let i : characterField ψ →ₐ[rootField ζ] AlgebraicClosure ℚ :=
      { (characterField ψ).val with commutes' := fun _ => rfl }
    have he : (kernelEquiv hζ g).toAlgHom.comp i = i := P.algHom_ext hg
    apply (mem_kernelInGalois ψ g).mp
    rw [← fixingSubgroup_characterField ψ hopen]
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    intro x hx
    exact DFunLike.congr_fun he ⟨x, hx⟩

end
end DkMath.Lib.NumberTheory.CyclotomicCharacterKummer
