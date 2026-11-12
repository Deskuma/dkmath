/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicKummerClassMap
import DkMath.Lib.NumberTheory.KummerSelmerEquivariance

/-!
# 元の円分 Kummer 類から実際の類群の ω² 成分へ

整数環の自己同型は底体の Galois 自己同型そのものの制限である。
同じ Selmer 類の像への同変性を内部供給し、元の二乗則を実際の類群へ移す。
元のベクトルの Selmer 所属は明示入力であり、像の非零性や消滅は結論しない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance

open CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField CyclicKummer
open CyclotomicKummerWeight KummerSelmer KummerSelmerClassMap
open CyclotomicKummerClassMap KummerSelmerEquivariance
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- 実際の数体自己同型と、その整数環への実際の制限。 -/
def integerAut {F : Type*} [Field F] [NumberField F] (γ : F ≃ₐ[ℚ] F) :
    CompatibleAut (NumberField.RingOfIntegers F) F where
  integers := NumberField.RingOfIntegers.mapRingEquiv γ.toRingEquiv
  field := γ.toRingEquiv
  commutes _ := rfl

theorem integerAut_one {F : Type*} [Field F] [NumberField F] :
    integerAut (1 : F ≃ₐ[ℚ] F) = CompatibleAut.refl := by
  apply CompatibleAut.ext
  · ext x
    rfl
  · rfl

theorem integerAut_mul {F : Type*} [Field F] [NumberField F] (γ δ : F ≃ₐ[ℚ] F) :
    integerAut (γ * δ) = (integerAut δ).trans (integerAut γ) := by
  apply CompatibleAut.ext
  · ext x
    rfl
  · rfl

/-- 実際の数体 Galois 群から、実際の類群の自己同型群への作用。 -/
def classGroupAction {F : Type*} [Field F] [NumberField F] :
    (F ≃ₐ[ℚ] F) →* MulAut (ClassGroup (NumberField.RingOfIntegers F)) where
  toFun γ := (integerAut γ).classGroupEquiv
  map_one' := by
    ext z
    change (integerAut (1 : F ≃ₐ[ℚ] F)).classGroupMap z = z
    rw [integerAut_one, CompatibleAut.classGroupMap_refl]
  map_mul' γ δ := by
    ext z
    change (integerAut (γ * δ)).classGroupMap z =
      (integerAut γ).classGroupMap ((integerAut δ).classGroupMap z)
    rw [integerAut_mul, CompatibleAut.classGroupMap_trans]

variable {p : ℕ} [Fact p.Prime] {C : Type*} [AddCommGroup C] [Module (ZMod p) C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberField : NumberField (rootField ζ) := rootField_numberField ζ

variable (P : (letI := extensionAlgebra ψ hζ; Presentation p (rootField ζ) (characterField ψ)))
    (hval : constantVector ψ hζ P ∈
      valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p)
    (hsurj : Function.Surjective ψ)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd)

include hsurj hopen hweight in
/-- 同じ Selmer 類の類群像は、整数環への制限から作った実際の作用の ω² 固有条件を満たす。
像が零となる場合も含む。`hval` の供給や類群成分の消滅は別の算術的段階である。 -/
theorem classImage_weight_square (γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)) :
    (integerAut γ).classTorsionLinearMap p (Additive.ofMul (classImage ψ hζ P hval)) =
      (baseCharacter hζ γ : ZMod p) ^ 2 • Additive.ofMul (classImage ψ hζ P hval) := by
  apply CompatibleAut.classImage_weight (integerAut γ) (Fact.out : p.Prime).pos
    (selmerElement ψ hζ P hval)
  exact constantClass_weight_square ψ hζ P hsurj hopen hweight γ

end
end DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance
