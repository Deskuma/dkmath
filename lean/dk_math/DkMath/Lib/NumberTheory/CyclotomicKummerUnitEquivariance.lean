/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance
import DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance

/-!
# 同じ円分 Kummer ベクトルから非零 ω² 単元類へ

数体の同じ Galois 群を、単元冪商・Selmer 群・類群捩れの実際の自己同型群へ写す。
既存の短完全列の両写像をこの作用と両立させる。
元のベクトルの Selmer 所属と類群像の零化を明示し、一意な同じ単元逆像へ二乗則を戻す。
算術的な所属・消滅や一般 hno の閉包を供給する定理ではない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance

open CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField CyclicKummer
open CyclotomicKummerWeight KummerSelmer KummerSelmerClassMap KummerSelmerExact
open CyclotomicKummerClassMap CyclotomicKummerEquivariance
open KummerSelmerEquivariance KummerSelmerUnitEquivariance
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- 実際の数体 Galois 群の、実際の整数環単元冪商への作用。 -/
def unitClassAction {F : Type*} [Field F] [NumberField F] (p : ℕ) :
    (F ≃ₐ[ℚ] F) →* MulAut (UnitClass (NumberField.RingOfIntegers F) p) where
  toFun γ := unitClassEquiv p (integerAut γ)
  map_one' := by
    ext u
    change unitClassMap p (integerAut (1 : F ≃ₐ[ℚ] F)) u = u
    rw [integerAut_one, unitClassMap_refl]
  map_mul' γ δ := by
    ext u
    change unitClassMap p (integerAut (γ * δ)) u =
      unitClassMap p (integerAut γ) (unitClassMap p (integerAut δ) u)
    rw [integerAut_mul, unitClassMap_trans]

/-- 同じ数体 Galois 群の、同じ Selmer 群への作用。 -/
def selmerAction {F : Type*} [Field F] [NumberField F] (p : ℕ) :
    (F ≃ₐ[ℚ] F) →* MulAut (Selmer (NumberField.RingOfIntegers F) F p) where
  toFun γ := selmerEquiv p (integerAut γ)
  map_one' := by
    apply MulEquiv.ext
    intro z
    change (integerAut (1 : F ≃ₐ[ℚ] F)).selmerMap p z = z
    rw [integerAut_one, selmerMap_refl]
  map_mul' γ δ := by
    apply MulEquiv.ext
    intro z
    change (integerAut (γ * δ)).selmerMap p z =
      (integerAut γ).selmerMap p ((integerAut δ).selmerMap p z)
    rw [integerAut_mul, selmerMap_trans]

/-- 同じ数体 Galois 群の、実際の類群 p 捩れへの作用。 -/
def classTorsionAction {F : Type*} [Field F] [NumberField F] (p : ℕ) :
    (F ≃ₐ[ℚ] F) →* MulAut (ClassTorsion (NumberField.RingOfIntegers F) p) where
  toFun γ := classTorsionEquiv p (integerAut γ)
  map_one' := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (integerAut (1 : F ≃ₐ[ℚ] F)).classGroupMap z.val = z.val
    rw [integerAut_one, CompatibleAut.classGroupMap_refl]
  map_mul' γ δ := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (integerAut (γ * δ)).classGroupMap z.val =
      (integerAut γ).classGroupMap ((integerAut δ).classGroupMap z.val)
    rw [integerAut_mul, CompatibleAut.classGroupMap_trans]

/-- 同じ実際の Galois 作用の下で、群の短完全列と両写像の同変性をまとめる。
固有成分を取った列の完全性や、その成分の消滅を主張しない。 -/
theorem numberField_short_exact_equivariant {F : Type*} [Field F] [NumberField F]
    (p : ℕ) (hp : 0 < p) :
    Function.Injective (unitInclusion (R := NumberField.RingOfIntegers F) (F := F) p hp) ∧
    (toClassTorsion (R := NumberField.RingOfIntegers F) (F := F) p hp).ker =
      (unitInclusion p hp).range ∧
    Function.Surjective (toClassTorsion (R := NumberField.RingOfIntegers F) (F := F) p hp) ∧
    (∀ γ : F ≃ₐ[ℚ] F, ∀ u : UnitClass (NumberField.RingOfIntegers F) p,
      selmerAction p γ (unitInclusion p hp u) = unitInclusion p hp (unitClassAction p γ u)) ∧
    (∀ γ : F ≃ₐ[ℚ] F, ∀ z : Selmer (NumberField.RingOfIntegers F) F p,
      toClassTorsion p hp (selmerAction p γ z) = classTorsionAction p γ (toClassTorsion p hp z)) :=
  ⟨unitInclusion_injective p hp, kernel_eq_unit_range p hp, toClassTorsion_surjective p hp,
    fun γ => unitInclusion_equivariant p hp (integerAut γ),
    fun γ => (integerAut γ).toClassTorsion_equivariant p hp⟩

variable {p : ℕ} [Fact p.Prime] {C : Type*} [AddCommGroup C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberField : NumberField (rootField ζ) := rootField_numberField ζ

variable (P : (letI := extensionAlgebra ψ hζ; Presentation p (rootField ζ) (characterField ψ)))
    (hval : constantVector ψ hζ P ∈
      valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p)
    (hzero : classImage ψ hζ P hval = 1)

/-- 元の同じ Selmer 類を表す、一意な単元冪商の類。 -/
def unitImage : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p :=
  unitPreimage p (Fact.out : p.Prime).pos (selmerElement ψ hζ P hval) hzero

theorem unitImage_spec :
    unitInclusion p (Fact.out : p.Prime).pos (unitImage ψ hζ P hval hzero) =
      selmerElement ψ hζ P hval :=
  unitPreimage_spec p (Fact.out : p.Prime).pos _ hzero

/-- 元の Kummer ベクトルが非零なので、同じ単元逆像も非自明。 -/
theorem unitImage_ne_one : unitImage ψ hζ P hval hzero ≠ 1 := by
  apply unitPreimage_ne_one
  intro hz
  apply constantClass_ne_one ψ hζ P
  exact congrArg Subtype.val hz

variable [Module (ZMod p) C]
    (hsurj : Function.Surjective ψ)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd)

include hsurj hopen hweight in
/-- 同じ一意な非零単元類の ω² 固有性。単元の固有性を provider として要求しない。 -/
theorem unitImage_weight_square (γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)) :
    unitClassLinearMap p (integerAut γ) (Additive.ofMul (unitImage ψ hζ P hval hzero)) =
      (baseCharacter hζ γ : ZMod p) ^ 2 • Additive.ofMul (unitImage ψ hζ P hval hzero) := by
  apply unitClassLinearMap_weight p (Fact.out : p.Prime).pos (integerAut γ)
    (selmerElement ψ hζ P hval) _ (unitImage_spec ψ hζ P hval hzero)
  exact constantClass_weight_square ψ hζ P hsurj hopen hweight γ

include hsurj hopen hweight in
/-- 同じ定数の単元倍冪表示を保持し、その同じ実際の単元の冪商類に二乗則を戻す。 -/
theorem unit_of_classImage_eq_one_weight_square :
    letI := extensionAlgebra ψ hζ
    ∃ (u : (NumberField.RingOfIntegers (rootField ζ))ˣ) (c : (rootField ζ)ˣ),
      P.constant = algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ) u * (c : rootField ζ) ^ p ∧
      constantVector ψ hζ P = Additive.ofMul
        ((Units.map (algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ)).toMonoidHom u :
          (rootField ζ)ˣ) : KummerClass (rootField ζ) p) ∧
      unitImage ψ hζ P hval hzero = (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) ∧
      (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) ≠ 1 ∧
      ∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        unitClassLinearMap p (integerAut γ)
            (Additive.ofMul (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p)) =
          (baseCharacter hζ γ : ZMod p) ^ 2 •
            Additive.ofMul (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) := by
  let := extensionAlgebra ψ hζ
  obtain ⟨u, c, he, hw, hne⟩ := unit_of_classImage_eq_one ψ hζ P hval hzero
  have hu : unitInclusion p (Fact.out : p.Prime).pos
      (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) = selmerElement ψ hζ P hval := by
    apply Subtype.ext
    exact (congrArg Additive.toMul hw).symm
  have hsame : unitImage ψ hζ P hval hzero =
      (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) :=
    unitPreimage_eq p (Fact.out : p.Prime).pos _ hzero _ hu
  refine ⟨u, c, he, hw, hsame, hne, ?_⟩
  intro γ
  rw [← hsame]
  exact unitImage_weight_square ψ hζ P hval hzero hsurj hopen hweight γ

end
end DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance
