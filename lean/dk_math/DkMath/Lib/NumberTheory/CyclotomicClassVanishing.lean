/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FiniteEigenTorsionBridge
import DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance
import Mathlib.NumberTheory.NumberField.ClassNumber

#print "file: DkMath.Lib.NumberTheory.CyclotomicClassVanishing"

/-!
# 実際の円分類群の冪商から p 捩れへの消滅移送

同じ実際の類群と Galois 作用を保ち、商 `Cl/pCl` の固有成分消滅を
`Cl[p]` へ移す。円分 Galois 群の位数の可逆性は内部供給する。
商側の算術的消滅は明示入力であり、本章で証明したわけではない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicClassVanishing

open DkMath.Lib.Algebra FiniteEigenTorsionBridge
open CyclotomicRootModule CyclotomicKernelField CyclotomicKummerWeight
open CyclotomicKummerClassMap CyclotomicKummerEquivariance KummerSelmerClassMap
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- 実際の類群を p 倍部分群で割った加法商。捩れ部分群とは異なる。 -/
abbrev ClassModP (F : Type*) [Field F] [NumberField F] (p : ℕ) :=
  ModQuotient p (Additive (ClassGroup (NumberField.RingOfIntegers F)))

/-- 前章の同じ実際の類群 Galois 作用を整数線形に読む。 -/
def classAction {F : Type*} [Field F] [NumberField F] :
    (F ≃ₐ[ℚ] F) →* (Additive (ClassGroup (NumberField.RingOfIntegers F)) ≃ₗ[ℤ]
      Additive (ClassGroup (NumberField.RingOfIntegers F))) :=
  additiveAction classGroupAction

/-- 同じ作用を実際の冪商へ下ろす。 -/
def classModPAction {F : Type*} [Field F] [NumberField F] (p : ℕ) :
    (F ≃ₐ[ℚ] F) →* (ClassModP F p ≃ₗ[ℤ] ClassModP F p) :=
  quotientAction p classAction

/-- 同じ有限類群の商での固有成分消滅から、同じ捩れ元の消滅を得る。
算術的消滅そのものは入力であり、自然な捩れから商への写像の単射性は使わない。 -/
theorem classTorsion_eq_one_of_quotient_eigen_vanishing
    {F : Type*} [Field F] [NumberField F] {p : ℕ} [NeZero p]
    (χ : (F ≃ₐ[ℚ] F) →* (ZMod p)ˣ)
    (hcard : IsUnit (Fintype.card (F ≃ₐ[ℚ] F) : ZMod p))
    (hvanish : ∀ v : ClassModP F p,
      (∀ γ : F ≃ₐ[ℚ] F, classModPAction p γ v = (χ γ : ZMod p) • v) → v = 0)
    (c : ClassTorsion (NumberField.RingOfIntegers F) p)
    (he : ∀ γ : F ≃ₐ[ℚ] F, classGroupAction γ c.val = c.val ^ (χ γ : ZMod p).val) : c = 1 := by
  apply Subtype.ext
  apply Additive.ofMul.injective
  change (Additive.ofMul c.val : Additive (ClassGroup (NumberField.RingOfIntegers F))) = 0
  apply torsion_eigen_eq_zero classAction χ hcard hvanish (Additive.ofMul c.val)
  · exact congrArg Additive.ofMul c.property
  · intro γ
    exact congrArg Additive.ofMul (he γ)

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance instRootFieldNumberField : NumberField (rootField ζ) := rootField_numberField ζ
local instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

include hζ in
/-- 実際の円分 Galois 群の位数は p−1。 -/
theorem root_galois_card : Nat.card ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) = p - 1 := by
  let : IsCyclotomicExtension {p} ℚ (rootField ζ) := rootField_isCyclotomic hζ
  let : IsGalois ℚ (rootField ζ) := IsCyclotomicExtension.isGalois {p} ℚ (rootField ζ)
  rw [IsGalois.card_aut_eq_finrank, rootField_finrank hζ]

include hζ in
/-- 実際の円分 Galois 群の位数は標数 p で可逆。新しい位数 provider を要求しない。 -/
theorem root_galois_card_isUnit :
    IsUnit (Fintype.card ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) : ZMod p) := by
  rw [← Nat.card_eq_fintype_card, root_galois_card hζ, ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_self_sub_left (Fact.out : p.Prime).pos]
  exact (Nat.coprime_one_left_iff p).mpr trivial

/-- 同じ実際の円分指標の二乗。 -/
def squareCharacter : ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) →* (ZMod p)ˣ :=
  (powMonoidHom 2).comp (baseCharacter hζ)

theorem squareCharacter_coe (γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)) :
    (squareCharacter hζ γ : ZMod p) = (baseCharacter hζ γ : ZMod p) ^ 2 := by
  exact Units.val_pow_eq_pow_val _ _

variable {C : Type*} [AddCommGroup C] [Module (ZMod p) C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)
    (P : (letI := CyclotomicCharacterField.extensionAlgebra ψ hζ;
      CyclicKummer.Presentation p (rootField ζ) (CyclotomicCharacterField.characterField ψ)))
    (hval : constantVector ψ hζ P ∈
      KummerSelmer.valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p)
    (hsurj : Function.Surjective ψ)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd)

include hsurj hopen hweight in
/-- 商側の ω² 消滅が供給された場合に、元の同じ Selmer 類の類群像の零化を内部で導く。
Selmer 所属と商側の算術的消滅は明示入力に残す。 -/
theorem classImage_eq_one_of_quotient_weight_square_vanishing
    (hvanish : ∀ v : ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        classModPAction p γ v = (baseCharacter hζ γ : ZMod p) ^ 2 • v) → v = 0) :
    classImage ψ hζ P hval = 1 := by
  apply classTorsion_eq_one_of_quotient_eigen_vanishing (squareCharacter hζ)
    (root_galois_card_isUnit hζ)
  · intro v hv
    apply hvanish v
    intro γ
    simpa only [squareCharacter_coe] using hv γ
  · intro γ
    have h := classImage_weight_square ψ hζ P hval hsurj hopen hweight γ
    have hs (a : ZMod p) (w : Additive (ClassTorsion (NumberField.RingOfIntegers (rootField ζ)) p)) :
        (a • w).toMul.val = w.toMul.val ^ a.val := by
      conv_lhs => rw [← ZMod.natCast_zmod_val a]
      rw [Nat.cast_smul_eq_nsmul, toMul_nsmul]
      rfl
    have hh := congrArg (fun w : Additive (ClassTorsion (NumberField.RingOfIntegers (rootField ζ)) p) =>
      w.toMul.val) h
    rw [hs, ← squareCharacter_coe hζ γ] at hh
    exact hh

end
end DkMath.Lib.NumberTheory.CyclotomicClassVanishing
