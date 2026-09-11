/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRGaloisAction
import Mathlib.NumberTheory.Cyclotomic.Gal

#print "file: DkMath.NumberTheory.CyclotomicQRGaloisRealization"

namespace DkMath.NumberTheory.CyclotomicQRGaloisRealization

open DkMath.NumberTheory.CyclotomicQRProduct
open DkMath.NumberTheory.CyclotomicQRGaloisAction

noncomputable section

/-! ## Nonzero residues and units -/

private theorem nonzero_residue_coprime
    {p : ℕ} [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0) :
    Nat.Coprime t.val p := by
  have hp : p.Prime := Fact.out
  exact (Nat.coprime_of_lt_prime (n := t.val) (p := p)
    (ZMod.val_ne_zero t |>.2 ht) t.val_lt hp).symm

def nonzeroExponentUnit
    {p : ℕ} [Fact p.Prime] (t : ZMod p) (ht : t ≠ 0) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime t.val (nonzero_residue_coprime ht)

theorem coe_nonzeroExponentUnit
    {p : ℕ} [Fact p.Prime] (t : ZMod p) (ht : t ≠ 0) :
    (nonzeroExponentUnit t ht : ZMod p) = t := by
  rw [nonzeroExponentUnit, ZMod.coe_unitOfCoprime]
  exact ZMod.natCast_zmod_val t

theorem nonzeroExponentUnit_ne_zero
    {p : ℕ} [Fact p.Prime] (t : ZMod p) (ht : t ≠ 0) :
    (nonzeroExponentUnit t ht : ZMod p) ≠ 0 := by
  rw [coe_nonzeroExponentUnit t ht]
  exact ht

/-! ## Realization of every nonzero exponent -/

theorem exists_cyclotomicAut_pow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (hirr : Irreducible (Polynomial.cyclotomic p K))
    (t : ZMod p) (ht : t ≠ 0) :
    ∃ σ : L ≃ₐ[K] L, σ ζ = ζ ^ t.val := by
  let ω : L := IsCyclotomicExtension.zeta p K L
  have hω : IsPrimitiveRoot ω p := IsCyclotomicExtension.zeta_spec p K L
  obtain ⟨i, hi, hζi⟩ := hω.eq_pow_of_pow_eq_one hζ.pow_eq_one
  let hμ : IsPrimitiveRoot (ω ^ t.val) p :=
    hω.pow_of_coprime t.val (nonzero_residue_coprime ht)
  let σ : L ≃ₐ[K] L := IsCyclotomicExtension.fromZetaAut hμ hirr
  refine ⟨σ, ?_⟩
  have hσω : σ ω = ω ^ t.val := by
    exact IsCyclotomicExtension.fromZetaAut_spec hμ hirr
  calc
    σ ζ = σ (ω ^ i) := by rw [hζi]
    _ = (σ ω) ^ i := by rw [map_pow]
    _ = (ω ^ t.val) ^ i := by rw [hσω]
    _ = (ω ^ i) ^ t.val := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = ζ ^ t.val := by rw [hζi]

/-! ## Full invariance under the cyclotomic Galois group -/

theorem cyclotomicAut_power_spec
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (σ : L ≃ₐ[K] L) :
    ∃ ut : (ZMod p)ˣ, (ut : ZMod p) ≠ 0 ∧
      σ ζ = ζ ^ (ut : ZMod p).val := by
  let ut : (ZMod p)ˣ := hζ.autToPow K σ
  have hut0 : (ut : ZMod p) ≠ 0 := Units.ne_zero ut
  have hσζ : σ ζ = ζ ^ (ut : ZMod p).val :=
    (IsPrimitiveRoot.autToPow_spec K hζ σ).symm
  exact ⟨ut, hut0, hσζ⟩

theorem map_Rpoly_of_cyclotomicAut
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (σ : L ≃ₐ[K] L) :
    MvPolynomial.map σ.toRingEquiv.toRingHom (Rpoly (p := p) ζ) =
      Rpoly (p := p) ζ := by
  obtain ⟨ut, hut0, hσζ⟩ := cyclotomicAut_power_spec ζ hζ σ
  by_cases hsq : IsSquare (ut : ZMod p)
  · exact map_Rpoly_of_square ζ hζ (ut : ZMod p) σ.toRingEquiv hut0 hsq hσζ
  · exact map_Rpoly_of_nonsquare ζ hζ (ut : ZMod p) σ.toRingEquiv hut0 hsq hσζ

theorem map_Dpoly_of_cyclotomicAut
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (σ : L ≃ₐ[K] L) :
    MvPolynomial.map σ.toRingEquiv.toRingHom (Dpoly (p := p) ζ) =
      Dpoly (p := p) ζ ∨
    MvPolynomial.map σ.toRingEquiv.toRingHom (Dpoly (p := p) ζ) =
      -(Dpoly (p := p) ζ) := by
  obtain ⟨ut, hut0, hσζ⟩ := cyclotomicAut_power_spec ζ hζ σ
  by_cases hsq : IsSquare (ut : ZMod p)
  · exact Or.inl (map_Dpoly_of_square ζ hζ (ut : ZMod p) σ.toRingEquiv hut0 hsq hσζ)
  · exact Or.inr (map_Dpoly_of_nonsquare ζ hζ (ut : ZMod p) σ.toRingEquiv hut0 hsq hσζ)

theorem map_Dpoly_sq_of_cyclotomicAut
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (σ : L ≃ₐ[K] L) :
    MvPolynomial.map σ.toRingEquiv.toRingHom (Dpoly (p := p) ζ ^ 2) =
      Dpoly (p := p) ζ ^ 2 := by
  obtain ⟨ut, hut0, hσζ⟩ := cyclotomicAut_power_spec ζ hζ σ
  by_cases hsq : IsSquare (ut : ZMod p)
  · exact map_Dpoly_sq_of_square ζ hζ (ut : ZMod p) σ.toRingEquiv hut0 hsq hσζ
  · exact map_Dpoly_sq_of_nonsquare ζ hζ (ut : ZMod p) σ.toRingEquiv hut0 hsq hσζ

end

end DkMath.NumberTheory.CyclotomicQRGaloisRealization
