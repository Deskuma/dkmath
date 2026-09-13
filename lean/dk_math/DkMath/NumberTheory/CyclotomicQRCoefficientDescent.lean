/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRGaloisRealization
import Mathlib.FieldTheory.Galois.Basic

#print "file: DkMath.NumberTheory.CyclotomicQRCoefficientDescent"

namespace DkMath.NumberTheory.CyclotomicQRCoefficientDescent

open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRGaloisRealization

noncomputable section

/-! ## Coefficientwise fixedness -/

theorem coeff_fixed_of_map_eq
    {L : Type*} [CommSemiring L]
    (σ : L →+* L) {P : MvPolynomial (Fin 2) L}
    (hP : MvPolynomial.map σ P = P) (d : Fin 2 →₀ ℕ) :
    σ (MvPolynomial.coeff d P) = MvPolynomial.coeff d P := by
  calc
    σ (MvPolynomial.coeff d P) = MvPolynomial.coeff d (MvPolynomial.map σ P) := by
      symm
      exact MvPolynomial.coeff_map σ P d
    _ = MvPolynomial.coeff d P := by rw [hP]

/-! ## Fixed-field membership of the Phase-9 coefficient targets -/

theorem coeff_Rpoly_mem_fixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (Rpoly (p := p) ζ) ∈
      IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ _
  exact coeff_fixed_of_map_eq σ.toRingEquiv.toRingHom
    (map_Rpoly_of_cyclotomicAut ζ hζ σ) d

theorem coeff_Dpoly_sq_mem_fixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (Dpoly (p := p) ζ ^ 2) ∈
      IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ _
  exact coeff_fixed_of_map_eq σ.toRingEquiv.toRingHom
    (map_Dpoly_sq_of_cyclotomicAut ζ hζ σ) d

/-! ## Fixed-field membership as base-field range membership -/

private theorem finiteDimensional_cyclotomic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L] :
    FiniteDimensional K L :=
  IsCyclotomicExtension.finiteDimensional {p} K L

theorem coeff_Rpoly_mem_range_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (Rpoly (p := p) ζ) ∈
      Set.range (algebraMap K L) := by
  letI : IsGalois K L := IsCyclotomicExtension.isGalois {p} K L
  letI : FiniteDimensional K L := finiteDimensional_cyclotomic (p := p)
  apply (IsGalois.mem_range_algebraMap_iff_fixed
    (MvPolynomial.coeff d (Rpoly (p := p) ζ))).2
  intro σ
  exact coeff_fixed_of_map_eq σ.toRingEquiv.toRingHom
    (map_Rpoly_of_cyclotomicAut ζ hζ σ) d

theorem coeff_Dpoly_sq_mem_range_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (Dpoly (p := p) ζ ^ 2) ∈
      Set.range (algebraMap K L) := by
  letI : IsGalois K L := IsCyclotomicExtension.isGalois {p} K L
  letI : FiniteDimensional K L := finiteDimensional_cyclotomic (p := p)
  apply (IsGalois.mem_range_algebraMap_iff_fixed
    (MvPolynomial.coeff d (Dpoly (p := p) ζ ^ 2))).2
  intro σ
  exact coeff_fixed_of_map_eq σ.toRingEquiv.toRingHom
    (map_Dpoly_sq_of_cyclotomicAut ζ hζ σ) d

/-! ## Whole-polynomial descent -/

theorem exists_Rpoly_over_base
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ R0 : MvPolynomial (Fin 2) K,
      MvPolynomial.map (algebraMap K L) R0 = Rpoly (p := p) ζ := by
  change Rpoly (p := p) ζ ∈ Set.range (MvPolynomial.map (algebraMap K L))
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  intro c hc
  obtain ⟨d, hd, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  exact coeff_Rpoly_mem_range_algebraMap ζ hζ d

theorem exists_Dpoly_sq_over_base
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ D20 : MvPolynomial (Fin 2) K,
      MvPolynomial.map (algebraMap K L) D20 = Dpoly (p := p) ζ ^ 2 := by
  change Dpoly (p := p) ζ ^ 2 ∈ Set.range (MvPolynomial.map (algebraMap K L))
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  intro c hc
  obtain ⟨d, hd, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  exact coeff_Dpoly_sq_mem_range_algebraMap ζ hζ d

end

end DkMath.NumberTheory.CyclotomicQRCoefficientDescent
