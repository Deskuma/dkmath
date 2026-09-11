/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRCoefficientDescent
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral

#print "file: DkMath.NumberTheory.CyclotomicQRIntegralDescent"

namespace DkMath.NumberTheory.CyclotomicQRIntegralDescent

open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRCoefficientDescent

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable section

/-! ## Integral cyclotomic factor polynomials -/

theorem rootFactorPoly_integral
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (a : ZMod p) :
    IsIntegral (MvPolynomial (Fin 2) ℤ)
      (rootFactorPoly ζ a) := by
  have hroot : IsIntegral ℤ (ζ ^ a.val) :=
    (hζ.isIntegral (show 0 < p from (Fact.out : Nat.Prime p).pos)).pow _
  rw [MvPolynomial.isIntegral_iff_isIntegral_coeff]
  intro d
  classical
  simp only [rootFactorPoly, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  by_cases h0 : Finsupp.single (0 : Fin 2) 1 = d
  · subst d
    have h10 : ¬Finsupp.single (1 : Fin 2) 1 = Finsupp.single (0 : Fin 2) 1 := by
      intro h
      have h' : (1 : Fin 2) = 0 :=
        (Finsupp.single_left_injective (M := ℕ) one_ne_zero) h
      omega
    simpa [h10] using (isIntegral_one : IsIntegral ℤ (1 : L))
  · by_cases h1 : Finsupp.single (1 : Fin 2) 1 = d
    · subst d
      have h01 : ¬Finsupp.single (0 : Fin 2) 1 = Finsupp.single (1 : Fin 2) 1 := by
        intro h
        have h' : (0 : Fin 2) = 1 :=
          (Finsupp.single_left_injective (M := ℕ) one_ne_zero) h
        omega
      simpa [h01] using hroot.neg
    · simpa [h0, h1] using (isIntegral_zero : IsIntegral ℤ (0 : L))

theorem qrFactorPoly_integral
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    IsIntegral (MvPolynomial (Fin 2) ℤ)
      (qrFactorPoly (p := p) ζ) := by
  classical
  unfold qrFactorPoly
  exact IsIntegral.prod _ fun a _ ↦ rootFactorPoly_integral ζ hζ a

theorem qnrFactorPoly_integral
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    IsIntegral (MvPolynomial (Fin 2) ℤ)
      (qnrFactorPoly (p := p) ζ) := by
  classical
  unfold qnrFactorPoly
  exact IsIntegral.prod _ fun a _ ↦ rootFactorPoly_integral ζ hζ a

theorem Rpoly_integral
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    IsIntegral (MvPolynomial (Fin 2) ℤ)
      (Rpoly (p := p) ζ) := by
  simpa [Rpoly] using
    (qrFactorPoly_integral ζ hζ).add (qnrFactorPoly_integral ζ hζ)

theorem Dpoly_sq_integral
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    IsIntegral (MvPolynomial (Fin 2) ℤ)
      (Dpoly (p := p) ζ ^ 2) := by
  simpa [Dpoly] using
    ((qrFactorPoly_integral ζ hζ).sub (qnrFactorPoly_integral ζ hζ)).pow 2

theorem coeff_Rpoly_isIntegral_int
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (d : Fin 2 →₀ ℕ) :
    IsIntegral ℤ (MvPolynomial.coeff d (Rpoly (p := p) ζ)) :=
  (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp (Rpoly_integral ζ hζ)) d

theorem coeff_Dpoly_sq_isIntegral_int
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (d : Fin 2 →₀ ℕ) :
    IsIntegral ℤ (MvPolynomial.coeff d (Dpoly (p := p) ζ ^ 2)) :=
  (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp (Dpoly_sq_integral ζ hζ)) d

/-! ## Rational coefficients mapped into an integral cyclotomic extension -/

theorem isIntegral_rat_of_map_isIntegral
    {L : Type*} [Field L] [Algebra ℚ L]
    (q : ℚ) (c : L) (hq : algebraMap ℚ L q = c)
    (hc : IsIntegral ℤ c) :
    IsIntegral ℤ q := by
  apply (isIntegral_algebraMap_iff
    (FaithfulSMul.algebraMap_injective ℚ L)).mp
  rw [hq]
  exact hc

theorem coeff_R0_isIntegral_int
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (R0 : MvPolynomial (Fin 2) ℚ)
    (hR0 : MvPolynomial.map (algebraMap ℚ L) R0 = Rpoly (p := p) ζ)
    (d : Fin 2 →₀ ℕ) :
    IsIntegral ℤ (MvPolynomial.coeff d R0) := by
  apply isIntegral_rat_of_map_isIntegral (L := L) (MvPolynomial.coeff d R0)
    (MvPolynomial.coeff d (Rpoly (p := p) ζ))
  · calc
      algebraMap ℚ L (MvPolynomial.coeff d R0) =
          MvPolynomial.coeff d (MvPolynomial.map (algebraMap ℚ L) R0) := by
            symm
            exact MvPolynomial.coeff_map (algebraMap ℚ L) R0 d
      _ = MvPolynomial.coeff d (Rpoly (p := p) ζ) := by rw [hR0]
  · exact coeff_Rpoly_isIntegral_int ζ hζ d

theorem coeff_D20_isIntegral_int
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (D20 : MvPolynomial (Fin 2) ℚ)
    (hD20 : MvPolynomial.map (algebraMap ℚ L) D20 =
      Dpoly (p := p) ζ ^ 2)
    (d : Fin 2 →₀ ℕ) :
    IsIntegral ℤ (MvPolynomial.coeff d D20) := by
  apply isIntegral_rat_of_map_isIntegral (L := L) (MvPolynomial.coeff d D20)
    (MvPolynomial.coeff d (Dpoly (p := p) ζ ^ 2))
  · calc
      algebraMap ℚ L (MvPolynomial.coeff d D20) =
          MvPolynomial.coeff d (MvPolynomial.map (algebraMap ℚ L) D20) := by
            symm
            exact MvPolynomial.coeff_map (algebraMap ℚ L) D20 d
      _ = MvPolynomial.coeff d (Dpoly (p := p) ζ ^ 2) := by rw [hD20]
  · exact coeff_Dpoly_sq_isIntegral_int ζ hζ d

/-! ## Rational integral elements are integer casts -/

theorem rat_isIntegral_iff_exists_int (q : ℚ) :
    IsIntegral ℤ q ↔ ∃ z : ℤ, (algebraMap ℤ ℚ) z = q := by
  simpa using (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ) (x := q))

theorem coeff_R0_mem_range_intCast
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (R0 : MvPolynomial (Fin 2) ℚ)
    (hR0 : MvPolynomial.map (algebraMap ℚ L) R0 = Rpoly (p := p) ζ)
    (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d R0 ∈ Set.range (algebraMap ℤ ℚ) :=
  (rat_isIntegral_iff_exists_int _).mp
    (coeff_R0_isIntegral_int ζ hζ R0 hR0 d)

theorem coeff_D20_mem_range_intCast
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (D20 : MvPolynomial (Fin 2) ℚ)
    (hD20 : MvPolynomial.map (algebraMap ℚ L) D20 =
      Dpoly (p := p) ζ ^ 2)
    (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d D20 ∈ Set.range (algebraMap ℤ ℚ) :=
  (rat_isIntegral_iff_exists_int _).mp
    (coeff_D20_isIntegral_int ζ hζ D20 hD20 d)

/-! ## Whole-polynomial integer descent -/

theorem exists_Rpoly_over_int
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ RZ : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ L) RZ = Rpoly (p := p) ζ := by
  obtain ⟨R0, hR0⟩ := exists_Rpoly_over_base (K := ℚ) ζ hζ
  have hR0range : R0 ∈ Set.range (MvPolynomial.map (algebraMap ℤ ℚ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨d, hd, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact coeff_R0_mem_range_intCast ζ hζ R0 hR0 d
  obtain ⟨RZ, hRZ⟩ := hR0range
  refine ⟨RZ, ?_⟩
  calc
    MvPolynomial.map (algebraMap ℤ L) RZ =
        MvPolynomial.map (algebraMap ℚ L)
          (MvPolynomial.map (algebraMap ℤ ℚ) RZ) := by
      rw [MvPolynomial.map_map, IsScalarTower.algebraMap_eq ℤ ℚ L]
    _ = MvPolynomial.map (algebraMap ℚ L) R0 := by rw [hRZ]
    _ = Rpoly (p := p) ζ := hR0

theorem exists_Dpoly_sq_over_int
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ D2Z : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ L) D2Z = Dpoly (p := p) ζ ^ 2 := by
  obtain ⟨D20, hD20⟩ := exists_Dpoly_sq_over_base (K := ℚ) ζ hζ
  have hD20range : D20 ∈ Set.range (MvPolynomial.map (algebraMap ℤ ℚ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨d, hd, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact coeff_D20_mem_range_intCast ζ hζ D20 hD20 d
  obtain ⟨D2Z, hD2Z⟩ := hD20range
  refine ⟨D2Z, ?_⟩
  calc
    MvPolynomial.map (algebraMap ℤ L) D2Z =
        MvPolynomial.map (algebraMap ℚ L)
          (MvPolynomial.map (algebraMap ℤ ℚ) D2Z) := by
      rw [MvPolynomial.map_map, IsScalarTower.algebraMap_eq ℤ ℚ L]
    _ = MvPolynomial.map (algebraMap ℚ L) D20 := by rw [hD2Z]
    _ = Dpoly (p := p) ζ ^ 2 := hD20

end

end DkMath.NumberTheory.CyclotomicQRIntegralDescent
