/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.IdealPowerFactor
import DkMath.Lib.NumberTheory.PowerFactor

#print "file: DkMath.Lib.NumberTheory.PrincipalIdealPower"

open scoped nonZeroDivisors

/-!
# Neutral principal-ideal to element-power bridge

This module keeps principal-ideal comparison, class-group principalization,
and unit p-th-power absorption as separate layers.
-/

namespace DkMath.Lib.NumberTheory

/-- Equality of principal ideals is the element-level Associated relation. -/
theorem associated_of_span_singleton_eq_span_singleton
    {R : Type*} [CommRing R] [IsDomain R]
    {a b : R}
    (h : Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R)) :
    Associated a b := by
  exact (Ideal.span_singleton_eq_span_singleton).mp h

/-- Extract a generator and retain the unit in a principal ideal p-th power. -/
theorem exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI : I.IsPrincipal)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ u gamma : R,
      IsUnit u ∧
      Ideal.span ({gamma} : Set R) = I ∧
      a = u * gamma ^ p := by
  letI : I.IsPrincipal := hI
  let gamma : R := Submodule.IsPrincipal.generator I
  have hgamma : Ideal.span ({gamma} : Set R) = I := by
    exact Ideal.span_singleton_generator I
  have hprincipal : Ideal.span ({a} : Set R) = Ideal.span ({gamma ^ p} : Set R) := by
    calc
      Ideal.span ({a} : Set R) = I ^ p := hspan
      _ = Ideal.span ({gamma} : Set R) ^ p := by rw [hgamma]
      _ = Ideal.span ({gamma ^ p} : Set R) := by
        rw [Ideal.span_singleton_pow]
  have hassociated : Associated a (gamma ^ p) :=
    associated_of_span_singleton_eq_span_singleton hprincipal
  rcases hassociated with ⟨v, hv⟩
  refine ⟨↑(v⁻¹), gamma, (v⁻¹).isUnit, hgamma, ?_⟩
  calc
    a = a * (v : R) * ↑(v⁻¹) := by simp [mul_assoc]
    _ = gamma ^ p * ↑(v⁻¹) := by rw [hv]
    _ = ↑(v⁻¹) * gamma ^ p := by rw [mul_comm]

/-- The same principal ideal p-th power bridge, exposing only association. -/
theorem exists_associated_pow_of_span_eq_pow_of_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI : I.IsPrincipal)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ gamma : R,
      Ideal.span ({gamma} : Set R) = I ∧
      Associated a (gamma ^ p) := by
  letI : I.IsPrincipal := hI
  let gamma : R := Submodule.IsPrincipal.generator I
  have hgamma : Ideal.span ({gamma} : Set R) = I := by
    exact Ideal.span_singleton_generator I
  have hprincipal : Ideal.span ({a} : Set R) = Ideal.span ({gamma ^ p} : Set R) := by
    calc
      Ideal.span ({a} : Set R) = I ^ p := hspan
      _ = Ideal.span ({gamma} : Set R) ^ p := by rw [hgamma]
      _ = Ideal.span ({gamma ^ p} : Set R) := by
        rw [Ideal.span_singleton_pow]
  exact ⟨gamma, hgamma, associated_of_span_singleton_eq_span_singleton hprincipal⟩

/-- Principalize an ideal root using the Phase-15 class-group hypothesis. -/
theorem exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : classGroupPTorsionFreeAt R p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ u gamma : R,
      IsUnit u ∧
      Ideal.span ({gamma} : Set R) = I ∧
      a = u * gamma ^ p := by
  have hIPrincipal : I.IsPrincipal := by
    apply ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
      hI0 hfree
    rw [← hspan]
    exact ⟨a, rfl⟩
  exact exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal hIPrincipal hspan

/-- Exact p-th powers require the separate p-th-power unit-sector hypothesis. -/
theorem exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : classGroupPTorsionFreeAt R p)
    (hunit : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ delta : R, a = delta ^ p := by
  rcases exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      hI0 hfree hspan with ⟨u, gamma, hu, hgamma, ha⟩
  have hprincipal : Ideal.span ({a} : Set R) = Ideal.span ({gamma ^ p} : Set R) := by
    calc
      Ideal.span ({a} : Set R) = I ^ p := hspan
      _ = Ideal.span ({gamma} : Set R) ^ p := by rw [hgamma]
      _ = Ideal.span ({gamma ^ p} : Set R) := by
        rw [Ideal.span_singleton_pow]
  exact eq_pow_of_associated_pow_of_unit_pow_surjective
    (associated_of_span_singleton_eq_span_singleton hprincipal) hunit

end DkMath.Lib.NumberTheory
