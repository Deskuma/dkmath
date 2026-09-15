/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Lib.NumberTheory.IdealPowerFactor"

/-!
# Neutral ideal power and class-group kernel

This module isolates the ideal/class-group layer from FLT and Kummer
receivers.  Element-level unit absorption remains a separate obligation.
-/

open scoped nonZeroDivisors

namespace DkMath.Lib.NumberTheory

/-! ### Class-group p-torsion -/

/-- The class group has no nontrivial `p`-torsion. -/
def classGroupPTorsionFreeAt (R : Type*) (p : ℕ)
    [CommRing R] [IsDomain R] : Prop :=
  ∀ a : ClassGroup R, a ^ p = 1 → a = 1

/-- Eliminate a class-group `p`-torsion witness under `classGroupPTorsionFreeAt`. -/
theorem classGroup_eq_one_of_pow_eq_one_of_classGroupPTorsionFreeAt
    {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    (hfree : classGroupPTorsionFreeAt R p) {a : ClassGroup R}
    (hpow : a ^ p = 1) : a = 1 := by
  exact hfree a hpow

/-! ### Principalization -/

/-- A nonzero integral ideal with trivial class is principal. -/
theorem ideal_isPrincipal_of_classGroup_eq_one
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ∈ (Ideal R)⁰)
    (hclass : ClassGroup.mk0 ⟨I, hI⟩ = 1) : I.IsPrincipal := by
  exact (ClassGroup.mk0_eq_one_iff hI).mp hclass

/-- A class-group `p`-torsion witness principalizes under `p`-torsion-freeness. -/
theorem ideal_isPrincipal_of_classGroupPTorsionFreeAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ∈ (Ideal R)⁰) {p : ℕ}
    (hfree : classGroupPTorsionFreeAt R p)
    (hpow : ClassGroup.mk0 ⟨I, hI⟩ ^ p = 1) : I.IsPrincipal := by
  exact ideal_isPrincipal_of_classGroup_eq_one hI (hfree _ hpow)

/-- If `I^p` is principal, `p`-torsion-freeness makes `I` principal. -/
theorem ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ∈ (Ideal R)⁰) {p : ℕ}
    (hfree : classGroupPTorsionFreeAt R p)
    (hIPrincipal : (I ^ p).IsPrincipal) : I.IsPrincipal := by
  have hIp : I ^ p ∈ (Ideal R)⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact pow_ne_zero p (mem_nonZeroDivisors_iff_ne_zero.mp hI)
  have hclass : ClassGroup.mk0 ⟨I, hI⟩ ^ p = 1 := by
    calc
      ClassGroup.mk0 ⟨I, hI⟩ ^ p = ClassGroup.mk0 (⟨I, hI⟩ ^ p) := by
        rw [← MonoidHom.map_pow]
      _ = ClassGroup.mk0 ⟨I ^ p, hIp⟩ := by rfl
      _ = 1 := (ClassGroup.mk0_eq_one_iff hIp).2 hIPrincipal
  exact ideal_isPrincipal_of_classGroupPTorsionFreeAt hI hfree hclass

/-! ### Coprime ideal factor extraction -/

/-- Extract an ideal `p`-th power from one factor of a coprime ideal product. -/
theorem exists_eq_pow_of_isCoprime_mul_eq_pow
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J K : Ideal R} {p : ℕ}
    (hcop : IsCoprime I J) (hpow : I * J = K ^ p) :
    ∃ A : Ideal R, I = A ^ p := by
  have hgcd : gcd I J = 1 := (Ideal.isCoprime_iff_gcd).mp hcop
  have hunit : IsUnit (gcd I J) := by
    rw [hgcd]
    exact isUnit_one
  exact exists_eq_pow_of_mul_eq_pow hunit hpow

/-- Extract the symmetric ideal `p`-th power from a coprime ideal product. -/
theorem exists_eq_pow_of_isCoprime_mul_eq_pow_right
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J K : Ideal R} {p : ℕ}
    (hcop : IsCoprime I J) (hpow : I * J = K ^ p) :
    ∃ B : Ideal R, J = B ^ p := by
  exact exists_eq_pow_of_isCoprime_mul_eq_pow hcop.symm (by simpa [mul_comm] using hpow)

/-- Extract both ideal `p`-th powers from a coprime ideal product. -/
theorem exists_eq_pow_of_isCoprime_mul_eq_pow_pair
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J K : Ideal R} {p : ℕ}
    (hcop : IsCoprime I J) (hpow : I * J = K ^ p) :
    (∃ A : Ideal R, I = A ^ p) ∧ (∃ B : Ideal R, J = B ^ p) := by
  exact ⟨exists_eq_pow_of_isCoprime_mul_eq_pow hcop hpow,
    exists_eq_pow_of_isCoprime_mul_eq_pow_right hcop hpow⟩

end DkMath.Lib.NumberTheory
