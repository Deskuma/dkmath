/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Lib.NumberTheory.PowerFactor"

/-!
# Coprime power-factor splitting

This module contains the generic natural-number wrapper around Mathlib's
`exists_eq_pow_of_mul_eq_pow`.  It is independent of FLT and of any fixed
exponent.
-/

namespace DkMath.Lib.NumberTheory

/-- Coprime factors of a power are associated to powers with the same exponent.

The pinned Mathlib API uses `CommMonoidWithZero` together with `GCDMonoid`; the
latter supplies the multiplicative cancellation needed by the extraction
theorem.  No unit classification and no fixed exponent are used here. -/
theorem associated_prime_power_of_coprime_mul_eq_pow
    {R : Type*} [CommMonoidWithZero R] [GCDMonoid R]
    {p : ℕ} {x y z : R}
    (hcop : IsUnit (gcd x y)) (hpow : x * y = z ^ p) :
    ∃ gamma : R, Associated x (gamma ^ p) := by
  rcases exists_associated_pow_of_mul_eq_pow hcop hpow with ⟨gamma, hgamma⟩
  exact ⟨gamma, hgamma.symm⟩

/-- Absorb an associated unit when the p-th power map is surjective on units.

This is deliberately separate from coprime-factor extraction: for a concrete
quadratic order, the displayed unit-surjectivity hypothesis is the entire
unit-sector obligation. -/
theorem eq_pow_of_associated_pow_of_unit_pow_surjective
    {R : Type*} [CommMonoidWithZero R]
    {p : ℕ} {x gamma : R}
    (hassoc : Associated x (gamma ^ p))
    (hsurj : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p) :
    ∃ delta : R, x = delta ^ p := by
  rcases hassoc with ⟨u, hu⟩
  rcases hsurj u with ⟨e, he⟩
  refine ⟨gamma * (↑(e⁻¹ : Rˣ) : R), ?_⟩
  apply (e ^ p).mul_left_inj.mp
  calc
    x * (↑(e : Rˣ) : R) ^ p = x * (u : R) := by
      simpa using congrArg (fun v : Rˣ => x * (v : R)) he.symm
    _ = gamma ^ p := hu
    _ = (gamma * (↑(e⁻¹ : Rˣ) : R)) ^ p *
        (↑(e : Rˣ) : R) ^ p := by
      symm
      rw [← mul_pow]
      simp [mul_assoc]

/-- Coprime factors of a power are powers with the same exponent. -/
theorem power_factor_split
    {d a b x : ℕ}
    (hcop : Nat.Coprime a b)
    (hbody : a * b = x ^ d) :
    (∃ u : ℕ, a = u ^ d) ∧ (∃ v : ℕ, b = v ^ d) := by
  have hunit : IsUnit (GCDMonoid.gcd a b) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
  constructor
  · exact exists_eq_pow_of_mul_eq_pow hunit hbody
  · have hunit' : IsUnit (GCDMonoid.gcd b a) := by
      simpa [gcd_comm] using hunit
    exact exists_eq_pow_of_mul_eq_pow hunit' (by simpa [mul_comm] using hbody)

end DkMath.Lib.NumberTheory
