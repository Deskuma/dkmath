/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadraticField
import DkMath.Lib.NumberTheory.UnitPowerSector

#print "file: DkMath.NumberTheory.TraceOnePrimeUnitSectors"

/-!
# Unit sectors for prime-discriminant TraceOne orders

This module proves the imaginary quadratic unit collapse for primes at least
seven.  The real quadratic Dirichlet-sector construction is intentionally not
asserted here until the explicit quadratic signature bridge is available.
-/

namespace DkMath.NumberTheory.TraceOnePrimeUnitSectors

open scoped nonZeroDivisors

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

private theorem discr_signedPrimeParameter_eq_neg
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 3) :
    discr (signedPrimeParameter p) = -(p : ℤ) := by
  rw [discr_signedPrimeParameter hp (by omega)]
  simp [signedPrimeDiscriminant, hmod]

private theorem traceOnePrimeImaginary_norm_pos
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    (x : TraceOneInt (signedPrimeParameter p)) (hx : x ≠ 0) :
    0 < norm x := by
  have hD := discr_signedPrimeParameter_eq_neg hp hmod
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  rcases x with ⟨a, b⟩
  have hsum :
      4 * norm (⟨a, b⟩ : TraceOneInt (signedPrimeParameter p)) =
        (2 * a + b) ^ 2 + (p : ℤ) * b ^ 2 := by
    rw [four_mul_traceOneNorm_eq_discriminant, hD]
    simp [trace]
  have hnonneg :
      0 ≤ norm (⟨a, b⟩ : TraceOneInt (signedPrimeParameter p)) := by
    nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  have hne :
      norm (⟨a, b⟩ : TraceOneInt (signedPrimeParameter p)) ≠ 0 := by
    intro hn
    have hsum0 : (2 * a + b) ^ 2 + (p : ℤ) * b ^ 2 = 0 := by
      nlinarith [hsum]
    have hb : b = 0 := by
      nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
    have ha : a = 0 := by
      rw [hb] at hsum0
      nlinarith [sq_nonneg a]
    apply hx
    apply traceOne_ext <;> simp [ha, hb]
  omega

private theorem traceOnePrimeImaginary_norm_eq_one_of_isUnit
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    (x : TraceOneInt (signedPrimeParameter p)) (hx : IsUnit x) :
    norm x = 1 := by
  obtain ⟨y, hxy⟩ := isUnit_iff_exists_inv.mp hx
  have hy : IsUnit y := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨x, by simpa [mul_comm] using hxy⟩
  have hprod : norm x * norm y = 1 := by
    rw [← traceOne_norm_mul, hxy]
    norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm]
  have hx0 : x ≠ 0 := by
    intro hx0
    have hzero : (0 : TraceOneInt (signedPrimeParameter p)) = 1 := by
      simpa [hx0] using hxy
    have hfst := congrArg TraceOneInt.fst hzero
    norm_num at hfst
  have hy0 : y ≠ 0 := by
    intro hy0
    have hzero : (0 : TraceOneInt (signedPrimeParameter p)) = 1 := by
      simpa [hy0] using hxy
    have hfst := congrArg TraceOneInt.fst hzero
    norm_num at hfst
  have hxpos := traceOnePrimeImaginary_norm_pos hp hp7 hmod x hx0
  have hypos := traceOnePrimeImaginary_norm_pos hp hp7 hmod y hy0
  rcases (Int.mul_eq_one_iff_eq_one_or_neg_one).mp hprod with h | h
  · exact h.1
  · nlinarith [hxpos, h.1]

private theorem traceOnePrimeImaginary_eq_one_or_neg_one_of_norm_eq_one
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    {x : TraceOneInt (signedPrimeParameter p)}
    (hx : norm x = 1) :
    x = 1 ∨ x = -1 := by
  have hD := discr_signedPrimeParameter_eq_neg hp hmod
  have hpz : (7 : ℤ) ≤ p := by exact_mod_cast hp7
  rcases x with ⟨a, b⟩
  have hsum :
      4 * norm (⟨a, b⟩ : TraceOneInt (signedPrimeParameter p)) =
        (2 * a + b) ^ 2 + (p : ℤ) * b ^ 2 := by
    rw [four_mul_traceOneNorm_eq_discriminant, hD]
    simp [trace]
  rw [hx] at hsum
  have hb_sq_lt : b ^ 2 < 1 := by
    nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  have hb : b = 0 := by
    nlinarith [sq_nonneg b]
  have hfactor : (a - 1) * (a + 1) = 0 := by
    rw [hb] at hsum
    nlinarith
  rcases mul_eq_zero.mp hfactor with ha | ha
  · left
    have ha' : a = 1 := by omega
    apply traceOne_ext <;> simp [ha', hb]
  · right
    have ha' : a = -1 := by omega
    apply traceOne_ext <;> simp [ha', hb]

/-- For `p >= 7` in the `p % 4 = 3` branch, every unit is a sign. -/
theorem traceOnePrimeImaginary_unit_eq_one_or_neg_one
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    (u : (TraceOneInt (signedPrimeParameter p))ˣ) :
    (u : TraceOneInt (signedPrimeParameter p)) = 1 ∨
      (u : TraceOneInt (signedPrimeParameter p)) = -1 := by
  exact traceOnePrimeImaginary_eq_one_or_neg_one_of_norm_eq_one hp hp7 hmod
    (traceOnePrimeImaginary_norm_eq_one_of_isUnit hp hp7 hmod (u : _) u.isUnit)

private theorem traceOnePrimeImaginary_unit_pow_surjective
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
    ∀ u : (TraceOneInt (signedPrimeParameter p))ˣ,
      ∃ e : (TraceOneInt (signedPrimeParameter p))ˣ, u = e ^ p := by
  intro u
  rcases traceOnePrimeImaginary_unit_eq_one_or_neg_one hp hp7 hmod u with h | h
  · refine ⟨1, ?_⟩
    apply Units.ext
    simpa using h
  · refine ⟨-1, ?_⟩
    apply Units.ext
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    simpa [Units.val_pow_eq_pow_val, hpodd.neg_pow] using h

/-- The imaginary prime-discriminant branch has a singleton unit sector. -/
def traceOnePrimeImaginarySingletonSectorSystem
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter p)) p :=
  singletonUnitPowerSectorSystem
    (traceOnePrimeImaginary_unit_pow_surjective hp hp7 hmod)

/-- Conditional exact-power extraction for the imaginary branch. -/
theorem traceOnePrimeImaginary_exists_eq_pow_of_span_eq_pow
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp (by omega)⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain hp (by omega)
    ∀ {I : Ideal (TraceOneInt (signedPrimeParameter p))}
      {a : TraceOneInt (signedPrimeParameter p)},
      I ∈ (Ideal (TraceOneInt (signedPrimeParameter p)))⁰ →
      classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      Ideal.span ({a} : Set (TraceOneInt (signedPrimeParameter p))) = I ^ p →
      ∃ delta : TraceOneInt (signedPrimeParameter p), a = delta ^ p := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp (by omega)⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain hp (by omega)
  intro I a hI0 hfree hspan
  exact exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt_of_unit_pow_surjective
    hI0 hfree (traceOnePrimeImaginary_unit_pow_surjective hp hp7 hmod) hspan

end DkMath.NumberTheory.TraceOnePrimeUnitSectors
