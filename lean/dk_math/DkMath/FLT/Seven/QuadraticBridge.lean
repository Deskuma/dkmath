/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.NumberTheory.TraceOneQuadratic

#print "file: DkMath.FLT.Seven.QuadraticBridge"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- The homogeneous seventh cyclotomic kernel over the integers. -/
def cyclotomicSeven (z y : ℤ) : ℤ :=
  z ^ 6 + z ^ 5 * y + z ^ 4 * y ^ 2 + z ^ 3 * y ^ 3
    + z ^ 2 * y ^ 4 + z * y ^ 5 + y ^ 6

/-- First cubic coordinate of the seventh cyclotomic kernel. -/
def cyclotomicSevenFst (z y : ℤ) : ℤ :=
  z ^ 3 + z ^ 2 * y - y ^ 3

/-- Second cubic coordinate of the seventh cyclotomic kernel. -/
def cyclotomicSevenSnd (z y : ℤ) : ℤ :=
  -z ^ 2 * y - z * y ^ 2

/-- The seventh cyclotomic kernel packaged in the discriminant `-7` order. -/
def cyclotomicSevenToTraceOne (z y : ℤ) : TraceOneInt (-2) :=
  ⟨cyclotomicSevenFst z y, cyclotomicSevenSnd z y⟩

@[simp] theorem cyclotomicSevenToTraceOne_fst (z y : ℤ) :
    (cyclotomicSevenToTraceOne z y).fst = cyclotomicSevenFst z y := rfl

@[simp] theorem cyclotomicSevenToTraceOne_snd (z y : ℤ) :
    (cyclotomicSevenToTraceOne z y).snd = cyclotomicSevenSnd z y := rfl

/-- The seventh homogeneous cyclotomic kernel is the `s = -2` norm of its
explicit cubic coordinate pair. -/
theorem cyclotomicSeven_eq_traceOneNorm_negTwo (z y : ℤ) :
    cyclotomicSeven z y = tqNorm (cyclotomicSevenToTraceOne z y) := by
  simp [cyclotomicSeven, cyclotomicSevenToTraceOne, cyclotomicSevenFst,
    cyclotomicSevenSnd, DkMath.NumberTheory.TraceOneQuadratic.norm]
  ring

/-- Standard factorization of a difference of seventh powers. -/
theorem seventh_pow_sub_pow_eq_sub_mul_cyclotomicSeven (z y : ℤ) :
    z ^ 7 - y ^ 7 = (z - y) * cyclotomicSeven z y := by
  simp [cyclotomicSeven]
  ring

/-- The generic `GN` coordinate uses gap `a-b` and base `b`, hence endpoint
`(a-b)+b=a`; the norm coordinates are evaluated at the endpoints `(a,b)`. -/
theorem GN_seven_sub_eq_traceOneNorm_negTwo
    (a b : ℕ) (hab : b ≤ a) :
    ((GN 7 (a - b) b : ℕ) : ℤ) =
      tqNorm (cyclotomicSevenToTraceOne (a : ℤ) (b : ℤ)) := by
  rw [← cyclotomicSeven_eq_traceOneNorm_negTwo]
  rw [GN_eq_sum]
  norm_num [Finset.sum_range_succ, Nat.choose, cyclotomicSeven]
  zify [hab]
  ring

/-- The two cubic coordinates vanish simultaneously only at the origin. -/
theorem cyclotomicSeven_coordinates_eq_zero_iff (z y : ℤ) :
    cyclotomicSevenFst z y = 0 ∧ cyclotomicSevenSnd z y = 0 ↔
      z = 0 ∧ y = 0 := by
  constructor
  · rintro ⟨hfst, hsnd⟩
    have hsnd_formula :
        cyclotomicSevenSnd z y = -(z * y * (z + y)) := by
      simp [cyclotomicSevenSnd]
      ring
    have hfactor : z * y * (z + y) = 0 := by
      rw [hsnd_formula] at hsnd
      exact neg_eq_zero.mp hsnd
    rcases mul_eq_zero.mp hfactor with hzy | hsum
    · rcases mul_eq_zero.mp hzy with hz | hy
      · subst z
        have : y ^ 3 = 0 := by simpa [cyclotomicSevenFst] using hfst
        exact ⟨rfl, eq_zero_of_pow_eq_zero this⟩
      · subst y
        have : z ^ 3 = 0 := by simpa [cyclotomicSevenFst] using hfst
        exact ⟨eq_zero_of_pow_eq_zero this, rfl⟩
    · have hz : z = -y := by omega
      rw [hz] at hfst
      simp only [cyclotomicSevenFst] at hfst
      ring_nf at hfst
      have hy : y = 0 := eq_zero_of_pow_eq_zero (neg_eq_zero.mp hfst)
      subst y
      simpa using hz
  · rintro ⟨rfl, rfl⟩
    norm_num [cyclotomicSevenFst, cyclotomicSevenSnd]

/-- The seventh cyclotomic norm vanishes only at the zero endpoint pair. -/
theorem cyclotomicSeven_eq_zero_iff (z y : ℤ) :
    cyclotomicSeven z y = 0 ↔ z = 0 ∧ y = 0 := by
  rw [cyclotomicSeven_eq_traceOneNorm_negTwo,
    norm_eq_zero_iff_of_negTwo]
  constructor
  · intro h
    apply (cyclotomicSeven_coordinates_eq_zero_iff z y).mp
    exact ⟨congrArg TraceOneInt.fst h, congrArg TraceOneInt.snd h⟩
  · intro h
    rcases (cyclotomicSeven_coordinates_eq_zero_iff z y).mpr h with ⟨hf, hs⟩
    apply traceOne_ext <;> simpa [cyclotomicSevenToTraceOne]

/-- In the strictly positive natural chamber, all seven monomials contribute
at least one. -/
theorem seven_le_cyclotomicSeven_nat
    (z y : ℕ) (hz : 0 < z) (hy : 0 < y) :
    7 ≤ z ^ 6 + z ^ 5 * y + z ^ 4 * y ^ 2 + z ^ 3 * y ^ 3
      + z ^ 2 * y ^ 4 + z * y ^ 5 + y ^ 6 := by
  have hz0 : z ≠ 0 := Nat.ne_of_gt hz
  have hy0 : y ≠ 0 := Nat.ne_of_gt hy
  have h1 : 1 ≤ z ^ 6 := Nat.one_le_pow 6 z hz
  have h2 : 1 ≤ z ^ 5 * y :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero 5 hz0) hy0)
  have h3 : 1 ≤ z ^ 4 * y ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero 4 hz0) (pow_ne_zero 2 hy0))
  have h4 : 1 ≤ z ^ 3 * y ^ 3 :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 hz0) (pow_ne_zero 3 hy0))
  have h5 : 1 ≤ z ^ 2 * y ^ 4 :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hz0) (pow_ne_zero 4 hy0))
  have h6 : 1 ≤ z * y ^ 5 :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hz0 (pow_ne_zero 5 hy0))
  have h7 : 1 ≤ y ^ 6 := Nat.one_le_pow 6 y hy
  omega

end DkMath.FLT.Seven
