/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.KUS.StructuralRatio"

namespace DkMath.KUS

/-!
# Structural self-ratio

This module separates ordinary field division from a ratio whose numerator and
denominator are known to come from the same source expression.

The structural value is `1` even when the evaluated source value is `0`.  This
does not redefine ordinary field division: over a field, `0 / 0` remains `0`.
The bridge to ordinary division is available only when the denominator is
nonzero.
-/

/-- A numerator and denominator together with evidence that they are the same source. -/
structure StructuralRatioWitness (α : Type*) where
  numerator : α
  denominator : α
  same_source : numerator = denominator

namespace StructuralRatioWitness

/-- Canonical witness for the self-ratio of one source expression. -/
def self {α : Type*} (x : α) : StructuralRatioWitness α where
  numerator := x
  denominator := x
  same_source := rfl

/-- Structural evaluation: identical source divided by itself has unit value. -/
def value {α : Type*} [One α] (_r : StructuralRatioWitness α) : α :=
  1

@[simp] theorem self_numerator {α : Type*} (x : α) :
    (self x).numerator = x := by
  rfl

@[simp] theorem self_denominator {α : Type*} (x : α) :
    (self x).denominator = x := by
  rfl

@[simp] theorem value_eq_one
    {α : Type*} [One α] (r : StructuralRatioWitness α) :
    r.value = 1 := by
  rfl

/-- Away from zero, structural evaluation agrees with ordinary field division. -/
theorem value_eq_div_of_denominator_ne
    {K : Type*} [DivisionRing K]
    (r : StructuralRatioWitness K)
    (hden : r.denominator ≠ 0) :
    r.value = r.numerator / r.denominator := by
  change 1 = r.numerator / r.denominator
  rw [r.same_source]
  exact (div_self hden).symm

end StructuralRatioWitness

/--
Evidence that an ordinary quotient is defined in the nonzero-denominator value
layer.  Unlike `StructuralRatioWitness`, this proposition does not assign a
value at a collapsed denominator.
-/
structure DefinedRatioWitness
    (K : Type*) [Zero K]
    (numerator denominator : K) : Prop where
  denominator_ne : denominator ≠ 0

namespace DefinedRatioWitness

/-- Construct a defined-ratio witness from a nonzero-denominator proof. -/
theorem of_denominator_ne
    {K : Type*} [Zero K]
    {numerator denominator : K}
    (hden : denominator ≠ 0) :
    DefinedRatioWitness K numerator denominator where
  denominator_ne := hden

/-- Ordinary quotient value carried by a defined-ratio witness. -/
def value
    {K : Type*} [Zero K] [Div K]
    {numerator denominator : K}
    (_r : DefinedRatioWitness K numerator denominator) : K :=
  numerator / denominator

@[simp] theorem value_eq_div
    {K : Type*} [Zero K] [Div K]
    {numerator denominator : K}
    (r : DefinedRatioWitness K numerator denominator) :
    r.value = numerator / denominator := by
  rfl

/-- The ordinary quotient is defined exactly when its denominator is nonzero. -/
theorem defined_iff_denominator_ne
    {K : Type*} [Zero K]
    (numerator denominator : K) :
    DefinedRatioWitness K numerator denominator ↔ denominator ≠ 0 := by
  constructor
  · intro r
    exact r.denominator_ne
  · intro hden
    exact of_denominator_ne hden

/-- A zero denominator excludes an ordinary defined-ratio witness. -/
theorem not_defined_of_denominator_eq_zero
    {K : Type*} [Zero K]
    (numerator denominator : K)
    (hden : denominator = 0) :
    ¬ DefinedRatioWitness K numerator denominator := by
  intro r
  exact r.denominator_ne hden

end DefinedRatioWitness

/-- In the natural-exponent monoid convention, `0^0` is the multiplicative unit. -/
@[simp] theorem zero_pow_zero_eq_one
    {R : Type*} [MonoidWithZero R] :
    (0 : R) ^ (0 : ℕ) = 1 := by
  simp

/-- A positive natural power of zero is zero; this records the adjacent branch. -/
@[simp] theorem zero_pow_one_eq_zero
    {R : Type*} [MonoidWithZero R] :
    (0 : R) ^ (1 : ℕ) = 0 := by
  simp

/-- Exponent-first quotient.  This is not ordinary field division. -/
def exponentQuotient
    {R : Type*} [Monoid R]
    (a : R) (m n : ℕ) : R :=
  a ^ (m - n)

/-- Equal exponents cancel before the base is evaluated. -/
@[simp] theorem exponentQuotient_self
    {R : Type*} [Monoid R]
    (a : R) (n : ℕ) :
    exponentQuotient a n n = 1 := by
  simp [exponentQuotient]

/-- In particular, exponent-first self-cancellation keeps unit value at base zero. -/
@[simp] theorem zero_exponentQuotient_self (n : ℕ) :
    exponentQuotient (0 : ℝ) n n = 1 := by
  simp

/-- Offset regularization of a self-ratio in the real value layer. -/
noncomputable def regularizedSelfRatio (x ε : ℝ) : ℝ :=
  (x + ε) / (x + ε)

/-- The regularized self-ratio is one whenever the lifted source is nonzero. -/
theorem regularizedSelfRatio_eq_one
    {x ε : ℝ}
    (h : x + ε ≠ 0) :
    regularizedSelfRatio x ε = 1 := by
  simp [regularizedSelfRatio, h]

/-- An offset distinct from the collapse offset `-x` gives unit self-ratio. -/
theorem regularizedSelfRatio_eq_one_of_offset_ne_neg
    {x ε : ℝ}
    (hε : ε ≠ -x) :
    regularizedSelfRatio x ε = 1 := by
  apply regularizedSelfRatio_eq_one
  intro hLift
  apply hε
  linarith

/--
For every fixed source `x`, the only collapsed offset is `ε = -x`.  Removing
that point gives an identically-one self-ratio, hence a two-sided limit of one
at the collapse offset.
-/
theorem tendsto_regularizedSelfRatio_punctured (x : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => regularizedSelfRatio x ε)
      (nhdsWithin (-x) ({-x}ᶜ : Set ℝ))
      (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  have hεne : ε ≠ -x := by
    simpa using hε
  symm
  exact regularizedSelfRatio_eq_one_of_offset_ne_neg hεne

/-- The right-hand path from the collapse offset has the same unit limit. -/
theorem tendsto_regularizedSelfRatio_right (x : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => regularizedSelfRatio x ε)
      (nhdsWithin (-x) (Set.Ioi (-x)))
      (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  have hLift : 0 < x + ε := by
    linarith
  symm
  exact regularizedSelfRatio_eq_one (ne_of_gt hLift)

/-- A positive offset lifts the zero source and gives self-ratio one. -/
theorem regularizedZeroSelfRatio_eq_one
    {ε : ℝ}
    (hε : 0 < ε) :
    regularizedSelfRatio 0 ε = 1 := by
  apply regularizedSelfRatio_eq_one
  positivity

/--
Away from the removed offset `ε = 0`, the regularized zero self-ratio is
identically one.  Hence its punctured-neighborhood limit is one from both sides.
-/
theorem tendsto_regularizedZeroSelfRatio_punctured :
    Filter.Tendsto
      (fun ε : ℝ => regularizedSelfRatio 0 ε)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ))
      (nhds 1) := by
  simpa using tendsto_regularizedSelfRatio_punctured (0 : ℝ)

/-- The positive-offset path tends to the same structural unit value. -/
theorem tendsto_regularizedZeroSelfRatio_right :
    Filter.Tendsto
      (fun ε : ℝ => regularizedSelfRatio 0 ε)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 1) := by
  simpa using tendsto_regularizedSelfRatio_right (0 : ℝ)

end DkMath.KUS
