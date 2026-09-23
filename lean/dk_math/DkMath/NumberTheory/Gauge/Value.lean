/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
import DkMath.Lib.NumberTheory.PadicValNat

#print "file: DkMath.NumberTheory.Gauge.Value"

/-!
# Value-side gauge facade

This module gives the value-side local power residue a stable Gauge vocabulary.
The implementation is definitionally the existing StructuralArithmetic
prime-coordinate projection; it does not introduce another valuation or
projection engine.
-/

namespace DkMath.NumberTheory.Gauge

/-! ## Definitionally thin value-side vocabulary -/

/-- Prime directions used by the value-side coordinate gauge. -/
abbrev ValueGaugePrime :=
  DkMath.NumberTheory.StructuralArithmetic.PrimeIndex

/-- The local value-side residue `v_p(a) mod n`. -/
abbrev valueGaugeResidue
    (n : ℕ) (p : ValueGaugePrime) (a : ℕ) : ℕ :=
  DkMath.NumberTheory.StructuralArithmetic.projectExponent
    n (padicValNat p.1 a)

/-- The full prime-coordinate value-side residue vector. -/
abbrev valueGaugeCoordinates (n a : ℕ) : ValueGaugePrime → ℕ :=
  DkMath.NumberTheory.StructuralArithmetic.projectPrimeCoordinates n a

/-! ## Exact meaning and boundary bridges -/

/-- The local residue is exactly the valuation modulo the gauge period. -/
theorem valueGaugeResidue_eq_mod
    (n : ℕ) (p : ValueGaugePrime) (a : ℕ) :
    valueGaugeResidue n p a = padicValNat p.1 a % n :=
  rfl

/-- Applying the coordinate vector at `p` gives the local residue at `p`. -/
theorem valueGaugeCoordinates_apply
    (n a : ℕ) (p : ValueGaugePrime) :
    valueGaugeCoordinates n a p = valueGaugeResidue n p a :=
  rfl

/-- Period zero retains the raw local valuation coordinate. -/
@[simp] theorem valueGaugeResidue_period_zero
    (p : ValueGaugePrime) (a : ℕ) :
    valueGaugeResidue 0 p a = padicValNat p.1 a :=
  DkMath.NumberTheory.StructuralArithmetic.projectExponent_period_zero _

/-- Period one collapses every local residue to zero. -/
@[simp] theorem valueGaugeResidue_period_one
    (p : ValueGaugePrime) (a : ℕ) :
    valueGaugeResidue 1 p a = 0 :=
  DkMath.NumberTheory.StructuralArithmetic.projectExponent_period_one _

/-- Period zero retains the raw prime-exponent vector. -/
@[simp] theorem valueGaugeCoordinates_period_zero (a : ℕ) :
    valueGaugeCoordinates 0 a =
      fun p : ValueGaugePrime => padicValNat p.1 a :=
  DkMath.NumberTheory.StructuralArithmetic.projectPrimeCoordinates_period_zero a

/-- Period one collapses the full value-side vector to zero. -/
@[simp] theorem valueGaugeCoordinates_period_one (a : ℕ) :
    valueGaugeCoordinates 1 a = fun _ => 0 :=
  DkMath.NumberTheory.StructuralArithmetic.projectPrimeCoordinates_period_one a

/-! ## Perfect-power landing and conservation -/

/-- A nonzero `n`-th power has zero local residue at every prime coordinate. -/
theorem valueGaugeResidue_pow_eq_zero
    {n a : ℕ} (p : ValueGaugePrime) (ha : a ≠ 0) :
    valueGaugeResidue n p (a ^ n) = 0 := by
  change DkMath.NumberTheory.StructuralArithmetic.projectExponent n
    (padicValNat p.1 (a ^ n)) = 0
  rw [DkMath.Lib.NumberTheory.padicValNat_pow p.2 n ha]
  exact DkMath.NumberTheory.StructuralArithmetic.projectExponent_period_mul n _

/-- The full value-side vector of a nonzero `n`-th power is the zero vector. -/
theorem valueGaugeCoordinates_pow_eq_zero
    {n a : ℕ} (ha : a ≠ 0) :
    valueGaugeCoordinates n (a ^ n) = fun _ => 0 := by
  funext p
  exact valueGaugeResidue_pow_eq_zero p ha

/-- Multiplication by a nonzero `n`-th power is invisible to the value gauge. -/
theorem valueGaugeCoordinates_mul_pow
    {n a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    valueGaugeCoordinates n (a * b ^ n) = valueGaugeCoordinates n a :=
  DkMath.NumberTheory.StructuralArithmetic.projectPrimeCoordinates_mul_pow
    (n := a) (a := b) (d := n) ha hb

/-! ## Explicit nonzero purity -/

/-- A nonzero value whose full local residue vector is zero. -/
def ValueGaugePure (n a : ℕ) : Prop :=
  a ≠ 0 ∧ valueGaugeCoordinates n a = fun _ => 0

/-- Every nonzero perfect `n`-th power is pure for the value-side gauge. -/
theorem valueGaugePure_pow
    {n a : ℕ} (ha : a ≠ 0) :
    ValueGaugePure n (a ^ n) :=
  ⟨pow_ne_zero n ha, valueGaugeCoordinates_pow_eq_zero ha⟩

/-- Zero is excluded from the ordinary nonzero value-side purity predicate. -/
theorem not_valueGaugePure_zero (n : ℕ) :
    ¬ ValueGaugePure n 0 := by
  intro h
  exact h.1 rfl

end DkMath.NumberTheory.Gauge

#print axioms DkMath.NumberTheory.Gauge.valueGaugeResidue_eq_mod
#print axioms DkMath.NumberTheory.Gauge.valueGaugeCoordinates_apply
#print axioms DkMath.NumberTheory.Gauge.valueGaugeResidue_period_zero
#print axioms DkMath.NumberTheory.Gauge.valueGaugeResidue_period_one
#print axioms DkMath.NumberTheory.Gauge.valueGaugeCoordinates_period_zero
#print axioms DkMath.NumberTheory.Gauge.valueGaugeCoordinates_period_one
#print axioms DkMath.NumberTheory.Gauge.valueGaugeResidue_pow_eq_zero
#print axioms DkMath.NumberTheory.Gauge.valueGaugeCoordinates_pow_eq_zero
#print axioms DkMath.NumberTheory.Gauge.valueGaugeCoordinates_mul_pow
#print axioms DkMath.NumberTheory.Gauge.valueGaugePure_pow
#print axioms DkMath.NumberTheory.Gauge.not_valueGaugePure_zero
