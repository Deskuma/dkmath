/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.PolynomialSuccessor
import DkMath.NumberTheory.GapFocusing.SuccessorGauge
import Mathlib.Data.ZMod.Basic

#print "file: DkMathTest.NumberTheory.GapFocusingSuccessorCalibration"

open DkMath.CosmicFormula DkMath.NumberTheory.GapFocusing Polynomial

/-- Degree zero participates in the polynomial Bézout identity. -/
example : IsCoprime (kernelPolynomial 0) (kernelPolynomial 1) :=
  kernelPolynomial_succ_isCoprime 0

/-- The polynomial witness does not need a domain coefficient ring. -/
example : IsCoprime (GTail 2 1 (X : (ZMod 4)[X]) 1)
    (GTail 3 1 (X : (ZMod 4)[X]) 1) :=
  GN_polynomial_succ_isCoprime 2

/-- Distinct adjacent divisor layers include composite-to-prime degree. -/
example : Disjoint ((6 : ℕ).divisors.erase 1) ((7 : ℕ).divisors.erase 1) :=
  successor_divisor_layers_disjoint 6

/-- Explicit residue interpolation at degrees two and three. -/
example (A B : ℤ[X]) :
    let P := A * kernelPolynomial 3 - B * (X + 1) * kernelPolynomial 2
    kernelPolynomial 2 ∣ P - A ∧ kernelPolynomial 3 ∣ P - B :=
  kernelPolynomial_successor_interpolation 2 A B

/-- The degree-zero gauge tests exact equality and the universal first-power class. -/
example {R : Type*} [CommMonoid R] (u v : Rˣ) :
    SameUnitPowerClass 0 u v ↔ u = v := by
  constructor
  · rintro ⟨t, ht⟩
    simpa only [pow_zero, mul_one] using ht
  · intro h
    exact ⟨1, by simpa using h⟩

example {R : Type*} [CommMonoid R] (u v : Rˣ) : SameUnitPowerClass 1 u v := by
  apply (sameUnitPowerClass_iff_mem_powerSubgroup 1 u v).mpr
  rw [DkMath.Lib.Algebra.powerSubgroup_one]
  trivial
