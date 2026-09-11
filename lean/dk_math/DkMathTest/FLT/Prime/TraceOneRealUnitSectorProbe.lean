/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOnePrimeUnitSectors
import DkMath.NumberTheory.TraceOneQuadraticField

#print "file: DkMathTest.FLT.Prime.TraceOneRealUnitSectorProbe"

namespace DkMathTest.FLT.Prime.TraceOneRealUnitSectorProbe

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.NumberTheory.TraceOnePrimeUnitSectors

example :
    signedPrimeParameter 5 = 1 ∧ signedPrimeParameter 13 = 3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 5 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
    letI : Field (TraceOneRat (signedPrimeParameter 5)) := inferInstance
    letI : NumberField (TraceOneRat (signedPrimeParameter 5)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance
    }
    NumberField.IsTotallyReal (TraceOneRat (signedPrimeParameter 5)) :=
  traceOneRat_isTotallyReal_of_prime_mod_four_eq_one (by norm_num) (by norm_num)

example :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 13 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
    letI : Field (TraceOneRat (signedPrimeParameter 13)) := inferInstance
    letI : NumberField (TraceOneRat (signedPrimeParameter 13)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance
    }
    NumberField.Units.rank (TraceOneRat (signedPrimeParameter 13)) = 1 := by
  have h := traceOnePrimeReal_signature (p := 13) (by norm_num) (by norm_num)
  exact h.2.2.2

example :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 13 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
    letI : Field (TraceOneRat (signedPrimeParameter 13)) := inferInstance
    letI : NumberField (TraceOneRat (signedPrimeParameter 13)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance
    }
    NumberField.IsTotallyReal (TraceOneRat (signedPrimeParameter 13)) :=
  traceOneRat_isTotallyReal_of_prime_mod_four_eq_one (by norm_num) (by norm_num)

noncomputable example :
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter 5)) 5 :=
  traceOnePrimeRealFinSectorSystem (by norm_num) (by norm_num)

noncomputable example :
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter 13)) 13 :=
  traceOnePrimeRealFinSectorSystem (by norm_num) (by norm_num)

end DkMathTest.FLT.Prime.TraceOneRealUnitSectorProbe
