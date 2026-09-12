/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOnePrimeUnitSectors
import DkMath.NumberTheory.TraceOneQuadraticField
import DkMath.FLT.Three.EisensteinUnitSectors
import DkMath.FLT.Five.GoldenUnitClassification

#print "file: DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorProbe"

namespace DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorProbe

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.NumberTheory.TraceOnePrimeUnitSectors
open DkMath.FLT.Three
open DkMath.FLT.Five

/-! The exceptional p=3 adapter remains the existing specialized result. -/

example (u : EisensteinIntˣ) :
    ∃ sector : EisensteinUnitSector, ∃ e : EisensteinInt,
      IsUnit e ∧ (u : EisensteinInt) = sector.rep * e ^ 3 :=
  exists_sector_mul_cube_of_unit u

/-! The imaginary generic construction is available at p=7 and p=11. -/

noncomputable example :
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter 7)) 7 :=
  traceOnePrimeImaginarySingletonSectorSystem (by norm_num) (by norm_num) (by norm_num)

noncomputable example :
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter 11)) 11 :=
  traceOnePrimeImaginarySingletonSectorSystem (by norm_num) (by norm_num) (by norm_num)

example (u : (TraceOneInt (signedPrimeParameter 7))ˣ) :
    (u : TraceOneInt (signedPrimeParameter 7)) = 1 ∨
      (u : TraceOneInt (signedPrimeParameter 7)) = -1 :=
  traceOnePrimeImaginary_unit_eq_one_or_neg_one (by norm_num) (by norm_num) (by norm_num) u

example (u : (TraceOneInt (signedPrimeParameter 11))ˣ) :
    (u : TraceOneInt (signedPrimeParameter 11)) = 1 ∨
      (u : TraceOneInt (signedPrimeParameter 11)) = -1 :=
  traceOnePrimeImaginary_unit_eq_one_or_neg_one (by norm_num) (by norm_num) (by norm_num) u

/-! p=5 and p=13 are real-branch regressions. -/

example : signedPrimeDiscriminant 5 = (5 : ℤ) := by
  norm_num [signedPrimeDiscriminant]

example : signedPrimeParameter 5 = 1 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeDiscriminant 13 = (13 : ℤ) := by
  norm_num [signedPrimeDiscriminant]

example : signedPrimeParameter 13 = 3 := by
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
    Module.finrank ℚ (TraceOneRat (signedPrimeParameter 5)) = 2 ∧
      NumberField.InfinitePlace.nrComplexPlaces
          (TraceOneRat (signedPrimeParameter 5)) = 0 ∧
      NumberField.InfinitePlace.nrRealPlaces
          (TraceOneRat (signedPrimeParameter 5)) = 2 ∧
      NumberField.Units.rank (TraceOneRat (signedPrimeParameter 5)) = 1 :=
  traceOnePrimeReal_signature (by norm_num) (by norm_num)

noncomputable example :
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter 5)) 5 := by
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
  exact traceOnePrimeRealFinSectorSystem (by norm_num) (by norm_num)

noncomputable example :
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter 13)) 13 := by
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
  exact traceOnePrimeRealFinSectorSystem (by norm_num) (by norm_num)

example :
    (traceOnePrimeRealFinSectorSystem (p := 5) (by norm_num) (by norm_num)).Sector =
      Fin 5 := by
  simp [traceOnePrimeRealFinSectorSystem]

/-! The old p=5 result is deliberately only a `GoldenUnit` predicate result,
not a `GoldenIntˣ` sector system. -/

example : GoldenUnitClassesModFifth := goldenUnitClassesModFifth

end DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorProbe
