/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOnePrimeUnitSectors
import DkMath.FLT.Three.EisensteinUnitSectors
import DkMath.FLT.Five.GoldenUnitClassification

#print "file: DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorProbe"

namespace DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorProbe

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
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

/-! p=5 and p=13 are real-branch carrier regressions.  Their explicit
parameters are checked here; the generic Dirichlet sector remains blocked by
the missing quadratic signature transport recorded in report-019. -/

example : signedPrimeDiscriminant 5 = (5 : ℤ) := by
  norm_num [signedPrimeDiscriminant]

example : signedPrimeParameter 5 = 1 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeDiscriminant 13 = (13 : ℤ) := by
  norm_num [signedPrimeDiscriminant]

example : signedPrimeParameter 13 = 3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

/-! The old p=5 result is deliberately only a `GoldenUnit` predicate result,
not a `GoldenIntˣ` sector system. -/

example : GoldenUnitClassesModFifth := goldenUnitClassesModFifth

end DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorProbe
