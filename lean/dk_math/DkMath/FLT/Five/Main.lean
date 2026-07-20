/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.BranchA
import DkMath.FLT.Five.GoldenOrder
import DkMath.FLT.Five.GoldenDivisibility
import DkMath.FLT.Five.GoldenFifthPowerCoordinates
import DkMath.FLT.Five.GoldenCoprimeFactor
import DkMath.FLT.Five.GoldenUnitClassification
import DkMath.FLT.Five.NormalForm
import DkMath.FLT.Five.Provider
import DkMath.FLT.Five.Reduction
import DkMath.FLT.Five.SignedBranchA
import DkMath.FLT.Five.SignedFiveAdic
import DkMath.FLT.Five.SignedFiveAdicPowerSplit
import DkMath.FLT.Five.SignedGoldenRamifierStripped
import DkMath.FLT.Five.SignedGoldenConjugateCoprime
import DkMath.FLT.Five.SignedGoldenFifthPower
import DkMath.FLT.Five.SignedGoldenUnitClasses
import DkMath.FLT.Five.SignedGoldenSectorArithmetic
import DkMath.FLT.Five.SignedGoldenZeroSector
import DkMath.FLT.Five.SignedGoldenZeroSectorInversion
import DkMath.FLT.Five.SignedGoldenZeroSectorFactorization
import DkMath.FLT.Five.SignedGoldenZeroSectorDescent
import DkMath.FLT.Five.SignedGoldenClosure
import DkMath.FLT.Five.SignedGoldenZeroSectorFinal
import DkMath.FLT.Five.SignedSquareGoldenExceptional
import DkMath.FLT.Five.SquareGoldenBridge
import DkMath.FLT.Five.SquareGoldenNormalForm
import DkMath.FLT.Five.Valuation

/-!
# Fermat's Last Theorem at exponent five

The proof route is: normalize a positive solution to a primitive packet; choose
one of the two signed gap orientations; split the associated golden-order
factor into a unit and a fifth power; eliminate four nonzero unit classes; and
exclude the zero class by a certified strict infinite descent. Conditional
receiver theorems expose the unit-class and zero-sector boundaries, while
`flt5Target` and `fermatFive_no_positive_solution` are unconditional endpoints.

The scope is exactly positive natural numbers and exponent five. This module
does not assert the general Fermat theorem, a novel historical proof, external
peer review, or acceptance of the development beyond Lean's kernel checks.
-/

#print "file: DkMath.FLT.Five.Main"

namespace DkMath.FLT.Five

/-- No positive natural numbers satisfy `x^5 + y^5 = z^5`. -/
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z

/-- Conditional receiver exposing both unit classification and zero-sector arithmetic. -/
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic

/-- Conditional receiver after the proved unit classification is supplied. -/
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic

/-- The unconditional positive-natural exponent-five endpoint. -/
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion

/-- Ordinary-argument form: positive `x`, `y`, and `z` cannot solve the equation. -/
theorem fermatFive_no_positive_solution
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z :=
  flt5Target x y z hx hy hz

/-- Every stripped golden packet is unconditionally reduced to the five sectors. -/
theorem signedGoldenFiniteUnitSectorCore : SignedGoldenFiniteUnitSectorCore :=
  signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth

/-- The zero-sector arithmetic proposition refutes every primitive packet. -/
theorem counterexamplePackRefuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic

/-- The zero-sector arithmetic proposition refutes every positive solution. -/
theorem positiveFermat5Refuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic

end DkMath.FLT.Five
