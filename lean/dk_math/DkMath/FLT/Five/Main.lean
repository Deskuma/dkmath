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
import DkMath.FLT.Five.SignedGoldenClosure
import DkMath.FLT.Five.SignedSquareGoldenExceptional
import DkMath.FLT.Five.SquareGoldenBridge
import DkMath.FLT.Five.SquareGoldenNormalForm
import DkMath.FLT.Five.Valuation

#print "file: DkMath.FLT.Five.Main"

namespace DkMath.FLT.Five

/-- Local exponent-five target, independent of the legacy general-`p ≥ 5` facade. -/
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z

/-- The two exact remaining arithmetic propositions suffice for the final target. -/
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic

/-!
The current reduction tower routes a primitive exponent-five candidate through:

- signed difference/sum Branch-A orientations,
- an exact common five-adic packet,
- the power split `carrier = 5^4*a^5`, `residual = 5*b^5`, and
- a signed square-golden exceptional packet, and
- an integral golden-order packet with the visible ramifier `tau` stripped.
- certified relative primality of the stripped element and its conjugate,
- unconditional fifth-power splitting up to a unit,
- elimination of unit sectors one through four, and
- the primitive and exact tenth-power split of the zero sector.

The remaining frontier consists of the explicit `GoldenUnitClassesModFifth`
and `GoldenZeroSectorArithmeticExclusion` propositions.  Their receiver above
already includes orientation closure and primitive normalization.
-/

end DkMath.FLT.Five
