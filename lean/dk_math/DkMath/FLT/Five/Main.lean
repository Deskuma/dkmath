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

/-!
The current reduction tower routes a primitive exponent-five candidate through:

- signed difference/sum Branch-A orientations,
- an exact common five-adic packet,
- the power split `carrier = 5^4*a^5`, `residual = 5*b^5`, and
- a signed square-golden exceptional packet, and
- an integral golden-order packet with the visible ramifier `tau` stripped.
- certified relative primality of the stripped element and its conjugate.

No final assembly theorem is declared before the remaining exceptional core is
Lean-certified.
-/

end DkMath.FLT.Five
