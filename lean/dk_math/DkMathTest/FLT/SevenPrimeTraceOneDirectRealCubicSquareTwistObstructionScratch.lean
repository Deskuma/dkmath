/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareTwistObstruction

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionScratch"

namespace DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionScratch

open DkMath.FLT.Seven

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ¬ ∃ v : SevenRealCubicIntˣ,
        directOrbitSquareTwistCoeff0 t = v ^ 2 :=
  directOrbit_squareTwist_coeff0_not_square t

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    SevenRealCubicInt.norm
        (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) = 1 :=
  directOrbit_squareTwist_coeff0_norm_eq_one t

end DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionScratch
