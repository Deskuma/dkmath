/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquarePrimeSupport

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportScratch"

namespace DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportScratch

open DkMath.FLT.Seven

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    IsCoprime t.gapSquareRoot t.quotientSquareRoot :=
  directOrbitSquareRefinement_squareRoots_isCoprime t

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ∃ u : SevenRealCubicIntˣ,
      t.gapSquareRoot * t.quotientSquareRoot =
        (u : SevenRealCubicInt) *
          (t.powerSplit.gapSplit.a : SevenRealCubicInt) :=
  directOrbitSquareRefinement_squareRoots_unit_split t

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    0 < Int.natAbs (SevenRealCubicInt.norm t.quotientSquareRoot) :=
  directOrbitSquareRefinement_quotient_square_norm_pos t

end DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportScratch
