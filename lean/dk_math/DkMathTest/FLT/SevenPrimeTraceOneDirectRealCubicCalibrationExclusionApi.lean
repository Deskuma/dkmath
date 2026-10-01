/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCalibrationExclusionApi"

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

#check directOrbitDeepJetWUnit_ne_calibration

example
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    directOrbitDeepJetWUnit h.squareRefinement eta ≠ directOrbitDeepJetRho := by
  exact directOrbitDeepJetWUnit_ne_calibration h hc eta heta
