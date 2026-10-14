/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSharpenedBranch

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSharpenedBranchR49Scratch"

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

#check directOrbitTrivialCommonFactor_exists_nontrivial_7pow9_correction
#check directOrbitTrivialCommonFactor_correction_norm_one
#check directOrbitTrivialCommonFactor_correction_not_torsion
#check directOrbitCommonFactor_large_residue_one_support
#check directOrbit_sharpened_common_factor_dichotomy

example
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    Nonempty (DirectOrbitTrivialCommonFactorSharpenedPacket h) ∨
      Nonempty (DirectOrbitNontrivialCommonFactorSharpenedPacket h) := by
  exact directOrbit_sharpened_common_factor_dichotomy h
