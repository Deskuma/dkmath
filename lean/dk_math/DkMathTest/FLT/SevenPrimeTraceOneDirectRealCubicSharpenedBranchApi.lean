/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSharpenedBranchApi"

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

#check directOrbitTrivialCommonFactor_exists_nontrivial_7pow9_correction
#check directOrbitTrivialCommonFactor_correction_norm_one
#check directOrbitTrivialCommonFactor_correction_not_torsion
#check directOrbitCommonFactor_large_residue_one_support
#check directOrbitCommonFactor_large_residue_one_height
#check directOrbit_sharpened_common_factor_dichotomy
#check DirectOrbitTrivialCommonFactorSharpenedPacket
#check DirectOrbitNontrivialCommonFactorSharpenedPacket

example
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1) :
    ∃ eta t : SevenRealCubicIntˣ,
      directOrbitDeepJetWUnit h.squareRefinement eta =
        directOrbitDeepJetRho * t ^ (7 ^ 9) ∧
      t ^ (7 ^ 9) ≠ 1 := by
  obtain ⟨eta, _xi, _v, t, _, _, _, _, _, hw, htne⟩ :=
    directOrbitTrivialCommonFactor_exists_nontrivial_7pow9_correction h hc
  exact ⟨eta, t, hw, htne⟩

example
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    Nonempty (DirectOrbitTrivialCommonFactorSharpenedPacket h) ∨
      Nonempty (DirectOrbitNontrivialCommonFactorSharpenedPacket h) := by
  exact directOrbit_sharpened_common_factor_dichotomy h
