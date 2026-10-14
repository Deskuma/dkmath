/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneApi"

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

#check common_norm_prime_mod_seven_one
#check directOrbitCommonPrime_q_mod_seven_one
#check directOrbitCommonFactor_c_ge_29

example
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (hq : q.Prime) (hqc : q ∣ h.c) :
    q % 7 = 1 := by
  exact directOrbitCommonPrime_q_mod_seven_one h q hq hqc

example
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (hcpos : 1 < h.c) : 29 ≤ h.c := by
  exact directOrbitCommonFactor_c_ge_29 h hcpos
