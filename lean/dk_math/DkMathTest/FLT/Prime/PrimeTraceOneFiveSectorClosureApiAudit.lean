/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneFiveSectorClosureApiAudit"

open DkMath.FLT.Five
open DkMath.FLT.Prime
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

#check GoldenInt
#check goldenToTraceOne
#check traceOneToGolden
#check goldenTraceOneRingEquiv
#check goldenNorm_eq_traceOneNorm_one
#check goldenEuclideanDomain
#check goldenUnit_iff_isUnit
#check goldenUnitClassesModFifth
#check goldenPhi
#check signedPrimeParameter
#check signedPrimeParameter_five
#check UnitPowerSectorSystem
#check classGroupPTorsionFreeAt_of_isPrincipalIdealRing
#check exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
#check exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
#check DkMath.NumberTheory.TraceOnePrimeUnitSectors.traceOnePrimeRealFinSectorSystem
#check goldenTraceOneFifthUnitPowerSectorSystem
#check goldenTraceOneFifthUnitPowerSectorSystem_complete
#check classGroupPTorsionFreeAt_traceOneOne_five
#check exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five

#synth EuclideanDomain GoldenInt
#synth IsPrincipalIdealRing GoldenInt

example (x : GoldenInt) :
    traceOneToGolden (goldenToTraceOne x) = x := by
  exact traceOneToGolden_goldenToTraceOne x

example (x : TraceOneInt 1) :
    goldenToTraceOne (traceOneToGolden x) = x := by
  exact goldenToTraceOne_traceOneToGolden x

example (x y : GoldenInt) :
    goldenTraceOneRingEquiv (x + y) =
      goldenTraceOneRingEquiv x + goldenTraceOneRingEquiv y := by
  exact goldenTraceOneRingEquiv.map_add x y

example (x y : GoldenInt) :
    goldenTraceOneRingEquiv (x - y) =
      goldenTraceOneRingEquiv x - goldenTraceOneRingEquiv y := by
  simp

example (x y : GoldenInt) :
    goldenTraceOneRingEquiv (x * y) =
      goldenTraceOneRingEquiv x * goldenTraceOneRingEquiv y := by
  exact goldenTraceOneRingEquiv.map_mul x y

example (n : ℕ) :
    goldenTraceOneRingEquiv (n : GoldenInt) =
      (n : TraceOneInt 1) := by
  simp

example (z : ℤ) :
    goldenTraceOneRingEquiv (z : GoldenInt) =
      (z : TraceOneInt 1) := by
  simp

example (x : GoldenInt) (n : ℕ) :
    goldenTraceOneRingEquiv (x ^ n) =
      (goldenTraceOneRingEquiv x) ^ n := by
  exact goldenTraceOneRingEquiv_map_pow x n

example :
    goldenTraceOneRingEquiv goldenPhi =
      DkMath.NumberTheory.TraceOneQuadratic.tau 1 := by
  exact goldenTraceOneRingEquiv_map_goldenPhi

example (x : GoldenInt) :
    goldenTraceOneRingEquiv (goldenConj x) =
      conj (goldenTraceOneRingEquiv x) := by
  exact goldenTraceOneRingEquiv_map_goldenConj x

example (x : GoldenInt) :
    goldenNorm x =
      DkMath.NumberTheory.TraceOneQuadratic.norm (goldenTraceOneRingEquiv x) := by
  exact goldenTraceOneRingEquiv_map_goldenNorm x

example : signedPrimeParameter 5 = 1 := by
  exact signedPrimeParameter_five

example :
    UnitPowerSectorSystem (TraceOneInt 1) 5 :=
  goldenTraceOneFifthUnitPowerSectorSystem

example (u : (TraceOneInt 1)ˣ) :
    ∃ i : Fin 5, ∃ e : (TraceOneInt 1)ˣ,
      u = goldenTraceOneFifthUnitPowerSectorSystem.rep i * e ^ 5 := by
  exact goldenTraceOneFifthUnitPowerSectorSystem_complete u

example (i : Fin 5) :
    (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) =
      goldenToTraceOne (goldenPhi ^ i.val) := by
  exact goldenTraceOneFifthUnitPowerSectorSystem_rep_apply i

section TraceOneOneAuditInstances

local instance traceOneOneEuclideanDomain : EuclideanDomain (TraceOneInt 1) :=
  goldenTraceOneRingEquiv.symm.euclideanDomain

local instance traceOneOneIsDomain : IsDomain (TraceOneInt 1) :=
  goldenTraceOneRingEquiv.symm.toMulEquiv.isDomain GoldenInt

example : classGroupPTorsionFreeAt (TraceOneInt 1) 5 := by
  exact classGroupPTorsionFreeAt_traceOneOne_five

end TraceOneOneAuditInstances

example :
    ∀ i : Fin 5,
      (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) =
        goldenToTraceOne (goldenPhi ^ i.val) := by
  intro i
  exact goldenTraceOneFifthUnitPowerSectorSystem_rep_apply i

end
