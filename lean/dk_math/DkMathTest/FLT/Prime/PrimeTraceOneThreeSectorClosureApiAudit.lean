/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneThreeSectorClosureApiAudit"

open DkMath.FLT.Prime
open DkMath.FLT.Three
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

noncomputable section

#check DkMath.FLT.Three.EisensteinInt
#check DkMath.FLT.Three.traceOneInt_signedPrimeParameter_three_type
#check DkMath.NumberTheory.PrimeQuadraticDiscriminant.signedPrimeParameter_three
#check DkMath.FLT.Three.traceOneNegOneEuclideanDomain
#check EuclideanDomain.instIsPrincipalIdealRing
#check classGroupPTorsionFreeAt_of_isPrincipalIdealRing
#check exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#check DkMath.FLT.Three.eisensteinCubeUnitPowerSectorSystem
#check DkMath.FLT.Three.eisensteinCubeUnitPowerSectorSystem_complete
#check DkMath.FLT.Prime.exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
#check DkMath.FLT.Prime.classGroupPTorsionFreeAt_traceOneNegOne_three
#check DkMath.FLT.Prime.exists_eisensteinSector_mul_cube_of_primeTraceOneStrippedIdealPacket_three

#synth EuclideanDomain (TraceOneInt (-1))
#synth IsPrincipalIdealRing (TraceOneInt (-1))

example : EisensteinInt = TraceOneInt (-1) := rfl

example : signedPrimeParameter 3 = -1 := by
  exact signedPrimeParameter_three

example : classGroupPTorsionFreeAt (TraceOneInt (-1)) 3 := by
  exact classGroupPTorsionFreeAt_traceOneNegOne_three

example :
    UnitPowerSectorSystem (TraceOneInt (-1)) 3 :=
  eisensteinCubeUnitPowerSectorSystem

example {u : (TraceOneInt (-1))ˣ} :
    ∃ sector : EisensteinUnitSector, ∃ e : (TraceOneInt (-1))ˣ,
      u = eisensteinCubeUnitPowerSectorSystem.rep sector * e ^ 3 := by
  exact eisensteinCubeUnitPowerSectorSystem_complete u

end
