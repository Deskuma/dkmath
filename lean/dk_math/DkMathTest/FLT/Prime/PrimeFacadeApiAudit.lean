/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime

#print "file: DkMathTest.FLT.Prime.PrimeFacadeApiAudit"

open DkMath.FLT.Prime
open DkMath.FLT.Three
open DkMath.FLT.Five
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.NumberTheory.TraceOnePrimeUnitSectors

noncomputable section

/-! The stable front door and generic packet/landing vocabulary. -/
#check PrimitivePrimeCounterexample
#check PrimeCounterexampleRoute
#check counterexampleRoute_of_primitive
#check PrimeAdicFactorPacket
#check PrimeAdicPowerSplit
#check PrimeTraceOneCoordinatePacket
#check PrimeTraceOneStrippedIdealPacket
#check classGroupPTorsionFreeAt_of_coprime_card
#check traceOnePowCoords
#check traceOne_pow_coordinates
#check traceOne_pow_core_landing_iff

/-! Calibrated p=3, p=5, p=7 and real-sector receivers. -/
#check signedPrimeParameter
#check signedPrimeParameter_three
#check signedPrimeParameter_five
#check EisensteinInt
#check traceOneInt_signedPrimeParameter_three_type
#check eisensteinCubeUnitPowerSectorSystem
#check exists_eisensteinSector_mul_cube_of_primeTraceOneStrippedIdealPacket_three
#check classGroupPTorsionFreeAt_traceOneNegOne_three
#check GoldenInt
#check goldenTraceOneRingEquiv
#check goldenTraceOneFifthUnitPowerSectorSystem
#check goldenTraceOneFifthUnitPowerSectorSystem_complete
#check classGroupPTorsionFreeAt_traceOneOne_five
#check exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five
#check exists_goldenSector_powCoords_of_primeTraceOneStrippedIdealPacket_five
#check exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket
#check exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
#check classGroupPTorsionFreeAt_traceOneNegTwo_seven
#check traceOnePrimeRealFinSectorSystem
#check exists_realSector_powCoords_of_primeTraceOneStrippedIdealPacket
#check exists_realSector_mul_pow_with_baseNorm_not_dvd
#check PrimeTraceOneStrippedIdealPacket.residual_natAbs_norm_not_dvd

end
