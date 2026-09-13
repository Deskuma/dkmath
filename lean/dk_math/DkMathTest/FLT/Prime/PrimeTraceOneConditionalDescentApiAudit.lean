/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
import DkMath.Lib.NumberTheory.PrincipalIdealPower
import DkMath.Lib.NumberTheory.UnitPowerSector
import DkMath.NumberTheory.TraceOnePrimeUnitSectors
import DkMath.FLT.Three.EisensteinUnitSectors

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneConditionalDescentApiAudit"

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.NumberTheory.TraceOnePrimeUnitSectors
open DkMath.FLT.Three

#check DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket
#check DkMath.FLT.Prime.nonempty_primeTraceOneStrippedIdealPacket
#check DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket.residual
#check DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket.idealRoot
#check DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket.idealRoot_nonzero
#check DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket.residual_span_eq
#check DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket.residual_norm_pow
#check DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket.residual_conj_ideal_coprime

#check classGroupPTorsionFreeAt
#check exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#check exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#check UnitPowerSectorSystem
#check traceOnePrimeRealFinSectorSystem
#check traceOnePrimeReal_exists_sector_mul_pow_of_span_eq_pow
#check traceOnePrimeImaginarySingletonSectorSystem
#check traceOnePrimeImaginary_exists_eq_pow_of_span_eq_pow

#check traceOneRat_no_rational_root
#check traceOneRatField
#check traceOneRatHom_injective
#check traceOneRat_isDedekindDomain

/-! The p=3 API is intentionally carrier-specific in this checkout. -/
#check EisensteinInt
#check EisensteinUnitSector
#check exists_sector_mul_cube_of_unit
#check DkMath.FLT.Three.EisensteinUnitSector.rep_isUnit
