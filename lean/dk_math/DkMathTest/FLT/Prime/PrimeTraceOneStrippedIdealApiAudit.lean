/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
import Mathlib.RingTheory.Ideal.Operations

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealApiAudit"

/-! Phase-25 signature pinning.  This file records the declarations consumed by
the stripped-ideal bridge without introducing a second implementation route. -/

#check DkMath.FLT.Prime.PrimeAdicFactorPacket
#check DkMath.FLT.Prime.PrimeAdicPowerSplit
#check DkMath.FLT.Prime.primeAdicPowerSplit_of_packet
#check DkMath.FLT.Prime.PrimeAdicPowerSplit.residual_eq
#check DkMath.FLT.Prime.PrimeAdicPowerSplit.prime_not_dvd_b
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket.coord
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket.coord_norm_eq
#check DkMath.FLT.Prime.prime_packet_coordinate_isCoprime
#check DkMath.NumberTheory.TraceOneQuadratic.PrimeDiscriminantPacket
#check DkMath.NumberTheory.PrimeQuadraticDiscriminant.discr_signedPrimeParameter
#check DkMath.NumberTheory.PrimeQuadraticDiscriminant.signedPrimeDiscriminant_natAbs
#check DkMath.NumberTheory.TraceOneQuadratic.signedPrimeDiscriminantPacket
#check DkMath.NumberTheory.TraceOneQuadratic.PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
#check DkMath.NumberTheory.TraceOneQuadratic.ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
#check DkMath.NumberTheory.TraceOneQuadratic.traceOne_mul_conj
#check DkMath.NumberTheory.TraceOneQuadraticField.traceOneRat_no_rational_root
#check DkMath.NumberTheory.TraceOneQuadraticField.traceOneRat_isDedekindDomain
#check DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow
#check Ideal.span
#check Ideal.span_singleton_mul_span_singleton
#check Ideal.span_singleton_pow
#check Ideal.span_singleton_eq_bot
#check Ideal.zero_eq_bot
#check mem_nonZeroDivisors_iff_ne_zero
#check DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell
#check DkMath.NumberTheory.TraceOneQuadratic.coordinate_isCoprime_of_eq_discrAxis_mul
#check DkMath.NumberTheory.TraceOneQuadratic.span_mul_span_conj_eq_span_norm
#check DkMath.NumberTheory.TraceOneQuadratic.span_mul_span_conj_eq_pow_of_norm_eq_pow
#check DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket
#check DkMath.FLT.Prime.nonempty_primeTraceOneStrippedIdealPacket
#check DkMath.FLT.Prime.primeTraceOneStrippedIdealPacket
