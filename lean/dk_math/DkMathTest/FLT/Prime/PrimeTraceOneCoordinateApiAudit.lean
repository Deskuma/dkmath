/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRTraceOneBridge
import DkMath.NumberTheory.TraceOneConjugateCoprime
import DkMath.FLT.Prime.AdicPowerSplit
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.DedekindDomain.Basic

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneCoordinateApiAudit"

/-! This file pins the names used by the Phase-22 resultant and residue-field
routes.  The resultant equivalence in this checkout is the monic-first form
`Polynomial.isUnit_resultant_iff_isCoprime`; there is no
`Polynomial.isCoprime_iff_resultant_isUnit` declaration. -/

#check Polynomial.resultant
#check IsCoprime
#check Polynomial.isUnit_resultant_iff_isCoprime
#check MvPolynomial.eval
#check MvPolynomial.aeval
#check MvPolynomial.rename
#check MvPolynomial.bind₁
#check MvPolynomial.coeff
#check MvPolynomial.map
#check Ideal.Quotient.mk
#check Ideal.Quotient.mk_eq_mk_iff_sub_mem
#check Ideal.IsPrime
#check Ideal.IsMaximal
#check IsPrimitiveRoot
#check primitiveRoots
#check ZMod
#check CharP

#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.exists_integral_gauss_form
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.map_modTwo_eq_of_integral_gauss_form
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.exists_half_difference
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.exists_prime_traceOne_coordinates
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.exists_prime_traceOne_coordinate_packet
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket.coord
#check DkMath.CosmicFormula.GTail_one_eq_GTailCyclotomicShell_of_ne_zero
#check DkMath.FLT.Prime.PrimeAdicFactorPacket.residual_exact_one
#check DkMath.FLT.Prime.PrimeAdicFactorPacket.residual_not_prime_sq
#check DkMath.FLT.Prime.PrimeAdicPowerSplit.residual_eq
#check DkMath.NumberTheory.TraceOneQuadratic.common_divisor_dvd_discrAxis_of_coordinate_coprime
#check DkMath.NumberTheory.TraceOneQuadratic.ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
#check DkMath.NumberTheory.TraceOneQuadratic.PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
