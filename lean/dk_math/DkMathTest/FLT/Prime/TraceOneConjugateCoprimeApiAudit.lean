/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneDiscriminantAxis
import DkMath.NumberTheory.TraceOneQuadraticField
import DkMath.NumberTheory.CyclotomicQRTraceOneBridge
import DkMath.FLT.Prime.AdicPowerSplit
import Mathlib.RingTheory.DedekindDomain.Basic

open DkMath.CosmicFormula
open DkMath.FLT.Prime
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge

#check Prime
#print Prime
#check Prime.not_unit
#check Prime.dvd_mul
#check Prime.dvd_of_dvd_pow
#check Ideal.isPrime_span_singleton_of_prime
#check Ideal.span_singleton_prime
#check Ideal.IsPrime.isMaximal
#check Ideal.isCoprime_iff_sup_eq
#check Ideal.mem_span_singleton
#check Ideal.mem_span_singleton_self
#check isUnit_iff_dvd_one
#check IsUnit.unit_spec
#check Ring.DimensionLEOne
#check IsDedekindDomain
#check GTail_one_eq_GTailCyclotomicShell_of_ne_zero
#check exists_prime_traceOne_coordinates
#check PrimeAdicPowerSplit.residual_eq
