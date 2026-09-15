/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRTraceOneBridge
import DkMath.NumberTheory.CyclotomicQRGaussNormalization
import DkMath.NumberTheory.CyclotomicQRProduct
import DkMath.NumberTheory.CyclotomicQRGaloisAction
import DkMath.NumberTheory.TraceOneConjugateCoprime
import DkMath.FLT.Prime.AdicPowerSplit
import DkMath.Lib.NumberTheory.IdealPowerFactor
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Resultant.Basic

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneResidueTransportApiAudit"

/-! This is a declaration audit for Phase 23.  In particular, the audit keeps
the characteristic-zero assumptions of the pinned DkMath Gauss-square API
visible beside Mathlib's characteristic-independent finite Gauss-sum API. -/

#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket.coord
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket.map_RZ
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket.gauss_form
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket.gauss_difference
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket.half_relation
#check DkMath.NumberTheory.CyclotomicQRTraceOneBridge.PrimeTraceOneCoordinatePacket.norm_eq

#check DkMath.NumberTheory.CyclotomicQRProduct.qrFinset
#check DkMath.NumberTheory.CyclotomicQRProduct.qnrFinset
#check DkMath.NumberTheory.CyclotomicQRProduct.rootFactor
#check DkMath.NumberTheory.CyclotomicQRProduct.rootPowerMap_injective_on_nonzero
#check DkMath.NumberTheory.CyclotomicQRProduct.qr_product_mul_qnr_product
#check DkMath.NumberTheory.CyclotomicQRGaloisAction.Rpoly
#check DkMath.NumberTheory.CyclotomicQRGaloisAction.Dpoly
#check DkMath.NumberTheory.CyclotomicQRGaloisAction.qrFactorPoly
#check DkMath.NumberTheory.CyclotomicQRGaloisAction.qnrFactorPoly
#check DkMath.NumberTheory.CyclotomicQRGaussNormalization.quadraticGauss
#check DkMath.NumberTheory.CyclotomicQRGaussNormalization.quadraticGauss_sq
#check DkMath.NumberTheory.CyclotomicQRGaussNormalization.quadraticGauss_ne_zero
#check DkMath.NumberTheory.CyclotomicQRGaussNormalization.quadraticGauss_ne_zero_of_char_ne

#check gaussSum_ne_zero_of_nontrivial
#check gaussSum_sq
#check CharP.cast_eq_zero_iff
#check ZMod.ringChar_zmod_n

#check Polynomial.isRoot_cyclotomic_iff
#check Polynomial.isRoot_cyclotomic_iff_charZero
#check IsAlgClosed.exists_root
#check primitiveRoots
#check IsPrimitiveRoot
#check Polynomial.isUnit_resultant_iff_isCoprime
#check Polynomial.resultant_map_map
#check CyclotomicRing
#check AdjoinRoot
#check AdjoinRoot.mk
#check IsPrimitiveRoot.adjoinEquivRingOfIntegers

#check DkMath.CosmicFormula.GTail_one_eq_GTailCyclotomicShell_of_ne_zero
#check DkMath.FLT.Prime.PrimeAdicFactorPacket.residual_not_prime_sq
#check DkMath.FLT.Prime.PrimeAdicFactorPacket.coprime_gap_unit
#check DkMath.FLT.Prime.PrimeAdicPowerSplit.residual_eq
#check DkMath.NumberTheory.TraceOneQuadratic.PrimeDiscriminantPacket
#check DkMath.NumberTheory.TraceOneQuadratic.PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
#check DkMath.NumberTheory.TraceOneQuadratic.ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
#check DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow
