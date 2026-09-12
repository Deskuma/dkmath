/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRIntegralDescent
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral

#print "file: DkMathTest.FLT.Prime.CyclotomicQRIntegralDescentAxiomAudit"

/-! The pinned integrality and ring-of-integers names used by Phase 11 are
    checked here independently of the production proof. -/

#check IsPrimitiveRoot.isIntegral
#check MvPolynomial.isIntegral_iff_isIntegral_coeff
#check IsIntegral.add
#check IsIntegral.sub
#check IsIntegral.mul
#check IsIntegral.pow
#check isIntegral_algebraMap_iff
#check IsIntegralClosure.isIntegral_iff
#check IsIntegrallyClosed.isIntegral_iff
#check NumberField.RingOfIntegers
#check Rat.ringOfIntegersEquiv
#check Rat.ringOfIntegersEquiv_apply_coe
#check Rat.ringOfIntegersEquiv_symm_apply_coe
#check IsCyclotomicExtension.integral
#check IsCyclotomicExtension.ringOfIntegers
#check MvPolynomial.mem_range_map_iff_coeffs_subset

#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.rootFactorPoly_integral
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.qrFactorPoly_integral
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.qnrFactorPoly_integral
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.Rpoly_integral
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.Dpoly_sq_integral
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.coeff_Rpoly_isIntegral_int
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.coeff_Dpoly_sq_isIntegral_int
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.isIntegral_rat_of_map_isIntegral
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.coeff_R0_isIntegral_int
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.coeff_D20_isIntegral_int
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.rat_isIntegral_iff_exists_int
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.coeff_R0_mem_range_intCast
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.coeff_D20_mem_range_intCast
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.exists_Rpoly_over_int
#print axioms DkMath.NumberTheory.CyclotomicQRIntegralDescent.exists_Dpoly_sq_over_int
