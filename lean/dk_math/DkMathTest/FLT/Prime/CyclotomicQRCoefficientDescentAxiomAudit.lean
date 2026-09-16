/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRCoefficientDescent
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

#print "file: DkMathTest.FLT.Prime.CyclotomicQRCoefficientDescentAxiomAudit"

/-!
Pinned coefficient, fixed-field, cyclotomic, and integrality declarations used
or audited by Phase 10.
-/

#check MvPolynomial.coeff_map
#check MvPolynomial.mem_range_map_iff_coeffs_subset
#check MvPolynomial.map_injective

#check IntermediateField.mem_fixedField_iff
#check IsGalois.fixedField_top
#check IsGalois.fixedField_fixingSubgroup
#check IsGalois.mem_range_algebraMap_iff_fixed
#check IntermediateField.mem_bot

#check IsCyclotomicExtension.isGalois
#check IsCyclotomicExtension.finiteDimensional

#check IsCyclotomicExtension.integral
#check IsCyclotomicExtension.ringOfIntegers
#check Algebra.IsIntegral
#check IsIntegral
#check integralClosure
#check IsIntegralClosure.isIntegral_iff
#check IsIntegrallyClosed.isIntegral_iff
#check Rat.ringOfIntegersEquiv
#check Rat.ringOfIntegersEquiv_apply_coe

#print axioms DkMath.NumberTheory.CyclotomicQRCoefficientDescent.coeff_fixed_of_map_eq
#print axioms DkMath.NumberTheory.CyclotomicQRCoefficientDescent.coeff_Rpoly_mem_fixedField
#print axioms DkMath.NumberTheory.CyclotomicQRCoefficientDescent.coeff_Dpoly_sq_mem_fixedField
#print axioms DkMath.NumberTheory.CyclotomicQRCoefficientDescent.coeff_Rpoly_mem_range_algebraMap
#print axioms DkMath.NumberTheory.CyclotomicQRCoefficientDescent.coeff_Dpoly_sq_mem_range_algebraMap
#print axioms DkMath.NumberTheory.CyclotomicQRCoefficientDescent.exists_Rpoly_over_base
#print axioms DkMath.NumberTheory.CyclotomicQRCoefficientDescent.exists_Dpoly_sq_over_base
