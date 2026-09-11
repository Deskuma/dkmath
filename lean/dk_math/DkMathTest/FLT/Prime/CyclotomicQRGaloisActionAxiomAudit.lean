/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRGaloisAction
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

#print "file: DkMathTest.FLT.Prime.CyclotomicQRGaloisActionAxiomAudit"

/-!
This file records the pinned Mathlib declarations relevant to the next
coefficient/integrality descent stage.  It does not claim that those bridges
are implemented by the abstract polynomial action in this phase.
-/

#check IsPrimitiveRoot.autToPow
#check IsPrimitiveRoot.autToPow_spec
#check IsPrimitiveRoot.autToPow_injective
#check IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
#check IsCyclotomicExtension.autEquivPow
#check galCyclotomicEquivUnitsZMod
#check galXPowEquivUnitsZMod
#check IntermediateField.mem_fixedField_iff
#check IsGalois.fixedField_fixingSubgroup
#check IsCyclotomicExtension.integral
#check IsCyclotomicExtension.isGalois
#check IsCyclotomicExtension.ringOfIntegers

#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.eval_rootFactorPoly
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.eval_qrFactorPoly
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.eval_qnrFactorPoly
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_rootFactorPoly
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_qrFactorPoly_of_square
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_qnrFactorPoly_of_square
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_qrFactorPoly_to_qnr_of_nonsquare
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_qnrFactorPoly_to_qr_of_nonsquare
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_Rpoly_of_square
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_Dpoly_of_square
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_Rpoly_of_nonsquare
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_Dpoly_of_nonsquare
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_Dpoly_sq_of_square
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisAction.map_Dpoly_sq_of_nonsquare
