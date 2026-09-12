/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRGaloisRealization
import Mathlib.NumberTheory.Cyclotomic.Gal

#print "file: DkMathTest.FLT.Prime.CyclotomicQRGaloisRealizationAxiomAudit"

/-!
Pinned realization declarations and the Phase-9 public theorem audit.
-/

#check IsPrimitiveRoot.autToPow
#check IsPrimitiveRoot.autToPow_spec
#check IsPrimitiveRoot.autToPow_injective
#check IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
#check IsCyclotomicExtension.autEquivPow
#check IsCyclotomicExtension.fromZetaAut
#check IsCyclotomicExtension.fromZetaAut_spec
#check galCyclotomicEquivUnitsZMod
#check galXPowEquivUnitsZMod
#check IsCyclotomicExtension.isGalois

#print axioms DkMath.NumberTheory.CyclotomicQRGaloisRealization.coe_nonzeroExponentUnit
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisRealization.exists_cyclotomicAut_pow
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisRealization.cyclotomicAut_power_spec
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisRealization.map_Rpoly_of_cyclotomicAut
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisRealization.map_Dpoly_of_cyclotomicAut
#print axioms DkMath.NumberTheory.CyclotomicQRGaloisRealization.map_Dpoly_sq_of_cyclotomicAut
