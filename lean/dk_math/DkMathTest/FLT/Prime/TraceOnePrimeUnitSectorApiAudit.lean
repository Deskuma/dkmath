/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadraticField
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

#print "file: DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorApiAudit"

#check NumberField.Units.rank
#check NumberField.Units.fundSystem
#check NumberField.Units.exist_unique_eq_mul_prod
#check NumberField.Units.basisModTorsion
#check NumberField.Units.finrank_modTorsion
#check NumberField.Units.rank_modTorsion
#check NumberField.InfinitePlace.nrRealPlaces
#check NumberField.InfinitePlace.nrComplexPlaces
#check NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
#check NumberField.sign_discr
#check NumberField.IsTotallyReal
#check NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
#check NumberField.IsTotallyReal.finrank
#check NumberField.RingOfIntegers.equiv
#check RingEquiv.toMonoidHom
#check Units.map
#check Units.val_zpow_eq_zpow_val
#check zpow_add₀
#check zpow_mul
#check Int.ediv_emod_unique
#check Int.ediv_mul_add_emod
#check Int.emod_nonneg
#check Int.emod_lt
