/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.PrimeGauge.PrimorialSync
import DkMath.NumberTheory.Primitive.PHZ30

#print "file: DkMathTest.NumberTheory.PrimeGaugeSynchronization"

namespace DkMathTest.NumberTheory.PrimeGaugeSynchronization

open DkMath.CosmicFormula.Rotation.CF2D
open DkMath.NumberTheory
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimeGauge

example : primeWorldModulus primeWorld235 = 30 := by
  decide

example : ∀ p ∈ primeWorld235, regularKernel p ^ 60 = 1 := by
  exact (all_primeGauge_return_iff_worldModulus_dvd
    knownPrimeScales_primeWorld235).mpr (by norm_num [primeWorldModulus, primeWorld235])

example (hreturn : ∀ p ∈ primeWorld235, regularKernel p ^ 42 = 1) :
    primeWorldModulus primeWorld235 ∣ 42 := by
  exact (all_primeGauge_return_iff_worldModulus_dvd
    knownPrimeScales_primeWorld235).mp hreturn

example : primeWorldModulus primeWorld235 ≤ 60 := by
  have hsync := primeGauge_worldModulus_is_first_positive_sync
    knownPrimeScales_primeWorld235
  apply hsync.2.2 60 (by norm_num)
  exact (all_primeGauge_return_iff_worldModulus_dvd
    knownPrimeScales_primeWorld235).mpr (by norm_num [primeWorldModulus, primeWorld235])

#print axioms all_primeGauge_return_iff_worldModulus_dvd
#print axioms primeGauge_worldModulus_is_first_positive_sync

end DkMathTest.NumberTheory.PrimeGaugeSynchronization
