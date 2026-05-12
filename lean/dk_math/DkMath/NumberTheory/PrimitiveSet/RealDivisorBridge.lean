/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel
import DkMath.NumberTheory.PrimitiveSet.RealLog

#print "file: DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge"

namespace DkMath.NumberTheory.PrimitiveSet

namespace PrimePowerWitnessProvider

/--
The base-prime reader supplied by a witness provider satisfies the real/log
nonnegativity condition on the selected sub-index.
-/
theorem basePrimeOf_realLogNonnegOn
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    RealLogNonnegOn I (W.basePrimeOf n I hI) :=
  W.basePrimeOf_one_le n I hI

/--
Bundle the witness-provider base-prime reader into the real/log product-budget
interface, assuming the selected base product bound.
-/
theorem basePrimeOf_realLogProductBudget_of_productBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hprod : NatProductBoundOn I (W.basePrimeOf n I hI) n) :
    RealLogProductBudget I (W.basePrimeOf n I hI) n :=
  ⟨W.basePrimeOf_realLogNonnegOn n I hI, hn, hprod⟩

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
