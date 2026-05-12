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

/--
The log-ratio real provider built from witness-provider base primes is
sub-probability under the selected base product bound.
-/
theorem basePrimeOf_realLogRatioWeightProvider_subProbability_of_productBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hprod : NatProductBoundOn I (W.basePrimeOf n I hI) n) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability :=
  realLogRatioWeightProvider_subProbability_of_productBudget I
    (W.basePrimeOf n I hI) n
    (W.basePrimeOf_realLogProductBudget_of_productBound n I hI hn hprod)

/--
The log-ratio real provider built from witness-provider base primes is
sub-probability when the selected base product is supplied by pairwise-coprime
divisibility into `n`.
-/
theorem basePrimeOf_realLogRatioWeightProvider_subProbability_of_pairwise_coprime_dvd
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hcop : NatPairwiseCoprimeOn I (W.basePrimeOf n I hI))
    (hdvd : ∀ q, q ∈ I → W.basePrimeOf n I hI q ∣ n) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability :=
  W.basePrimeOf_realLogRatioWeightProvider_subProbability_of_productBound n I hI hn
    (natProductBoundOn_of_pairwise_coprime_dvd I (W.basePrimeOf n I hI)
      (Nat.lt_trans Nat.zero_lt_one hn) hcop hdvd)

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
