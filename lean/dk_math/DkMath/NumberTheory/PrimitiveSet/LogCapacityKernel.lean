/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Kernel.Normalize
import DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.Kernel

namespace PrimePowerWitnessProvider

/--
The selected witness base-prime logarithms fit inside the source state's log
capacity.  This is the capacity-kernel form of the R/log valuation-budget route.
-/
theorem basePrimeOf_logCapacity_outgoing_le
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (I.sum fun q => Real.log (W.basePrimeOf n I hI q : ℝ)) ≤
      Real.log (n : ℝ) :=
  realLogBudget_of_nat_product_le I (W.basePrimeOf n I hI) n
    (W.basePrimeOf_realLogNonnegOn n I hI)
    (Nat.lt_trans Nat.zero_lt_one hn)
    (W.basePrimeOf_natProductBoundOn_of_multiplicityBudget n I hI
      (Nat.lt_trans Nat.zero_lt_one hn)
      (W.basePrimeOf_multiplicityBudgetOn n I hI
        (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hn))))

/--
Local DkMath log-capacity kernel at a fixed source `n` and selected channel set
`I`.  The parent state is `Unit`; all source data is closed over by the kernel.
-/
noncomputable def logCapacityKernel
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    CapacityKernel Unit ℕ where
  children := fun _ => I
  capacity := fun _ => Real.log (n : ℝ)
  cost := fun _ q => Real.log (W.basePrimeOf n I hI q : ℝ)
  cost_nonneg := by
    intro _ q hq
    exact real_log_nat_nonneg_of_one_le
      (W.basePrimeOf_realLogNonnegOn n I hI q hq)
  outgoing_le := by
    intro _
    exact W.basePrimeOf_logCapacity_outgoing_le n I hI hn

/--
The normalized local log-capacity kernel has total outgoing mass at most one.
-/
theorem logCapacityKernel_normalizedOutgoing_le_one
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (W.logCapacityKernel n I hI hn).normalizedOutgoing () ≤ 1 :=
  (W.logCapacityKernel n I hI hn).normalizedOutgoing_le_one ()
    (real_log_nat_pos_of_one_lt hn)

/--
Expression-level normalized sub-probability theorem for the local log-capacity
kernel.  This is the Markov/sub-Markov shadow of the capacity bound.
-/
theorem logCapacityKernel_normalized_subProbability
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (I.sum fun q =>
      Real.log (W.basePrimeOf n I hI q : ℝ) / Real.log (n : ℝ)) ≤ 1 := by
  simpa [logCapacityKernel, CapacityKernel.normalizedWeight] using
    (W.logCapacityKernel n I hI hn).normalizedWeight_subProbability ()
      (real_log_nat_pos_of_one_lt hn)

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
