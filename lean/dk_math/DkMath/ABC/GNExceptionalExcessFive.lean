/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNOddPrimeExceptionalExcess
import DkMath.ABC.GNFinalBudgetBridge

#print "file: DkMath.ABC.GNExceptionalExcessFive"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Vanishing of the exceptional GN excess at exponent five

This module connects the local factorization-one result at exponent five to
the exceptional filtered sum and its affine budget.  No positivity hypotheses
on the coordinates of an ABC triple are needed.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
The exponent-exceptional valuation excess vanishes identically at exponent
five for an ABC triple.
-/
theorem Triple.GNExceptionalValuationExcess_five_eq_zero
    (T : Triple) :
    GNExceptionalValuationExcess 5 T.a T.b = 0 := by
  classical
  unfold GNExceptionalValuationExcess
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hqSupport, hqDvdFive⟩ := Finset.mem_filter.mp hq
  have hqPrime : q.Prime := by
    rw [Nat.support_factorization] at hqSupport
    exact Nat.prime_of_mem_primeFactors hqSupport
  have hqEq : q = 5 :=
    (Nat.prime_dvd_prime_iff_eq hqPrime Nat.prime_five).mp hqDvdFive
  subst q
  have h5GN : 5 ∣ GN 5 T.a T.b :=
    Nat.dvd_of_factorization_pos (Finsupp.mem_support_iff.mp hqSupport)
  rw [factorization_five_GN_five_eq_one_of_dvd T.hcop h5GN]
  simp

/--
At exponent five, the exceptional affine excess budget is exactly zero.
-/
theorem Triple.GNExceptionalExcessBudgetAffine_five_zero
    (T : Triple) :
    GNExceptionalExcessBudgetAffine T 5 0 0 := by
  unfold GNExceptionalExcessBudgetAffine
  rw [T.GNExceptionalValuationExcess_five_eq_zero]
  simp

end DkMath.ABC
