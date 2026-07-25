/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNOddPrimeExceptionalExcess
import DkMath.ABC.GNFinalBudgetBridge

#print "file: DkMath.ABC.GNExceptionalExcessOddPrime"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Vanishing of exceptional GN excess at odd-prime exponents

For an odd prime exponent, the only possible exponent-exceptional support
prime is the exponent itself.  Its GN multiplicity is exactly one, so the
entire exceptional valuation excess and its affine budget vanish.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
The exponent-exceptional valuation excess vanishes at every odd-prime
exponent.
-/
theorem Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p) :
    GNExceptionalValuationExcess p T.a T.b = 0 := by
  classical
  unfold GNExceptionalValuationExcess
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hqSupport, hqDvdP⟩ := Finset.mem_filter.mp hq
  have hqPrime : q.Prime := by
    rw [Nat.support_factorization] at hqSupport
    exact Nat.prime_of_mem_primeFactors hqSupport
  have hqEq : q = p :=
    (Nat.prime_dvd_prime_iff_eq hqPrime hp).mp hqDvdP
  subst q
  have hpGN : p ∣ GN p T.a T.b :=
    Nat.dvd_of_factorization_pos (Finsupp.mem_support_iff.mp hqSupport)
  rw [factorization_GN_prime_eq_one_of_dvd hp hpOdd T.hcop hpGN]
  simp

/-- The exceptional affine excess budget is exactly zero at odd-prime exponents. -/
theorem Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p) :
    GNExceptionalExcessBudgetAffine T p 0 0 := by
  unfold GNExceptionalExcessBudgetAffine
  rw [T.GNExceptionalValuationExcess_eq_zero_of_oddPrime hp hpOdd]
  simp

/--
At an odd-prime exponent, a non-exceptional affine budget is already a budget
for the full GN valuation excess.
-/
theorem Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
    (T : Triple) {p : ℕ} {τn Dn : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hn : GNNonExceptionalExcessBudgetAffine T p τn Dn) :
    GNValuationExcessBudgetAffine T p τn Dn := by
  have he : GNExceptionalExcessBudgetAffine T p 0 0 :=
    T.GNExceptionalExcessBudgetAffine_zero_of_oddPrime hp hpOdd
  simpa using GNValuationExcessBudgetAffine.of_split he hn

end DkMath.ABC
