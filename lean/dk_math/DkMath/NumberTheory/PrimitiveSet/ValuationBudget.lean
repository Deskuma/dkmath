/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.RealLog

#print "file: DkMath.NumberTheory.PrimitiveSet.ValuationBudget"

namespace DkMath.NumberTheory.PrimitiveSet

/--
The selected natural-number bases are prime-valued on the index.

This is the valuation-budget analogue of the earlier duplicate-free route's
prime-valued input.
-/
def NatPrimeValuedOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) : Prop :=
  ∀ i, i ∈ I → Nat.Prime (pOf i)

/--
Multiplicity of a base value on the selected index.

This counts how many selected labels read the same base value `p`.
-/
def NatBaseMultiplicityOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (p : ℕ) : ℕ :=
  (I.filter fun i => pOf i = p).card

/--
Base-prime multiplicity budget against the prime factorization of `n`.

For every prime `p`, the number of selected occurrences of `p` must fit inside
the exponent of `p` in `n`.
-/
def NatBaseMultiplicityBudgetOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  ∀ p, Nat.Prime p → NatBaseMultiplicityOn I pOf p ≤ n.factorization p

/-- Unfolding helper for `NatBaseMultiplicityOn`. -/
theorem natBaseMultiplicityOn_eq_card_filter
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (p : ℕ) :
    NatBaseMultiplicityOn I pOf p =
      (I.filter fun i => pOf i = p).card :=
  rfl

/-- Unfolding helper for `NatBaseMultiplicityBudgetOn`. -/
theorem natBaseMultiplicityBudgetOn_iff
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) :
    NatBaseMultiplicityBudgetOn I pOf n ↔
      ∀ p, Nat.Prime p → NatBaseMultiplicityOn I pOf p ≤ n.factorization p :=
  Iff.rfl

/--
For prime-valued selected bases, the exponent of a prime `p` in the selected
product is exactly the number of selected occurrences of `p`.
-/
theorem factorization_prod_primeValued_eq_multiplicity_of_prime
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (hprime : NatPrimeValuedOn I pOf)
    {p : ℕ}
    (hp : Nat.Prime p) :
    (I.prod fun i => pOf i).factorization p =
      NatBaseMultiplicityOn I pOf p := by
  classical
  have hnonzero : ∀ i ∈ I, pOf i ≠ 0 := by
    intro i hi
    exact (hprime i hi).ne_zero
  rw [Nat.factorization_prod_apply hnonzero]
  calc
    (I.sum fun i => (pOf i).factorization p)
        = I.sum fun i => if pOf i = p then 1 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hpi : pOf i = p
          · subst hpi
            simp [Nat.Prime.factorization_self hp]
          · simp [Nat.Prime.factorization (hprime i hi), hpi]
    _ = NatBaseMultiplicityOn I pOf p := by
      simp [NatBaseMultiplicityOn]

/--
A multiplicity budget supplies divisibility of the selected base product by
`n`.

This is the core natural-number bridge for the repeated-base route.
-/
theorem natProductDvdOn_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hprime : NatPrimeValuedOn I pOf)
    (hbudget : NatBaseMultiplicityBudgetOn I pOf n) :
    NatProductDvdOn I pOf n := by
  classical
  unfold NatProductDvdOn
  by_cases hn : n = 0
  · rw [hn]
    exact dvd_zero _
  · have hprod_ne : (I.prod fun i => pOf i) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr fun i hi => (hprime i hi).ne_zero
    rw [← Nat.factorization_le_iff_dvd hprod_ne hn]
    rw [Finsupp.le_def]
    intro p
    by_cases hp : Nat.Prime p
    · rw [factorization_prod_primeValued_eq_multiplicity_of_prime I pOf hprime hp]
      exact hbudget p hp
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _

/-- Prime-valued selected bases satisfy the real/log nonnegativity condition. -/
theorem realLogNonnegOn_of_natPrimeValuedOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (hprime : NatPrimeValuedOn I pOf) :
    RealLogNonnegOn I pOf := by
  intro i hi
  exact le_of_lt (hprime i hi).one_lt

/-- A multiplicity budget supplies the selected natural-number product bound. -/
theorem natProductBoundOn_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    {n : ℕ}
    (hn : 0 < n)
    (hprime : NatPrimeValuedOn I pOf)
    (hbudget : NatBaseMultiplicityBudgetOn I pOf n) :
    NatProductBoundOn I pOf n :=
  natProductBoundOn_of_product_dvd I pOf hn
    (natProductDvdOn_of_multiplicityBudget I pOf n hprime hbudget)

/--
A multiplicity budget supplies the bundled real/log product budget for
prime-valued selected bases.
-/
theorem realLogProductBudget_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hn : 1 < n)
    (hprime : NatPrimeValuedOn I pOf)
    (hbudget : NatBaseMultiplicityBudgetOn I pOf n) :
    RealLogProductBudget I pOf n :=
  ⟨realLogNonnegOn_of_natPrimeValuedOn I pOf hprime,
    hn,
    natProductBoundOn_of_multiplicityBudget I pOf
      (Nat.lt_trans Nat.zero_lt_one hn) hprime hbudget⟩

/--
The log-ratio real provider is sub-probability under a prime-valued
multiplicity budget.
-/
theorem realLogRatioWeightProvider_subProbability_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hn : 1 < n)
    (hprime : NatPrimeValuedOn I pOf)
    (hbudget : NatBaseMultiplicityBudgetOn I pOf n) :
    (realLogRatioWeightProvider I pOf n
      (realLogNonnegOn_of_natPrimeValuedOn I pOf hprime) hn).SubProbability :=
  realLogRatioWeightProvider_subProbability_of_productBudget I pOf n
    (realLogProductBudget_of_multiplicityBudget I pOf n hn hprime hbudget)

end DkMath.NumberTheory.PrimitiveSet
