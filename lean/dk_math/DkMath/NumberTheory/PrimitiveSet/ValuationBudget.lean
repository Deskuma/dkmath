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

end DkMath.NumberTheory.PrimitiveSet
