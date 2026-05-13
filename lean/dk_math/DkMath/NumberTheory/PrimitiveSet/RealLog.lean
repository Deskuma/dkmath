/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.RealWeightedPath

#print "file: DkMath.NumberTheory.PrimitiveSet.RealLog"

namespace DkMath.NumberTheory.PrimitiveSet

/--
Natural-number log nonnegativity for the numerator side of the real/log route.

The boundary case `p = 1` is allowed: it gives `Real.log 1 = 0`.
-/
theorem real_log_nat_nonneg_of_one_le
    {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ Real.log (p : ℝ) := by
  exact Real.log_nonneg (by exact_mod_cast hp)

/--
Natural-number log positivity for the denominator side of the real/log route.

This strict form is the one needed before dividing by `Real.log (n : ℝ)`.
-/
theorem real_log_nat_pos_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    0 < Real.log (n : ℝ) := by
  exact Real.log_pos (by exact_mod_cast hn)

/--
External budget predicate for the real/log route.

This records the analytic/numerical input
`Σ log (pOf q) ≤ log n` without trying to derive it from prime-power labels.
-/
def RealLogBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  (I.sum fun q => Real.log (pOf q : ℝ)) ≤ Real.log (n : ℝ)

/--
Index-local positivity condition for logarithmic numerators.

It excludes the problematic `pOf q = 0` case and is weak enough to allow the
boundary value `pOf q = 1`, where the logarithm is `0`.
-/
def RealLogNonnegOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) : Prop :=
  ∀ q, q ∈ I → 1 ≤ pOf q

/-- Natural-number product bound on the selected bases. -/
def NatProductBoundOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  (I.prod fun q => pOf q) ≤ n

/-- Natural-number product divisibility for the selected bases. -/
def NatProductDvdOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  (I.prod fun q => pOf q) ∣ n

/-- Pairwise coprimality of the selected natural-number bases. -/
def NatPairwiseCoprimeOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) : Prop :=
  ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → Nat.Coprime (pOf i) (pOf j)

/-- Pairwise distinctness of the selected natural-number bases. -/
def NatPairwiseDistinctOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) : Prop :=
  ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → pOf i ≠ pOf j

/--
Pairwise distinct selected prime values are pairwise coprime.

This is the abstract bridge for the duplicate-free route.
-/
theorem natPairwiseCoprimeOn_of_pairwise_distinct_prime
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (hprime : ∀ i, i ∈ I → Nat.Prime (pOf i))
    (hdistinct : NatPairwiseDistinctOn I pOf) :
    NatPairwiseCoprimeOn I pOf := by
  intro i hi j hj hij
  exact (Nat.coprime_primes (hprime i hi) (hprime j hj)).mpr
    (hdistinct i hi j hj hij)

/--
Pairwise-coprime selected divisors multiply to a divisor of `n`.

This is the first abstract supply route for `NatProductBoundOn`; it deliberately
does not mention prime-power witnesses yet.
-/
theorem natProductDvdOn_of_pairwise_coprime_dvd
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hcop : NatPairwiseCoprimeOn I pOf)
    (hdvd : ∀ i, i ∈ I → pOf i ∣ n) :
    NatProductDvdOn I pOf n := by
  classical
  unfold NatProductDvdOn
  revert hcop hdvd
  induction I using Finset.induction_on with
  | empty =>
    intro _ _
    simp
  | insert a s ha ih =>
    intro hcop hdvd
    rw [Finset.prod_insert ha]
    have hsdvd : (s.prod fun i => pOf i) ∣ n := by
      exact ih
        (fun i hi j hj hij =>
          hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
        (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))
    have hadvd : pOf a ∣ n := hdvd a (Finset.mem_insert_self a s)
    have hcop_prod : Nat.Coprime (pOf a) (s.prod fun i => pOf i) := by
      exact Nat.Coprime.prod_right (by
        intro b hb
        exact hcop a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb) (by
          intro hab
          exact ha (by simpa [hab] using hb)))
    exact hcop_prod.mul_dvd_of_dvd_of_dvd hadvd hsdvd

/-- A positive target turns selected product divisibility into a product bound. -/
theorem natProductBoundOn_of_product_dvd
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    {n : ℕ}
    (hn : 0 < n)
    (hprod : NatProductDvdOn I pOf n) :
    NatProductBoundOn I pOf n :=
  Nat.le_of_dvd hn hprod

/--
Pairwise-coprime selected divisors of a positive `n` satisfy the selected
product bound.
-/
theorem natProductBoundOn_of_pairwise_coprime_dvd
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    {n : ℕ}
    (hn : 0 < n)
    (hcop : NatPairwiseCoprimeOn I pOf)
    (hdvd : ∀ i, i ∈ I → pOf i ∣ n) :
    NatProductBoundOn I pOf n :=
  natProductBoundOn_of_product_dvd I pOf hn
    (natProductDvdOn_of_pairwise_coprime_dvd I pOf n hcop hdvd)

/--
Bundled product-budget hypotheses for the real/log provider route.

This is the interface later prime-power code should try to supply.
-/
def RealLogProductBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  RealLogNonnegOn I pOf ∧ 1 < n ∧ NatProductBoundOn I pOf n

/-- The index-local condition gives nonnegative logarithmic numerators. -/
theorem real_log_nat_nonneg_on
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (hp : RealLogNonnegOn I pOf) :
    ∀ q, q ∈ I → 0 ≤ Real.log (pOf q : ℝ) := by
  intro q hq
  exact real_log_nat_nonneg_of_one_le (hp q hq)

/--
Log-ratio finite-sum bound from an external log budget.

This is the first theorem where the expression `log p / log n` appears in the
R-version route.  It deliberately treats the budget as an input.
-/
theorem real_log_ratio_sum_le_one
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hn : 1 < n)
    (hbudget : RealLogBudget I pOf n) :
    (I.sum fun q =>
      Real.log (pOf q : ℝ) / Real.log (n : ℝ)) ≤ 1 :=
  real_ratio_sum_le_one
    I
    (fun q => Real.log (pOf q : ℝ))
    (Real.log (n : ℝ))
    (real_log_nat_pos_of_one_lt hn)
    hbudget

/--
The finite real provider whose weights are `log (pOf q) / log n`.

The hypotheses only ensure itemwise nonnegativity and denominator positivity.
Sub-probability is supplied separately by `RealLogBudget`.
-/
noncomputable def realLogRatioWeightProvider
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : RealLogNonnegOn I pOf)
    (hn : 1 < n) :
    RealWeightProvider ι where
  index := I
  weight := fun q => Real.log (pOf q : ℝ) / Real.log (n : ℝ)
  weight_nonneg := by
    intro q hq
    exact div_nonneg
      (real_log_nat_nonneg_on I pOf hp q hq)
      (le_of_lt (real_log_nat_pos_of_one_lt hn))

/--
The log-ratio real provider is sub-probability under the external log budget.
-/
theorem realLogRatioWeightProvider_subProbability
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : RealLogNonnegOn I pOf)
    (hn : 1 < n)
    (hbudget : RealLogBudget I pOf n) :
    (realLogRatioWeightProvider I pOf n hp hn).SubProbability := by
  unfold RealWeightProvider.SubProbability RealWeightProvider.totalWeight
  exact real_log_ratio_sum_le_one I pOf n hn hbudget

/-- A finite product of positive real terms is positive. -/
theorem real_finset_prod_pos_of_pos
    {ι : Type _}
    (I : Finset ι)
    (a : ι → ℝ)
    (ha : ∀ i, i ∈ I → 0 < a i) :
    0 < I.prod a :=
  Finset.prod_pos ha

/-- The logarithm of a finite product of positive real terms is the sum of logs. -/
theorem real_log_prod_eq_sum_log_of_pos
    {ι : Type _}
    (I : Finset ι)
    (a : ι → ℝ)
    (ha : ∀ i, i ∈ I → 0 < a i) :
    Real.log (I.prod a) = I.sum fun i => Real.log (a i) :=
  Real.log_prod (s := I) (f := a) fun i hi => ne_of_gt (ha i hi)

/-- Alias in the direction used by product-budget-to-log-budget arguments. -/
theorem real_sum_log_eq_log_prod_of_pos
    {ι : Type _}
    (I : Finset ι)
    (a : ι → ℝ)
    (ha : ∀ i, i ∈ I → 0 < a i) :
    (I.sum fun i => Real.log (a i)) = Real.log (I.prod a) :=
  (real_log_prod_eq_sum_log_of_pos I a ha).symm

/--
Product-budget-to-log-sum bound for positive real finite products.

This is the real-valued core of the later `RealLogBudget` supply route.
-/
theorem real_sum_log_le_log_of_prod_le
    {ι : Type _}
    (I : Finset ι)
    (a : ι → ℝ)
    (N : ℝ)
    (ha : ∀ i, i ∈ I → 0 < a i)
    (_hN : 0 < N)
    (hprod : I.prod a ≤ N) :
    (I.sum fun i => Real.log (a i)) ≤ Real.log N := by
  rw [real_sum_log_eq_log_prod_of_pos I a ha]
  exact Real.log_le_log (real_finset_prod_pos_of_pos I a ha) hprod

/-- Cast a finite product of natural numbers to a real finite product. -/
theorem real_finset_prod_nat_cast
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ) :
    ((I.prod fun q => pOf q : ℕ) : ℝ) =
      I.prod fun q => (pOf q : ℝ) := by
  simp [Nat.cast_prod]

/--
Supply a real log budget from a natural-number product bound.

This is still independent of prime-power labels; it only translates a product
bound on selected natural numbers into the external `RealLogBudget`.
-/
theorem realLogBudget_of_nat_product_le
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : RealLogNonnegOn I pOf)
    (hn : 0 < n)
    (hprod : (I.prod fun q => pOf q) ≤ n) :
    RealLogBudget I pOf n := by
  unfold RealLogBudget
  refine real_sum_log_le_log_of_prod_le
    I (fun q => (pOf q : ℝ)) (n : ℝ) ?ha ?hN ?hprodReal
  · intro q hq
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (hp q hq))
  · exact_mod_cast hn
  · rw [← real_finset_prod_nat_cast I pOf]
    exact_mod_cast hprod

/--
The log-ratio real provider is sub-probability under a natural-number product
bound on the selected bases.
-/
theorem realLogRatioWeightProvider_subProbability_of_nat_product_le
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hp : RealLogNonnegOn I pOf)
    (hn : 1 < n)
    (hprod : (I.prod fun q => pOf q) ≤ n) :
    (realLogRatioWeightProvider I pOf n hp hn).SubProbability :=
  realLogRatioWeightProvider_subProbability I pOf n hp hn
    (realLogBudget_of_nat_product_le I pOf n hp
      (Nat.lt_trans Nat.zero_lt_one hn) hprod)

/--
The log-ratio real provider is sub-probability under the bundled product-budget
predicate.
-/
theorem realLogRatioWeightProvider_subProbability_of_productBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hbudget : RealLogProductBudget I pOf n) :
    (realLogRatioWeightProvider I pOf n hbudget.1 hbudget.2.1).SubProbability :=
  realLogRatioWeightProvider_subProbability_of_nat_product_le
    I pOf n hbudget.1 hbudget.2.1 hbudget.2.2

end DkMath.NumberTheory.PrimitiveSet
