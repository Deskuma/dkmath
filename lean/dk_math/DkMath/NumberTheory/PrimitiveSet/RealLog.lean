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

end DkMath.NumberTheory.PrimitiveSet
