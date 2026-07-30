/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExceptionalSplit
import DkMath.NumberTheory.PrimitiveSet.FullChannelLogSum

#print "file: DkMath.ABC.GNValuationExcess"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Finite valuation excess on GN

The radical records one copy of every prime in the factorization support.
`valuationExcess m` records all remaining copies, with logarithmic weight.
For nonzero `m`, these two finite quantities reconstruct `log m` exactly.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
The logarithmic multiplicity discarded by `rad`.

The subtraction is in `ℕ`, so every summand is visibly nonnegative before
casting to `ℝ`.  On factorization support, every valuation is at least one.
-/
noncomputable def valuationExcess (m : ℕ) : ℝ :=
  ∑ q ∈ m.factorization.support,
    ((m.factorization q - 1 : ℕ) : ℝ) * Real.log (q : ℝ)

/-- The GN specialization of finite valuation excess. -/
noncomputable def GNValuationExcess (n a b : ℕ) : ℝ :=
  valuationExcess (GN n a b)

/-- The part of GN excess supported on exponent-exceptional primes `q ∣ n`. -/
noncomputable def GNExceptionalValuationExcess (n a b : ℕ) : ℝ :=
  ∑ q ∈ (GN n a b).factorization.support.filter (fun q => q ∣ n),
    (((GN n a b).factorization q - 1 : ℕ) : ℝ) * Real.log (q : ℝ)

/-- The part of GN excess supported on non-exceptional primes `q ∤ n`. -/
noncomputable def GNNonExceptionalValuationExcess (n a b : ℕ) : ℝ :=
  ∑ q ∈ (GN n a b).factorization.support.filter (fun q => ¬ q ∣ n),
    (((GN n a b).factorization q - 1 : ℕ) : ℝ) * Real.log (q : ℝ)

/-- Factorization support gives a positive valuation. -/
theorem one_le_factorization_of_mem_support
    {m q : ℕ} (hq : q ∈ m.factorization.support) :
    1 ≤ m.factorization q := by
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hq)

/--
The exact finite decomposition of logarithmic size into radical support and
valuation excess.
-/
theorem log_eq_log_rad_add_valuationExcess
    {m : ℕ} (hm : m ≠ 0) :
    Real.log (m : ℝ) = Real.log (rad m : ℝ) + valuationExcess m := by
  have hfactorLog :
      (∑ q ∈ m.factorization.support,
          (m.factorization q : ℝ) * Real.log (q : ℝ)) =
        Real.log (m : ℝ) :=
    DkMath.NumberTheory.PrimitiveSet.sum_factorization_mul_log_eq_log_nat hm
  have hradLog :
      Real.log (rad m : ℝ) =
        ∑ q ∈ m.factorization.support, Real.log (q : ℝ) := by
    simpa [rad] using support_prod_log_eq_sum_log m
  rw [← hfactorLog, hradLog, valuationExcess, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hq_one : 1 ≤ m.factorization q :=
    one_le_factorization_of_mem_support hq
  rw [Nat.cast_sub hq_one]
  ring

/-- Exact logarithmic support/excess identity for a nonzero GN kernel. -/
theorem log_GN_eq_log_rad_add_GNValuationExcess
    {n a b : ℕ} (hGN : GN n a b ≠ 0) :
    Real.log ((GN n a b : ℕ) : ℝ) =
      Real.log (rad (GN n a b) : ℝ) + GNValuationExcess n a b := by
  simpa [GNValuationExcess] using log_eq_log_rad_add_valuationExcess hGN

/-- Exact partition of GN excess into exponent-exceptional and non-exceptional parts. -/
theorem GNValuationExcess_eq_exceptional_add_nonExceptional
    (n a b : ℕ) :
    GNValuationExcess n a b =
      GNExceptionalValuationExcess n a b +
        GNNonExceptionalValuationExcess n a b := by
  classical
  unfold GNValuationExcess valuationExcess
    GNExceptionalValuationExcess GNNonExceptionalValuationExcess
  exact (Finset.sum_filter_add_sum_filter_not
    (s := (GN n a b).factorization.support)
    (p := fun q => q ∣ n)
    (f := fun q =>
      (((GN n a b).factorization q - 1 : ℕ) : ℝ) * Real.log (q : ℝ))).symm

/--
Positive ABC coordinates and `2 ≤ n` supply the nonzero condition required by
the exact GN support/excess identity.
-/
theorem Triple.log_GN_eq_log_rad_add_GNValuationExcess
    (T : Triple) {n : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) :
    Real.log ((GN n T.a T.b : ℕ) : ℝ) =
      Real.log (rad (GN n T.a T.b) : ℝ) +
        GNValuationExcess n T.a T.b := by
  exact DkMath.ABC.log_GN_eq_log_rad_add_GNValuationExcess
    (n := n) (a := T.a) (b := T.b)
    (GN_ne_zero_nat_of_two_le hn ha hb)

end DkMath.ABC
