/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.ABCCalibrationSourceDecomposition
import DkMath.ABC.GNDepthPressure

#print "file: DkMath.ABC.GNBalanceDepthLayers"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Local valuation balance layers for the GN channel

This module expands the checkpoint-000 support-minus-depth balance into its
prime-local and finite depth-layer forms.  It records only exact identities
and the local valuation-two pivot; it does not define a global mutation or
prove a monotonicity statement.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- Local non-exceptional GN mass carried by a support prime. -/
noncomputable def GNNonExceptionalLocalMass
    (p a b q : ℕ) : ℝ :=
  ((GN p a b).factorization q : ℝ) * Real.log (q : ℝ)

/-- Local support-minus-depth balance carried by a support prime. -/
noncomputable def GNNonExceptionalLocalBalance
    (p a b q : ℕ) : ℝ :=
  (2 - ((GN p a b).factorization q : ℝ)) * Real.log (q : ℝ)

/-- The checkpoint-000 support mass is the first non-exceptional layer. -/
theorem GNChannelSupportMass_eq_nonExceptionalSupportLogMass
    (T : Triple) (p : ℕ) :
    GNChannelSupportMass T p =
      GNNonExceptionalSupportLogMass p T.a T.b := by
  simpa [GNChannelSupportMass] using
    (GNNonExceptionalSupportLogMass_eq_log_product p T.a T.b).symm

/-- The checkpoint-000 depth mass is the finite repeated-layer cake. -/
theorem GNChannelDepthMass_eq_sum_nonExceptionalDepthMass
    (T : Triple) (p : ℕ) :
    GNChannelDepthMass T p =
      ∑ k ∈ (Finset.range (GN p T.a T.b)).filter (fun k => 2 ≤ k),
        GNNonExceptionalDepthMass p T.a T.b k := by
  simpa [GNChannelDepthMass] using
    GNNonExceptionalValuationExcess_eq_sum_depthMass p T.a T.b

theorem GNNonExceptionalSupportLogMass_add_valuationExcess_eq_sum_localMass
    (p a b : ℕ) :
    GNNonExceptionalSupportLogMass p a b +
        GNNonExceptionalValuationExcess p a b =
      ∑ q ∈ GNNonExceptionalSupport p a b,
        GNNonExceptionalLocalMass p a b q := by
  classical
  unfold GNNonExceptionalSupportLogMass GNNonExceptionalValuationExcess
    GNNonExceptionalSupport GNNonExceptionalLocalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hq_one : 1 ≤ (GN p a b).factorization q :=
    one_le_factorization_of_mem_support
      (Finset.mem_filter.mp hq).1
  rw [Nat.cast_sub hq_one]
  ring

theorem GNNonExceptionalSupportLogMass_sub_valuationExcess_eq_sum_localBalance
    (p a b : ℕ) :
    GNNonExceptionalSupportLogMass p a b -
        GNNonExceptionalValuationExcess p a b =
      ∑ q ∈ GNNonExceptionalSupport p a b,
        GNNonExceptionalLocalBalance p a b q := by
  classical
  unfold GNNonExceptionalSupportLogMass GNNonExceptionalValuationExcess
    GNNonExceptionalSupport GNNonExceptionalLocalBalance
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hq_one : 1 ≤ (GN p a b).factorization q :=
    one_le_factorization_of_mem_support
      (Finset.mem_filter.mp hq).1
  rw [Nat.cast_sub hq_one]
  ring

/-- Total channel mass is the first layer plus all repeated-depth layers. -/
theorem GNChannelMass_eq_firstLayer_add_repeatedLayers
    (T : Triple) (p : ℕ) :
    GNChannelMass T p =
      GNNonExceptionalSupportLogMass p T.a T.b +
        ∑ k ∈ (Finset.range (GN p T.a T.b)).filter (fun k => 2 ≤ k),
          GNNonExceptionalDepthMass p T.a T.b k := by
  rw [GNChannelMass, GNChannelSupportMass_eq_nonExceptionalSupportLogMass,
    GNChannelDepthMass_eq_sum_nonExceptionalDepthMass]

/-- The signed channel balance is first support layer minus repeated layers. -/
theorem GNChannelBalance_eq_firstLayer_sub_repeatedLayers
    (T : Triple) (p : ℕ) :
    GNChannelBalance T p =
      GNNonExceptionalSupportLogMass p T.a T.b -
        ∑ k ∈ (Finset.range (GN p T.a T.b)).filter (fun k => 2 ≤ k),
          GNNonExceptionalDepthMass p T.a T.b k := by
  rw [GNChannelBalance, GNChannelSupportMass_eq_nonExceptionalSupportLogMass,
    GNChannelDepthMass_eq_sum_nonExceptionalDepthMass]

/-- The total channel mass is the sum of prime-local masses. -/
theorem GNChannelMass_eq_sum_nonExceptionalLocalMass
    (T : Triple) (p : ℕ) :
    GNChannelMass T p =
      ∑ q ∈ GNNonExceptionalSupport p T.a T.b,
        GNNonExceptionalLocalMass p T.a T.b q := by
  calc
    GNChannelMass T p =
        GNNonExceptionalSupportLogMass p T.a T.b +
          GNNonExceptionalValuationExcess p T.a T.b := by
      rw [GNChannelMass, GNChannelSupportMass_eq_nonExceptionalSupportLogMass,
        GNChannelDepthMass]
    _ = _ :=
      GNNonExceptionalSupportLogMass_add_valuationExcess_eq_sum_localMass
        p T.a T.b

/-- The signed channel balance is the sum of signed prime-local balances. -/
theorem GNChannelBalance_eq_sum_nonExceptionalLocalBalance
    (T : Triple) (p : ℕ) :
    GNChannelBalance T p =
      ∑ q ∈ GNNonExceptionalSupport p T.a T.b,
        GNNonExceptionalLocalBalance p T.a T.b q := by
  calc
    GNChannelBalance T p =
        GNNonExceptionalSupportLogMass p T.a T.b -
          GNNonExceptionalValuationExcess p T.a T.b := by
      rw [GNChannelBalance, GNChannelSupportMass_eq_nonExceptionalSupportLogMass,
        GNChannelDepthMass]
    _ = _ :=
      GNNonExceptionalSupportLogMass_sub_valuationExcess_eq_sum_localBalance
        p T.a T.b

theorem GNNonExceptionalLocalBalance_eq_log_of_factorization_eq_one
    {p a b q : ℕ}
    (_hq : q ∈ GNNonExceptionalSupport p a b)
    (hv : (GN p a b).factorization q = 1) :
    GNNonExceptionalLocalBalance p a b q = Real.log (q : ℝ) := by
  unfold GNNonExceptionalLocalBalance
  rw [hv]
  norm_num

/-- Valuation depth two is the exact local balance pivot. -/
theorem GNNonExceptionalLocalBalance_eq_zero_of_factorization_eq_two
    {p a b q : ℕ}
    (_hq : q ∈ GNNonExceptionalSupport p a b)
    (hv : (GN p a b).factorization q = 2) :
    GNNonExceptionalLocalBalance p a b q = 0 := by
  unfold GNNonExceptionalLocalBalance
  rw [hv]
  norm_num

/-- Depth at least three contributes strictly on the depth-heavy side. -/
theorem GNNonExceptionalLocalBalance_neg_of_factorization_ge_three
    {p a b q : ℕ}
    (hq : q ∈ GNNonExceptionalSupport p a b)
    (hv : 3 ≤ (GN p a b).factorization q) :
    GNNonExceptionalLocalBalance p a b q < 0 := by
  have hqPrime : Nat.Prime q :=
    (mem_support_factorization_iff.mp
      (Finset.mem_filter.mp hq).1).2.1
  have hlog : 0 < Real.log (q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hqPrime.one_lt
  have hvReal : (3 : ℝ) ≤ ((GN p a b).factorization q : ℝ) := by
    exact_mod_cast hv
  have hcoef :
      (2 : ℝ) - ((GN p a b).factorization q : ℝ) < 0 := by
    linarith
  unfold GNNonExceptionalLocalBalance
  exact mul_neg_of_neg_of_pos hcoef hlog

end DkMath.ABC
