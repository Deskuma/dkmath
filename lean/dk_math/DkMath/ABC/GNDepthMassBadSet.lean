/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNAverageExcess

#print "file: DkMath.ABC.GNDepthMassBadSet"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Averaged GN depth mass and its bad set

This module packages the log-weighted GN valuation mass for a finite prime
family.  The prime-sensitive average theorem gives a finite Markov bound for
the points where that mass exceeds a positive threshold.

The theorem proves that bad points are sparse in the interval.  It does not
prove that a distinguished ABC coordinate avoids the bad set.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- Log-weighted GN valuation mass at one interval point. -/
noncomputable def GNDepthMassAt
    (Q : Finset ℕ) (p b a : ℕ) : ℝ :=
  ∑ q ∈ Q,
    (padicValNat q (GN p a b) : ℝ) * Real.log (q : ℝ)

/-- The finite set of interval points whose GN depth mass exceeds a threshold. -/
noncomputable def GNDepthMassBadSet
    (Q : Finset ℕ) (p b X : ℕ) (threshold : ℝ) : Finset ℕ :=
  (Finset.Icc 0 X).filter
    (fun a => threshold < GNDepthMassAt Q p b a)

/-- GN depth mass is nonnegative for a finite family of primes. -/
theorem GNDepthMassAt_nonneg
    {Q : Finset ℕ} {p b a : ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q) :
    0 ≤ GNDepthMassAt Q p b a := by
  unfold GNDepthMassAt
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast (hQprime q hq).one_le))

/--
Prime-sensitive finite-family average GN depth-mass bound.
-/
theorem sum_GNDepthMassAt_over_interval_le
    {p b X : ℕ}
    (Q : Finset ℕ)
    (hp : Nat.Prime p)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X, GNDepthMassAt Q p b a ≤
      ∑ q ∈ Q,
        ((((p - 1) *
          ((X + 1) / (q - 1) +
            Nat.log q (p * (X + b) ^ p)) : ℕ) : ℝ) *
              Real.log (q : ℝ)) := by
  unfold GNDepthMassAt
  calc
    ∑ a ∈ Finset.Icc 0 X,
        ∑ q ∈ Q,
          (padicValNat q (GN p a b) : ℝ) *
            Real.log (q : ℝ) =
        ∑ q ∈ Q,
          ∑ a ∈ Finset.Icc 0 X,
            (padicValNat q (GN p a b) : ℝ) *
              Real.log (q : ℝ) := Finset.sum_comm
    _ ≤ ∑ q ∈ Q,
        ((((p - 1) *
          ((X + 1) / (q - 1) +
            Nat.log q (p * (X + b) ^ p)) : ℕ) : ℝ) *
              Real.log (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hnat :=
        sum_padicValNat_GN_le_of_simpleRoot_div_pred
          (X := X) hp (hQprime q hq) (hQp q hq) (hQb q hq)
      have hreal :
          (∑ a ∈ Finset.Icc 0 X,
            (padicValNat q (GN p a b) : ℝ)) ≤
          (((p - 1) *
            ((X + 1) / (q - 1) +
              Nat.log q (p * (X + b) ^ p)) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hreal
        (Real.log_nonneg
          (by exact_mod_cast (hQprime q hq).one_le))

/--
Abstract Markov bound for the GN depth-mass bad set.
-/
theorem card_GNDepthMassBadSet_le_sum
    {Q : Finset ℕ} {p b X : ℕ} {threshold : ℝ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hthreshold : 0 < threshold) :
    ((GNDepthMassBadSet Q p b X threshold).card : ℝ) ≤
      (∑ a ∈ Finset.Icc 0 X, GNDepthMassAt Q p b a) /
        threshold := by
  have hmarkov :=
    markov_card_bound X (GNDepthMassAt Q p b)
      (fun n hn =>
        GNDepthMassAt_nonneg
          (p := p) (b := b) (a := n) hQprime)
      hthreshold
  have heq :
      (Finset.Icc 0 X).filter
          (fun a => a ≤ X ∧ threshold < GNDepthMassAt Q p b a) =
        GNDepthMassBadSet Q p b X threshold := by
    unfold GNDepthMassBadSet
    ext a
    simp
  rw [heq] at hmarkov
  exact hmarkov

/--
Explicit cardinality bound for points with large finite-family GN depth mass.

This is the formal statement that the bad points are sparse.
-/
theorem card_GNDepthMassBadSet_le
    {p b X : ℕ}
    (Q : Finset ℕ)
    (hp : Nat.Prime p)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b)
    {threshold : ℝ}
    (hthreshold : 0 < threshold) :
    ((GNDepthMassBadSet Q p b X threshold).card : ℝ) ≤
      (∑ q ∈ Q,
        ((((p - 1) *
          ((X + 1) / (q - 1) +
            Nat.log q (p * (X + b) ^ p)) : ℕ) : ℝ) *
              Real.log (q : ℝ))) / threshold := by
  calc
    ((GNDepthMassBadSet Q p b X threshold).card : ℝ) ≤
        (∑ a ∈ Finset.Icc 0 X,
          GNDepthMassAt Q p b a) / threshold :=
      card_GNDepthMassBadSet_le_sum hQprime hthreshold
    _ ≤ (∑ q ∈ Q,
        ((((p - 1) *
          ((X + 1) / (q - 1) +
            Nat.log q (p * (X + b) ^ p)) : ℕ) : ℝ) *
              Real.log (q : ℝ))) / threshold := by
      exact div_le_div_of_nonneg_right
        (sum_GNDepthMassAt_over_interval_le
          Q hp hQprime hQp hQb)
        hthreshold.le

end DkMath.ABC
