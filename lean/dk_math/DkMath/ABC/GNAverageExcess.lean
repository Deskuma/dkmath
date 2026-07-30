/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNLegacyTailCountingBridge

#print "file: DkMath.ABC.GNAverageExcess"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Prime-sensitive average GN excess

This module strengthens the fixed-prime average estimates by retaining their
dependence on the prime `q`.  For valuation excess it starts the finite
layer-cake at depth two, so the density contribution is bounded by
`(X+1) / (q * (q-1))`.

The remaining `+1` at each depth is kept explicitly as a boundary-address
term.  No average-to-pointwise compensation is asserted here.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
Prime-sensitive geometric bound for the positive prime-power quotient layers.
-/
theorem sum_div_prime_pow_Icc_le_div_pred
    {q N K : ℕ}
    (hq : Nat.Prime q) :
    ∑ k ∈ Finset.Icc 1 K, N / q ^ k ≤
      N / (q - 1) := by
  have hset : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
    ext k
    simp
  rw [hset]
  exact Nat.geom_sum_Ico_le hq.two_le N (K + 1)

/--
Prime-sensitive geometric bound starting at the excess layer `k = 2`.
-/
theorem sum_div_prime_pow_Icc_two_le
    {q N K : ℕ}
    (hq : Nat.Prime q) :
    ∑ k ∈ Finset.Icc 2 K, N / q ^ k ≤
      N / (q * (q - 1)) := by
  have hgeom :=
    Nat.geom_sum_Ico_le hq.two_le (N / q) K
  have hshift :
      ∑ k ∈ Finset.Icc 2 K, N / q ^ k =
        ∑ j ∈ Finset.Ico 1 K, (N / q) / q ^ j := by
    have hset : Finset.Icc 2 K = Finset.Ico 2 (K + 1) := by
      ext k
      simp
    rw [hset]
    rw [← Finset.sum_Ico_add' (fun k => N / q ^ k) 1 K 1]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [hshift]
  simpa [Nat.div_div_eq_div_mul] using hgeom

/--
Exact finite layer-cake for the natural excess `(V a - 1)`.

Only depth layers `2, ..., K` occur.
-/
theorem sum_nat_pred_eq_sum_card_ge_two
    {α : Type*}
    (s : Finset α) (V : α → ℕ) (K : ℕ)
    (hV : ∀ a ∈ s, V a ≤ K) :
    ∑ a ∈ s, (V a - 1) =
      ∑ k ∈ Finset.Icc 2 K,
        (s.filter (fun a => k ≤ V a)).card := by
  classical
  calc
    ∑ a ∈ s, (V a - 1) =
        ∑ a ∈ s, ∑ k ∈ Finset.Icc 2 K,
          if k ≤ V a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have hcard :
          (Finset.Icc 2 (V a)).card = V a - 1 := by
        rw [Nat.card_Icc]
        omega
      calc
        V a - 1 = (Finset.Icc 2 (V a)).card := hcard.symm
        _ = ((Finset.Icc 2 K).filter (fun k => k ≤ V a)).card := by
          congr 1
          ext k
          simp only [Finset.mem_Icc, Finset.mem_filter]
          constructor
          · intro hk
            exact ⟨⟨hk.1, hk.2.trans (hV a ha)⟩, hk.2⟩
          · intro hk
            exact ⟨hk.1.1, hk.2⟩
        _ = ∑ k ∈ Finset.Icc 2 K,
              if k ≤ V a then 1 else 0 := by simp
    _ = ∑ k ∈ Finset.Icc 2 K, ∑ a ∈ s,
          if k ≤ V a then 1 else 0 := by
      exact Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 2 K,
        (s.filter (fun a => k ≤ V a)).card := by
      apply Finset.sum_congr rfl
      intro k hk
      simp

/--
The `q`-sensitive refinement of the full fixed-prime average valuation bound.
-/
theorem sum_padicValNat_GN_le_of_simpleRoot_div_pred
    {p q b X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X, padicValNat q (GN p a b) ≤
      (p - 1) *
        ((X + 1) / (q - 1) +
          Nat.log q (p * (X + b) ^ p)) := by
  let K := Nat.log q (p * (X + b) ^ p)
  calc
    ∑ a ∈ Finset.Icc 0 X, padicValNat q (GN p a b) ≤
        (p - 1) *
          ∑ k ∈ Finset.Icc 1 K,
            ((X + 1) / q ^ k + 1) :=
      sum_padicValNat_GN_le_of_simpleRoot_layers
        hp hq hqp hqb
    _ = (p - 1) *
        ((∑ k ∈ Finset.Icc 1 K, (X + 1) / q ^ k) +
          (Finset.Icc 1 K).card) := by
      congr 1
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ (p - 1) * ((X + 1) / (q - 1) + K) := by
      apply Nat.mul_le_mul_left
      have hdiv :=
        sum_div_prime_pow_Icc_le_div_pred
          (q := q) (N := X + 1) (K := K) hq
      have hcard : (Finset.Icc 1 K).card = K := by
        rw [Nat.card_Icc]
        omega
      rw [hcard]
      omega

/--
Layer-explicit fixed-prime average valuation-excess bound.
-/
theorem sum_padicValNat_pred_GN_le_of_simpleRoot_layers
    {p q b X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        (padicValNat q (GN p a b) - 1) ≤
      (p - 1) *
        ∑ k ∈ Finset.Icc 2 (Nat.log q (p * (X + b) ^ p)),
          ((X + 1) / q ^ k + 1) := by
  have hb0 : b ≠ 0 := by
    intro hb
    subst b
    exact hqb (dvd_zero q)
  have hb : 0 < b := Nat.pos_of_ne_zero hb0
  let V := fun a => padicValNat q (GN p a b)
  let K := Nat.log q (p * (X + b) ^ p)
  have hGN :
      ∀ a ∈ Finset.Icc 0 X, GN p a b ≠ 0 := by
    intro a ha
    exact GN_ne_zero_of_prime_of_right_ne_zero hp hb0
  have hV :
      ∀ a ∈ Finset.Icc 0 X, V a ≤ K := by
    intro a ha
    dsimp [V, K]
    exact (padicValNat_le_nat_log (GN p a b)).trans
      (Nat.log_mono_right
        (GN_le_mul_interval_add_pow hb
          (Finset.mem_Icc.mp ha).2))
  rw [sum_nat_pred_eq_sum_card_ge_two
    (Finset.Icc 0 X) V K hV]
  calc
    ∑ k ∈ Finset.Icc 2 K,
        ((Finset.Icc 0 X).filter
          (fun a => k ≤ V a)).card ≤
        ∑ k ∈ Finset.Icc 2 K,
          (p - 1) * ((X + 1) / q ^ k + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k :=
        (by omega : 0 < 2).trans_le (Finset.mem_Icc.mp hk).1
      have heq :=
        congrArg Finset.card
          (gn_deep_lift_filter_eq_padic_depth_filter
            (p := p) (q := q) (b := b) (k := k) (X := X)
            hq hGN)
      change
        ((Finset.Icc 0 X).filter
          (fun a => k ≤ padicValNat q (GN p a b))).card ≤
            (p - 1) * ((X + 1) / q ^ k + 1)
      rw [← heq]
      exact card_gn_deep_lift_residue_classes_le_of_simpleRoot
        hp hq hqp hqb hkpos
    _ = (p - 1) *
        ∑ k ∈ Finset.Icc 2 K,
          ((X + 1) / q ^ k + 1) := by
      rw [Finset.mul_sum]

/--
Explicit `q`-sensitive average valuation-excess bound.

The density contribution has denominator `q * (q-1)`; the second term is the
number of possible boundary-address layers.
-/
theorem sum_padicValNat_pred_GN_le_of_simpleRoot
    {p q b X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        (padicValNat q (GN p a b) - 1) ≤
      (p - 1) *
        ((X + 1) / (q * (q - 1)) +
          (Nat.log q (p * (X + b) ^ p) - 1)) := by
  let K := Nat.log q (p * (X + b) ^ p)
  calc
    ∑ a ∈ Finset.Icc 0 X,
        (padicValNat q (GN p a b) - 1) ≤
        (p - 1) *
          ∑ k ∈ Finset.Icc 2 K,
            ((X + 1) / q ^ k + 1) :=
      sum_padicValNat_pred_GN_le_of_simpleRoot_layers
        hp hq hqp hqb
    _ = (p - 1) *
        ((∑ k ∈ Finset.Icc 2 K, (X + 1) / q ^ k) +
          (Finset.Icc 2 K).card) := by
      congr 1
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ (p - 1) *
        ((X + 1) / (q * (q - 1)) + (K - 1)) := by
      apply Nat.mul_le_mul_left
      have hdiv :=
        sum_div_prime_pow_Icc_two_le
          (q := q) (N := X + 1) (K := K) hq
      have hcard : (Finset.Icc 2 K).card = K - 1 := by
        rw [Nat.card_Icc]
        omega
      rw [hcard]
      omega

/-- Log-weighted form of the fixed-prime average excess bound. -/
theorem sum_padicValNat_pred_GN_mul_log_le_of_simpleRoot
    {p q b X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        ((padicValNat q (GN p a b) - 1 : ℕ) : ℝ) *
          Real.log (q : ℝ) ≤
      (((p - 1) *
        ((X + 1) / (q * (q - 1)) +
          (Nat.log q (p * (X + b) ^ p) - 1)) : ℕ) : ℝ) *
            Real.log (q : ℝ) := by
  have hsum :=
    sum_padicValNat_pred_GN_le_of_simpleRoot
      (X := X) hp hq hqp hqb
  have hsumR :
      (∑ a ∈ Finset.Icc 0 X,
        ((padicValNat q (GN p a b) - 1 : ℕ) : ℝ)) ≤
      (((p - 1) *
        ((X + 1) / (q * (q - 1)) +
          (Nat.log q (p * (X + b) ^ p) - 1)) : ℕ) : ℝ) := by
    exact_mod_cast hsum
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hsumR
    (Real.log_nonneg (by exact_mod_cast hq.one_le))

/-- Log-weighted valuation excess over a chosen finite prime family. -/
noncomputable def GNExcessMassAt
    (Q : Finset ℕ) (p b a : ℕ) : ℝ :=
  ∑ q ∈ Q,
    ((padicValNat q (GN p a b) - 1 : ℕ) : ℝ) *
      Real.log (q : ℝ)

/--
Finite-family average GN excess with `q`-sensitive density terms.
-/
theorem sum_GNExcessMassAt_over_interval_le
    {p b X : ℕ}
    (Q : Finset ℕ)
    (hp : Nat.Prime p)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X, GNExcessMassAt Q p b a ≤
      ∑ q ∈ Q,
        ((((p - 1) *
          ((X + 1) / (q * (q - 1)) +
            (Nat.log q (p * (X + b) ^ p) - 1)) : ℕ) : ℝ) *
              Real.log (q : ℝ)) := by
  unfold GNExcessMassAt
  calc
    ∑ a ∈ Finset.Icc 0 X,
        ∑ q ∈ Q,
          ((padicValNat q (GN p a b) - 1 : ℕ) : ℝ) *
            Real.log (q : ℝ) =
        ∑ q ∈ Q,
          ∑ a ∈ Finset.Icc 0 X,
            ((padicValNat q (GN p a b) - 1 : ℕ) : ℝ) *
              Real.log (q : ℝ) := Finset.sum_comm
    _ ≤ ∑ q ∈ Q,
        ((((p - 1) *
          ((X + 1) / (q * (q - 1)) +
            (Nat.log q (p * (X + b) ^ p) - 1)) : ℕ) : ℝ) *
              Real.log (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact sum_padicValNat_pred_GN_mul_log_le_of_simpleRoot
        hp (hQprime q hq) (hQp q hq) (hQb q hq)

/--
All non-exceptional GN primes occurring in `[0,X]` and avoiding the fixed
boundary coordinate `b`.
-/
noncomputable def GNNonExceptionalIntervalPrimeFamily
    (p b X : ℕ) : Finset ℕ :=
  (Finset.Icc 0 X).biUnion
    (fun a =>
      (GNNonExceptionalSupport p a b).filter
        (fun q => ¬ q ∣ b))

theorem mem_GNNonExceptionalIntervalPrimeFamily_iff
    {p b X q : ℕ} :
    q ∈ GNNonExceptionalIntervalPrimeFamily p b X ↔
      ∃ a ∈ Finset.Icc 0 X,
        q ∈ GNNonExceptionalSupport p a b ∧ ¬ q ∣ b := by
  classical
  simp [GNNonExceptionalIntervalPrimeFamily]

theorem GNNonExceptionalIntervalPrimeFamily_prime
    {p b X q : ℕ}
    (hq : q ∈ GNNonExceptionalIntervalPrimeFamily p b X) :
    Nat.Prime q := by
  rcases mem_GNNonExceptionalIntervalPrimeFamily_iff.mp hq with
    ⟨a, ha, hqsupport, hqb⟩
  exact (mem_support_factorization_iff.mp
    (Finset.mem_filter.mp hqsupport).1).2.1

theorem GNNonExceptionalIntervalPrimeFamily_not_dvd_exponent
    {p b X q : ℕ}
    (hq : q ∈ GNNonExceptionalIntervalPrimeFamily p b X) :
    ¬ q ∣ p := by
  rcases mem_GNNonExceptionalIntervalPrimeFamily_iff.mp hq with
    ⟨a, ha, hqsupport, hqb⟩
  exact (Finset.mem_filter.mp hqsupport).2

theorem GNNonExceptionalIntervalPrimeFamily_not_dvd_boundary
    {p b X q : ℕ}
    (hq : q ∈ GNNonExceptionalIntervalPrimeFamily p b X) :
    ¬ q ∣ b := by
  rcases mem_GNNonExceptionalIntervalPrimeFamily_iff.mp hq with
    ⟨a, ha, hqsupport, hqb⟩
  exact hqb

/--
Canonical interval-wide average excess bound over every non-exceptional prime
away from the fixed boundary coordinate.
-/
theorem sum_GNNonExceptionalIntervalExcessMass_le
    {p b X : ℕ}
    (hp : Nat.Prime p) :
    ∑ a ∈ Finset.Icc 0 X,
        GNExcessMassAt
          (GNNonExceptionalIntervalPrimeFamily p b X) p b a ≤
      ∑ q ∈ GNNonExceptionalIntervalPrimeFamily p b X,
        ((((p - 1) *
          ((X + 1) / (q * (q - 1)) +
            (Nat.log q (p * (X + b) ^ p) - 1)) : ℕ) : ℝ) *
              Real.log (q : ℝ)) := by
  exact sum_GNExcessMassAt_over_interval_le
    (GNNonExceptionalIntervalPrimeFamily p b X) hp
    (fun q hq =>
      GNNonExceptionalIntervalPrimeFamily_prime hq)
    (fun q hq =>
      GNNonExceptionalIntervalPrimeFamily_not_dvd_exponent hq)
    (fun q hq =>
      GNNonExceptionalIntervalPrimeFamily_not_dvd_boundary hq)

end DkMath.ABC
