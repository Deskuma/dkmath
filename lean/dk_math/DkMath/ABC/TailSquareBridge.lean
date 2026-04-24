/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.HeavyPrimeCounting
import DkMath.ABC.QualityTailBridge
import DkMath.ABC.SquareTailBasic

#print "file: DkMath.ABC.TailSquareBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-- TailBound γ for triple (a,b,c): twoTail c ≤ (rad (a * b)) ^ γ (in ℝ). -/
def TailBound (γ : ℝ) (a b c : ℕ) : Prop :=
  (twoTail c : ℝ) ≤ (rad (a * b) : ℝ) ^ γ

/-- Maximal square divisor (square part) of `n`. -/
def sqPart (n : ℕ) : ℕ :=
  n.factorization.support.prod fun p => p ^ (2 * (n.factorization p / 2))

lemma sqPart_eq_evenPart_pow2 (n : ℕ) : sqPart n = (evenPart n) ^ 2 := by
  dsimp [sqPart, evenPart]
  conv_lhs => arg 2; ext p; rw [two_mul]
  simp only [pow_add]
  rw [Finset.prod_mul_distrib]
  ring

lemma oddPart_le_rad (n : ℕ) : (oddPart n : ℝ) ≤ (rad n : ℝ) := by
  dsimp [oddPart, rad]
  let S := n.factorization.support
  have pointwise_nat : ∀ p ∈ S, p ^ (n.factorization p % 2) ≤ p := by
    intro p hp
    rcases mem_support_factorization_iff.mp hp with ⟨_, ⟨hprime, _⟩⟩
    let v := n.factorization p
    by_cases hv0 : v % 2 = 0
    · rw [hv0]
      simp only [pow_zero, ge_iff_le]
      exact Nat.one_le_of_lt (Nat.Prime.one_lt hprime)
    · have vlt2 := Nat.mod_lt v (by norm_num : (0 : ℕ) < 2)
      have vpos : 0 < v % 2 := Nat.pos_of_ne_zero hv0
      have one_le : 1 ≤ v % 2 := Nat.succ_le_of_lt vpos
      have le1 : v % 2 ≤ 1 := Nat.le_of_lt_succ vlt2
      have req : v % 2 = 1 := Nat.le_antisymm le1 one_le
      rw [req]
      simp
  have prod_le_nat :
      Finset.prod S (fun p => p ^ (n.factorization p % 2)) ≤ Finset.prod S fun p => p :=
    Finset.prod_le_prod' fun p hp => pointwise_nat p hp
  exact_mod_cast prod_le_nat

lemma sqTail_le_sqPart (n : ℕ) : (sqTail n : ℝ) ≤ (sqPart n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn, sqTail, sqPart]
  have h_mul : (sqTail n : ℝ) * (rad n : ℝ) = (oddPart n : ℝ) * (evenPart n : ℝ) ^ 2 := by
    calc
      (sqTail n : ℝ) * (rad n : ℝ) = (n : ℝ) := by rw [nat_eq_sqTail_mul_rad_real n hn]
      _ = (oddPart n : ℝ) * (evenPart n : ℝ) ^ 2 := by rw [decomp_oddPart_evenPart_real n hn]
  have h_odd_le_rad := oddPart_le_rad n
  have h_even_sq_nonneg : 0 ≤ (evenPart n : ℝ) ^ 2 := by
    apply pow_two_nonneg
  have h_mul_bound :
      (oddPart n : ℝ) * (evenPart n : ℝ) ^ 2 ≤ (rad n : ℝ) * (evenPart n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h_odd_le_rad h_even_sq_nonneg
  have h_le := by rwa [← h_mul] at h_mul_bound
  have heq_real : (evenPart n : ℝ) ^ 2 = (sqPart n : ℝ) := by
    have hnat := sqPart_eq_evenPart_pow2 n
    exact_mod_cast hnat.symm
  rw [mul_comm (rad n : ℝ) ((evenPart n : ℝ) ^ 2)] at h_le
  rw [heq_real] at h_le
  exact le_of_mul_le_mul_right h_le
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_rad_real n))

/-- Unconditional decomposition bound using sqPart: c ≤ rad(c) * sqPart(c). -/
lemma c_le_sqPart_mul_rad (n : ℕ) : (n : ℝ) ≤ (rad n : ℝ) * (sqPart n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have h := nat_eq_sqTail_mul_rad_real n hn
  rw [h]
  rw [mul_comm (rad n : ℝ) (sqPart n : ℝ)]
  apply mul_le_mul_of_nonneg_right (sqTail_le_sqPart n)
  norm_cast
  exact Nat.cast_nonneg (rad n)

/-- Generalized analytic bridge: assumes piSqRad and TailBound and concludes quality bound. -/
lemma quality_le_of_pi_tail_general
  {a b c : ℕ} {ε δ γ : ℝ}
  (hε_pos : 0 < ε) (hsum : a + b = c) (hcop : Nat.Coprime a b)
  (hπ : (piSqRad c : ℝ) ≤ (rad (a * b) : ℝ) ^ δ)
  (htail : TailBound γ a b c)
  (hδγ_nonneg : 0 ≤ δ + γ) (hδγ : δ + γ ≤ ε) :
  quality (Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  by_cases hc : c = 0
  · have hqual_zero : quality (Triple.mk a b c hsum hcop) = 0 := by
      simp [quality, hc]
    have : (0 : ℝ) ≤ 1 + ε := by linarith
    simpa [hqual_zero] using this
  have hc_ne : c ≠ 0 := hc
  have hdec := decomp_piRad_twoTail_real c hc_ne
  have h_two_le := htail
  have h_pos_left : 0 ≤ (piSqRad c : ℝ) * (rad c : ℝ) := by
    have h1 : (1 : ℝ) ≤ (piSqRad c : ℝ) := by
      exact_mod_cast (piSqRad_ge_one c)
    have h2 : 0 < (rad c : ℝ) := rad_pos_real c
    exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) h1) (le_of_lt h2)
  have hmul := mul_le_mul_of_nonneg_left h_two_le h_pos_left
  have htail' : (c : ℝ) ≤ (piSqRad c : ℝ) * (rad (a * b) : ℝ) ^ γ * (rad c : ℝ) := by
    rw [hdec.symm] at hmul
    have :
        (piSqRad c : ℝ) * (rad c : ℝ) * (rad (a * b) : ℝ) ^ γ =
          (piSqRad c : ℝ) * (rad (a * b) : ℝ) ^ γ * (rad c : ℝ) := by
      ring
    rw [this] at hmul
    exact hmul
  exact quality_le_of_pi_tail δ γ ε hε_pos hcop hsum hπ htail' hδγ_nonneg hδγ

lemma log_twoTail_le_excess_sum (c : ℕ) (hc : c ≠ 0) :
  Real.log (twoTail c : ℝ)
    ≤ ∑ p ∈ c.factorization.support, (((c.factorization p - 2) : ℕ) : ℝ) * Real.log (p : ℝ) := by
  have h_eq := ABC.log_twoTail_eq_sum_vplus c hc
  have h_support : c.primeFactors = c.factorization.support := by
    ext p
    simp [Nat.support_factorization, Nat.mem_primeFactors, ne_eq]
  exact ge_of_eq (id (Eq.symm h_eq))

end DkMath.ABC
