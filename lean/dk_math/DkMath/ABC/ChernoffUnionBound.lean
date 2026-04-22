/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ChernoffSinglePrime

#print "file: DkMath.ABC.ChernoffUnionBound"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.ABC

namespace Chernoff

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- ==========================================
-- Layer D: Explicit Specialization
-- ==========================================
--
-- Just a one-line call to Uniform with t = log2/(2·log3)
open Classical in
lemma chernoff_single_prime_explicit'
    {p : ℕ} [Fact p.Prime] (hp3 : pge3 p)
    (γ : ℝ) (hγ : 0 < γ) :
    let t0 := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), C = const_C ∧ 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
          ≤ C * (X : ℝ) * Real.exp (- t0 * γ * Real.log (p : ℝ)) := by
  intro t0
  have ht0_pos : 0 < t0 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have : 0 < 2 * Real.log 3 := by linarith
    exact div_pos hlog2 this
  have ht0_le : t0 ≤ Real.log 2 / Real.log 3 := by
    dsimp [t0]
    exact t_bound_log2_div_log3
  obtain ⟨C0, rfl, hC0_pos, hbound0⟩ :=
    chernoff_single_prime_uniform hp3 γ hγ t0 ht0_pos ht0_le
  exact chernoff_single_prime_uniform hp3 γ hγ t0 ht0_pos ht0_le

open Classical in
lemma chernoff_single_prime_explicit
    {p : ℕ} [Fact p.Prime] (hp3 : pge3 p)
    (γ : ℝ) (hγ : 0 < γ) :
    let t0 := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), C = const_C ∧ 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
          ≤ C * (X : ℝ) * Real.exp (- t0 * γ * Real.log (p : ℝ)) := by
  intro t0
  have ht0_pos : 0 < t0 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have : 0 < 2 * Real.log 3 := by
      have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
      nlinarith
    exact div_pos hlog2 this
  have ht0_le : t0 ≤ Real.log 2 / Real.log 3 := by
    dsimp [t0]
    exact t_bound_log2_div_log3
  obtain ⟨C, hC, hCpos, hU⟩ :=
    chernoff_single_prime_uniform hp3 γ hγ t0 ht0_pos ht0_le
  refine ⟨C, hC, hCpos, ?_⟩
  intro X hX
  simpa using hU X hX

-- ==========================================
-- Layer E: Union Bound
-- ==========================================

open Classical in
lemma union_bound_chernoff
    (γ_values : ℕ → ℝ) (hγ_values : ∀ p, 0 < γ_values p) :
    let t0 := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        (∑ p ∈ primesUpTo X,
           ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ C * (X : ℝ) * ∑ p ∈ primesUpTo X,
             Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ))) := by
  intro t0
  use const_C
  constructor
  · rw [const_C]
    norm_num
  · intro X hX
    calc
      (∑ p ∈ primesUpTo X,
          ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ))
        ≤ ∑ p ∈ primesUpTo X,
            5 * (X : ℝ) * Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ)) := by
              apply Finset.sum_le_sum
              intro p hp
              have hf := Finset.mem_filter.1 hp
              rcases hf with ⟨hp_in, hp_prop⟩
              rcases hp_prop with ⟨hpPrime, hp3⟩
              let hpFact : Fact p.Prime := ⟨hpPrime⟩
              obtain ⟨C, rfl, hC_pos, hbound⟩ :=
                @chernoff_single_prime_explicit p hpFact hp3 (γ_values p) (hγ_values p)
              have h := hbound X hX
              calc
                ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
                    ≤ const_C * ↑X * Real.exp
                        (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p) * Real.log ↑p) := h
                _ = const_C * ↑X * Real.exp
                        (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p) * Real.log ↑p) := by
                          rfl
      _ = const_C * (X : ℝ) * ∑ p ∈ primesUpTo X,
            Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ)) := by
              rw [Finset.mul_sum]
              rfl

open Classical in
lemma union_bound_chernoff'
    (γ_values : ℕ → ℝ) (hγ_values : ∀ p, 0 < γ_values p) :
    let t0 := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        (∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
           ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ C * (X : ℝ) * ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
             Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ))) := by
  intro t0
  use const_C
  constructor
  · rw [const_C]
    norm_num
  · intro X hX
    calc
      (∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
          ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ))
        ≤ ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
            5 * (X : ℝ) * Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ)) := by
              apply Finset.sum_le_sum
              intro p hp
              let hf := Finset.mem_filter.1 hp
              rcases hf with ⟨_, ⟨hpPrime, hp3⟩⟩
              let hpFact : Fact p.Prime := ⟨hpPrime⟩
              obtain ⟨C, rfl, hC_pos, hbound⟩ :=
                @chernoff_single_prime_explicit p hpFact hp3 (γ_values p) (hγ_values p)
              have h := hbound X hX
              calc
                ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
                    ≤ const_C * ↑X * Real.exp
                        (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p) * Real.log ↑p) := h
                _ = const_C * ↑X * Real.exp
                        (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p) * Real.log ↑p) := by
                          rfl
      _ = const_C * (X : ℝ) *
            ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
              Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ)) := by
              have :
                  ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
                      5 * (X : ℝ) * Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ))
                    = 5 * (X : ℝ) *
                        ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
                          Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ)) := by
                    rw [Finset.sum_congr rfl (fun p _ => rfl), ← Finset.mul_sum]
              rw [this]
              rfl

open Classical in
/-- Union bound in pow-form: sum over primes ≤ X of `card(Excess)` is
    ≤ const_C · X · (∑ p≤X p^{-t(γ_p+2)}).  We plug `t = α := log 2 / log 3`. -/
lemma union_bound_chernoff_pow
    (γ_values : ℕ → ℝ) (hγ : ∀ p, 0 < γ_values p) :
    let α := Real.log 2 / Real.log 3
    ∃ (C : ℝ), 0 < C ∧
      ∀ X ≥ const_X,
        (∑ p ∈ primesUpTo X,
            ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ))
        ≤ C * (X : ℝ) *
            ∑ p ∈ primesUpTo X,
              (p : ℝ) ^ (- α * (γ_values p + 2)) := by
  intro α
  use const_C
  constructor
  · simp [const_C]
  intro X hX
  have hle : ∀ p ∈ primesUpTo X,
      ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2)) := by
    intro p hp
    let ⟨hp_in, ⟨hpPrime, hp3⟩⟩ := Finset.mem_filter.1 hp
    haveI : Fact p.Prime := ⟨hpPrime⟩
    have hαpos : 0 < α := by
      have : 1 < (3 : ℝ) := by norm_num
      exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos this)
    exact chernoff_single_prime_uniform_rpow hp3 (γ_values p) (hγ p) α hαpos (le_of_eq rfl) X hX
  have := Finset.sum_le_sum hle
  have h_sum' :
    ∑ p ∈ primesUpTo X, const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2))
      = const_C * (X : ℝ) * ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-α * (γ_values p + 2)) := by
        rw [Finset.mul_sum]
  rw [h_sum'] at this
  exact this

open Classical in
lemma union_bound_chernoff_pow'
    (γ_values : ℕ → ℝ) (hγ : ∀ p, 0 < γ_values p) :
    let α := Real.log 2 / Real.log 3
    ∃ (C : ℝ), 0 < C ∧
      ∀ X ≥ const_X,
        (∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
            ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ))
        ≤ C * (X : ℝ) *
            ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
              (p : ℝ) ^ (- α * (γ_values p + 2)) := by
  intro α
  use const_C
  constructor
  · simp [const_C]
  intro X hX
  have hle : ∀ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
      ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have ⟨hp_in, ⟨hpPrime, hp3⟩⟩ := hp
    haveI : Fact p.Prime := ⟨hpPrime⟩
    have hαpos : 0 < α := by
      have : 1 < (3 : ℝ) := by norm_num
      exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos this)
    exact chernoff_single_prime_uniform_rpow hp3 (γ_values p) (hγ p) α hαpos (le_of_eq rfl) X hX
  have := Finset.sum_le_sum hle
  have h_sum :
    ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
      const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2))
      = const_C * (X : ℝ) *
          ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
            (p : ℝ) ^ (-α * (γ_values p + 2)) := by
        rw [Finset.mul_sum]
  rw [h_sum] at this
  exact this

end Chernoff

end DkMath.ABC
