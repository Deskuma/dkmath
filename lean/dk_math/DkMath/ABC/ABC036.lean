/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC035

#print "file: DkMath.ABC.ABC036"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

namespace Chernoff

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- ==========================================
-- Bad Set Definitions
-- ==========================================

def Bad_ε (n : ℕ) (γ_values : ℕ → ℝ) : Prop :=
  ∃ p ≥ 3, p.Prime ∧ Excess p (γ_values p) n

-- Auxiliary lemma: Bad_ε characterization via existential
lemma bad_iff_exists_excess (n : ℕ) (γ_values : ℕ → ℝ) :
    Bad_ε n γ_values ↔ ∃ p ≥ 3, p.Prime ∧ Excess p (γ_values p) n :=
  Iff.rfl

-- Density bound (proven version - replaces not_bad_of_union_bound)
-- Auxiliary lemma: exp(1) > 1 (e ≈ 2.718...)
lemma exp_one_gt_one : 1 < Real.exp 1 := by
  norm_num [Real.exp_one_lt_d9]

-- Decidability instance for Bad_ε (classical logic needed)
noncomputable instance decidable_Bad_ε (γ_values : ℕ → ℝ) : DecidablePred fun n => Bad_ε n γ_values :=
  fun n => Classical.dec (Bad_ε n γ_values)


lemma p_lt_X_to_p_lt_X_succ (p X : ℕ) : p ≤ X → p < X + 1 := by
  intro hp
  linarith



-- Parameterized bad-set density: assume an upper bound Λ for the prime-sum over `primesUpTo X`.
lemma bad_set_density_bound_param
  (γ_values : ℕ → ℝ) (hγ_values : ∀ p, 0 < γ_values p)
  (Λ : ℝ) (hΛ_nonneg : 0 ≤ Λ)
  (HΛ : ∀ X, X ≥ const_X → ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(Real.log 2 / Real.log 3) * (γ_values p + 2)) ≤ Λ) :
  ∃ C > 0, ∀ X ≥ const_X,
    ((Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ)
      ≤ C * (X : ℝ) := by
  classical
  let C := const_C * (Λ + 1)
  have hCpos : 0 < (C : ℝ) := by
    have h1 : (0 : ℝ) < (const_C : ℝ) := by norm_num [const_C]
    have h2 : 0 < Λ + 1 := by linarith [hΛ_nonneg]
    exact mul_pos h1 h2
  use C
  refine ⟨hCpos, ?_⟩
  intro X hX
  -- (A) Cover Bad set by biUnion over primesUpTo X
  have h_sub :
    (Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X))
      ⊆ Finset.biUnion (primesUpTo X) fun p => Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and, Finset.mem_biUnion,
      and_self_left] at hn ⊢
    rcases hn with ⟨hnIcc, hbad⟩
    unfold Bad_ε at hbad
    rcases hbad with ⟨p, hpge3, hpPrime, hExcess⟩
    -- Excess gives v_p(2n+1) - 2 > γ > 0, so v_p(2n+1) ≠ 0 hence ≥ 1
    have hv_ne0 : padicValNat p (2 * n + 1) ≠ 0 := by
      intro h0
      have h_eq : (((padicValNat p (2 * n + 1) : ℤ) : ℝ) - 2) = -2 := by simp [h0]
      -- Expand the definition of Excess before rewriting so the inequality is available
      unfold Excess at hExcess
      have h_lt : -2 > γ_values p := by
        rw [h_eq] at hExcess
        exact hExcess
      have h_pos : 0 < γ_values p := hγ_values p
      linarith [h_lt, h_pos]
    have hv_pos : 0 < padicValNat p (2 * n + 1) := by
      exact Nat.pos_iff_ne_zero.mpr hv_ne0
    have hv_ge1 : 1 ≤ padicValNat p (2 * n + 1) := by linarith [Nat.succ_le_iff.mpr hv_pos]
    have hp_dvd : p ∣ 2 * n + 1 := by
      -- use dvd_of_one_le_padicValNat from padic theory
      exact dvd_of_one_le_padicValNat (p := p) hv_ge1
    -- p ∈ primesUpTo X because p ∣ 2n+1 and n ≤ X
    have hp_mem := prime_mem_primesUpTo_of_dvd_odd hnIcc hpPrime hpge3 hp_dvd
    exact ⟨p, ⟨hp_mem, ⟨hnIcc, hExcess⟩⟩⟩

  -- (B) card ≤ sum over primesUpTo X
  have h_card_le :
    ((Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ)
      ≤ ∑ p ∈ primesUpTo X, ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ) := by
    calc ((Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ)
        ≤ (Finset.biUnion (primesUpTo X) fun p => Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card := by
          exact_mod_cast Finset.card_le_card h_sub
    _ ≤ ∑ p ∈ primesUpTo X, ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le

  -- (C) apply single-prime bound for each p and sum
  let α := Real.log 2 / Real.log 3
  have hαpos : 0 < α := by
    have : 1 < (3 : ℝ) := by norm_num
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos this)
  have h_each : ∀ p ∈ primesUpTo X,
    ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
      ≤ const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2)) := by
    intro p hp
    -- hp : p ∈ primesUpTo X, i.e., p ∈ Finset.filter (fun p => p.Prime ∧ p ≥ 3) (Finset.range (2 * X + 2))
    -- hp : p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (2 * X + 2))
    -- 分解には Finset.mem_filter.mp を使い、range の不等式は Finset.mem_range.mp で取り出す
    have ⟨hp_in_range_mem, ⟨hpPrime_prop, hp3_prop⟩⟩ := Finset.mem_filter.mp hp
    have hp_in_range : p < 2 * X + 2 := Finset.mem_range.mp hp_in_range_mem
    have hpPrime : p.Prime := hpPrime_prop
    have hp3 : 3 ≤ p := hp3_prop
    haveI : Fact p.Prime := ⟨hpPrime⟩
    exact chernoff_single_prime_uniform_rpow hp3 (γ_values p) (hγ_values p) α hαpos (le_of_eq rfl) X hX
  have h_sum_le := Finset.sum_le_sum h_each
  -- (D) bound prime-sum by Λ and finish
  have h_primes_bound := HΛ X hX
  calc ((Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ)
      ≤ ∑ p ∈ primesUpTo X, ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ) := h_card_le
    _ ≤ ∑ p ∈ primesUpTo X, (const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2))) := by
      exact_mod_cast h_sum_le
    _ = const_C * (X : ℝ) * ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-α * (γ_values p + 2)) := by
      rw [Finset.mul_sum]
    _ ≤ const_C * (X : ℝ) * Λ := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast h_primes_bound
      · -- prove nonnegativity of const_C * X explicitly
        have hCpos_local : 0 < (const_C : ℝ) := by norm_num [const_C]
        have hX_nonneg : 0 ≤ (X : ℝ) := by exact_mod_cast Nat.zero_le X
        have h_nonneg_CX : 0 ≤ (const_C : ℝ) * (X : ℝ) := mul_nonneg (le_of_lt hCpos_local) hX_nonneg
        exact h_nonneg_CX
    _ ≤ (const_C * (Λ + 1)) * (X : ℝ) := by
      -- show Λ ≤ Λ + 1 using the nonnegativity hypothesis on Λ
      have hΛ_add : Λ ≤ Λ + 1 := by linarith [hΛ_nonneg]
      -- rewrite the RHS as (const_C * X) * (Λ + 1) so we can apply mul_le_mul_of_nonneg_left
      have : (const_C : ℝ) * (Λ + 1) * (X : ℝ) = (const_C : ℝ) * (X : ℝ) * (Λ + 1) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_left hΛ_add
      -- prove nonnegativity of const_C * X explicitly as above
      have hCpos_local2 : 0 < (const_C : ℝ) := by norm_num [const_C]
      have hX_nonneg2 : 0 ≤ (X : ℝ) := by exact_mod_cast Nat.zero_le X
      exact mul_nonneg (le_of_lt hCpos_local2) hX_nonneg2



-- Density version (実用的かつ証明可能)
/--
`bad_set_density_bound` は、与えられた実数 ε > 0、関数 γ_values : ℕ → ℝ（各素数 p に対して γ_values p > 0）、
および特定の級数評価条件のもとで、集合 `{ n ∈ [0, X] | Bad_ε n γ_values }` の濃度が X に対して C * X で上から抑えられることを示す補題です。

この補題は、Bad_ε n γ_values という性質を満たす整数 n の個数が、X が十分大きいときに線形な上界を持つことを保証します。
ここで、級数条件は、p が 3 以上の素数に対して、`∑ p ((p : ℕ) : ℝ) ^ (-(log 2 / (2 * log 3)) * (γ_values p + 2)) ≤ 1` という形で与えられています。

この結果は、数論的な集合の密度評価や、特定の条件を満たす整数の分布に関する研究に有用です。
-/
lemma bad_set_density_bound'
    (ε : ℝ) (_hε : 0 < ε)
    (γ_values : ℕ → ℝ) (hγ_values : ∀ p, 0 < γ_values p)
    (hseries : ∀ N, ∑ p ∈ primesUpTo N, ((p : ℕ) : ℝ) ^ (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p + 2)) ≤ 1) :
    ∃ C > 0, ∀ (X : ℕ), X ≥ const_X → ((Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ)
    ≤ C * (X : ℝ) := by
  -- Delegate to the parameterized version using Λ = 1
  haveI := decidable_Bad_ε γ_values
  let Λ := (1 : ℝ)
  have hΛ_nonneg : 0 ≤ Λ := by norm_num
  -- HΛ: for X ≥ const_X, sum over primesUpTo X ≤ 1 follows from hseries
  have HΛ : ∀ X, X ≥ const_X → ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(Real.log 2 / Real.log 3) * (γ_values p + 2)) ≤ Λ := by
    intro X hX
    -- hseries holds for any N, in particular for X
    have hN := hseries X
    -- 型不一致を指数部の大小関係で補正する
    have h_pow_le : ∀ p ∈ primesUpTo X,
      (p : ℝ) ^ (-(Real.log 2 / Real.log 3) * (γ_values p + 2))
      ≤ (p : ℝ) ^ (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p + 2)) := by
      intro p hp
      -- Extract properties from membership in primesUpTo X
      have hp_pos : 0 < (p : ℝ) := by
        have hp : Nat.Prime p := by
          let hf := Finset.mem_filter.1 hp
          rcases hf with ⟨_, ⟨hpPrime, _⟩⟩
          exact hpPrime
        exact_mod_cast hp.pos
      -- primesUpTo X の定義より p ≥ 3 なので (p : ℝ) ≥ 3 > 1
      have base_ge_one : 1 ≤ (p : ℝ) := by
        have hp_ge3 : 3 ≤ p := by
          -- primesUpTo X の定義より
          let ⟨_, ⟨_, hp3⟩⟩ := Finset.mem_filter.mp hp
          exact hp3
        norm_cast
        linarith [hp_ge3]
      let s := γ_values p + 2
      have s_pos : 0 < s := by linarith [hγ_values p]
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
      have hpos : 0 < Real.log 2 / (2 * Real.log 3) := by exact div_pos hlog2_pos (mul_pos (by norm_num : (2 : ℝ) > 0) hlog3_pos)
      have diff_eq : (-(Real.log 2 / (2 * Real.log 3)) * s) - (-(Real.log 2 / Real.log 3) * s) = (Real.log 2 / (2 * Real.log 3)) * s := by ring_nf
      have pos_nonneg : 0 ≤ (Real.log 2 / (2 * Real.log 3)) * s := by
        apply mul_nonneg (le_of_lt hpos) (le_of_lt s_pos)
      have exp_le : (-(Real.log 2 / Real.log 3) * s) ≤ (-(Real.log 2 / (2 * Real.log 3)) * s) := by
        linarith [diff_eq, pos_nonneg]
      exact Real.rpow_le_rpow_of_exponent_le base_ge_one exp_le
    have h_sum_le := Finset.sum_le_sum h_pow_le
    exact le_trans h_sum_le hN
  -- now call param version
  exact bad_set_density_bound_param γ_values hγ_values Λ hΛ_nonneg HΛ

end Chernoff

end ABC
