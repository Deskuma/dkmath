/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC036

#print "file: DkMath.ABC.ABC037"

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
-- Quality Inequality
-- ==========================================

-- Construct Λ for the γ_values used in `abc_quality_final`.
lemma construct_HΛ_for_quality (ε : ℝ) (hε : 0 < ε) :
  let γ_values : ℕ → ℝ := fun p => if p ≤ 2 then 1 else ε / (4 * Real.log p)
  let α := Real.log 2 / Real.log 3
  ∃ (Λ : ℝ), 0 < Λ ∧ ∀ X, X ≥ const_X →
    ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(α * (γ_values p + 2))) ≤ Λ := by
  -- Unfold definitions
  let γ_values := fun p => if p ≤ 2 then 1 else ε / (4 * Real.log p)
  let α := Real.log 2 / Real.log 3

  have hαpos : 0 < α := by
    have : 1 < (3 : ℝ) := by norm_num
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos this)

  -- show 2*α > 1 so p^{-2α} is summable over naturals ≥ 2
  have h2α_gt1 : 1 < 2 * α := by
    -- 1 < 2 * α  ⇔  Real.log 3 < 2 * Real.log 2  ⇔  3 < 4, which is true
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      -- まず 4 = 2 ^ 2 と書き換えてから Real.log_pow を適用する
      have : Real.log 4 = Real.log (2 ^ 2) := by norm_num
      rw [this]
      rw [Real.log_pow]
      norm_num

    have hlt : Real.log 3 < 2 * Real.log 2 := by
      rw [← hlog4]
      apply Real.log_lt_log
      · norm_num
      · norm_num

    -- Now, 2 * α = 2 * (Real.log 2 / Real.log 3) = (2 * Real.log 2) / Real.log 3
    -- So 1 < (2 * Real.log 2) / Real.log 3  ⇔  Real.log 3 < 2 * Real.log 2
    have : 1 < 2 * α := by
      -- 2 * α = 2 * (Real.log 2 / Real.log 3) = (2 * Real.log 2) / Real.log 3
      -- So 1 < (2 * Real.log 2) / Real.log 3  ⇔  Real.log 3 < 2 * Real.log 2
      have : 2 * α = (2 * Real.log 2) / Real.log 3 := by
        rw [mul_div_assoc]
      rw [this]
      -- 1 < (2 * Real.log 2) / Real.log 3  ⇔  Real.log 3 < 2 * Real.log 2
      rw [one_lt_div]
      · exact hlt
      · linarith
    exact this

  -- Summability: ∑_{n≥2} n^{-2α} converges
  have hsumm : Summable fun n : ℕ => (n : ℝ) ^ (-(2 * α)) := by
    -- (n : ℝ) ^ (-(2 * α)) = ((n : ℝ) ^ (2 * α))⁻¹ と書き換えてから適用
    apply Real.summable_nat_rpow.mpr
    -- 2 * α > 1 なら -(2 * α) < -1
    linarith [h2α_gt1]

  -- define S = tsum of n^{-2α} over n ≥ 2 (we'll use full tsum over ℕ but zero/1 are finite)
  let S := ∑' (n : ℕ), (n : ℝ) ^ (-(2 * α))
  have hSpos : 0 < S := by
    -- All terms are nonnegative and the n = 2 term is strictly positive, so the tsum is ≥ that term > 0.
    have hnonneg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-(2 * α)) := by
      intro n
      apply Real.rpow_nonneg
      norm_cast
      exact Nat.zero_le n
    have hpos_term : 0 < (2 : ℝ) ^ (-(2 * α)) := by
      apply Real.rpow_pos_of_pos; norm_num
    -- Use Summable.le_tsum to get the finite term ≤ tsum
    have hterm_le_tsum : (2 : ℝ) ^ (-(2 * α)) ≤ ∑' (n : ℕ), (n : ℝ) ^ (-(2 * α)) := by
      -- rewrite ↑2 as 2 : ℕ then apply le_tsum
      have : (2 : ℝ) = ↑(2 : ℕ) := rfl
      rw [this]
      exact Summable.le_tsum hsumm 2 (fun j hj => hnonneg j)
    linarith

  -- Now we can conclude 0 < S
  -- constant factor from γ_values: for p ≥ 3, p^{-α*γ_p} = exp(-α*ε/4)
  let c := Real.exp (-(α * ε / 4))
  have hcpos : 0 < c := by apply Real.exp_pos
  -- define Λ := c * S
  let Λ := c * S
  have hΛpos : 0 < Λ := mul_pos hcpos hSpos
  use Λ
  refine ⟨hΛpos, ?_⟩
  intro X hX
  -- For p ∈ primesUpTo X we have p ≥ 3 and γ_values p = ε / (4 * log p)
  have h_subset_range : (primesUpTo X : Finset ℕ) ⊆ Finset.Icc 3 (2 * X + 1) := by
    intro p hp
    simp only [primesUpTo, ge_iff_le, Finset.mem_filter, Finset.mem_range] at hp
    -- hp : p ∈ primesUpTo X, i.e., p ∈ Finset.filter (fun p => p.Prime ∧ p ≥ 3) (Finset.range (2 * X + 2))
    -- 分解には Finset.mem_filter.1 を使う
    have h_range : p < 2 * X + 2 := hp.left
    have h_prime : Nat.Prime p := hp.right.left
    have h_ge3 : 3 ≤ p := hp.right.right
    -- membership in range ensures p < 2*X+2 ⇒ p ≤ 2*X+1, and p ≥3 from filter
    have hlt := Finset.mem_range.mpr h_range
    have hle : p ≤ 2 * X + 1 := Nat.le_pred_of_lt h_range
    exact Finset.mem_Icc.2 ⟨by linarith [h_ge3], hle⟩

  -- For p in primesUpTo X, p^{-α*(γ_p+2)} = c * p^{-2α}
  have hterm_eq : ∀ p ∈ primesUpTo X,
    (p : ℝ) ^ (-(α * (γ_values p + 2))) = c * (p : ℝ) ^ (-(2 * α)) := by
    intro p hp
    -- extract p ≥ 3 so γ_values p = ε / (4 * Real.log p)
    have hp_filter := Finset.mem_filter.1 hp
    have hpPrime : p.Prime := hp_filter.2.1
    have hp3 : p ≥ 3 := hp_filter.2.2
    have hγdef : γ_values p = ε / (4 * Real.log (p : ℝ)) := by
      -- γ_values p = if p ≤ 2 then 1 else ε / (4 * Real.log p)  (p ≥ 3 より p > 2)
      dsimp [γ_values]
      rw [if_neg]
      have h_gt : p > 2 := Nat.lt_of_succ_le hp3
      exact not_le_of_gt (by exact_mod_cast h_gt : (p : ℝ) > 2)
    -- Now calculate the term by splitting the exponent and converting the first factor to exp(...)
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast Nat.Prime.pos hpPrime
    calc (p : ℝ) ^ (-(α * (γ_values p + 2)))
        = (p : ℝ) ^ (-(α * (ε / (4 * Real.log (p : ℝ)) + 2))) := by rw [hγdef]
      _ = (p : ℝ) ^ (-(α * ε / (4 * Real.log (p : ℝ)) + 2 * α)) := by ring_nf
      _ = (p : ℝ) ^ (-(α * ε / (4 * Real.log (p : ℝ)))) * (p : ℝ) ^ (-(2 * α)) := by
        -- まず指数部を -(α * ε / (4 * Real.log ↑p) + 2 * α) = (-(α * ε / (4 * Real.log ↑p))) + (-(2 * α)) に整理
        rw [neg_add]
        rw [Real.rpow_add hp_pos (-(α * ε / (4 * Real.log (p : ℝ)))) (-(2 * α))]
      _ = Real.exp (-(α * ε / 4)) * (p : ℝ) ^ (-(2 * α)) := by
        -- 片方の因子を hpow で書き換えてから両辺に掛ける
        have hpow : (p : ℝ) ^ (-(α * ε / (4 * Real.log (p : ℝ)))) = Real.exp (-(α * ε / 4)) := by
          rw [Real.rpow_def_of_pos hp_pos]
          have hlog_ne : Real.log (p : ℝ) ≠ 0 := by
            apply _root_.ne_of_gt
            apply Real.log_pos
            -- p ≥ 3 より (p : ℝ) > 1
            norm_cast
            linarith [hp3]
          -- 順序を揃えてから書き換える
          have : Real.log (p : ℝ) * (-(α * ε / (4 * Real.log (p : ℝ)))) = (-(α * ε / (4 * Real.log (p : ℝ)))) * Real.log (p : ℝ) := by ring_nf
          rw [this]
          have : (-(α * ε / (4 * Real.log (p : ℝ)))) * Real.log (p : ℝ) = -(α * ε / 4) := by
            field_simp [hlog_ne]
          apply congr_arg Real.exp; rw [this]
        rw [hpow]


  -- Now sum up
  -- 素数和の各項を上の形に書き換える
  -- ⊢ ∑ p ∈ primesUpTo X, ↑p ^ (-(Real.log 2 / Real.log 3 * ((fun p ↦ if p ≤ 2 then 1 else ε / (4 * Real.log ↑p)) p + 2))) ≤ Λ

  have h_sum :
    ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(α * (γ_values p + 2)))
      = c * ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(2 * α)) := by
    rw [Finset.sum_congr rfl hterm_eq, Finset.mul_sum]

  -- γ_values の定義を展開して一致させる
  -- primesUpTo X ⊆ Icc 3 (2X+1) so sum over primes ≤ sum over that Icc (nonneg terms)
  have h_nonneg : ∀ n ∈ Finset.Icc 3 (2 * X + 1), n ∉ primesUpTo X → 0 ≤ (n : ℝ) ^ (-(2 * α)) := by
    intros n hn _; apply Real.rpow_nonneg_of_nonneg; norm_cast; linarith
  have h_le_range := Finset.sum_le_sum_of_subset_of_nonneg h_subset_range h_nonneg

  -- Use h_sum to rewrite the sum into the form with c
  have : ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(α * (γ_values p + 2)))
      = c * ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(2 * α)) := by rw [h_sum]
  -- 型を明示的に一致させるため、γ_values, α の定義を展開してから rw で書き換える
  have : ∑ p ∈ primesUpTo X,
      (p : ℝ) ^ (-(Real.log 2 / Real.log 3 * ((fun p ↦ if p ≤ 2 then 1 else ε / (4 * Real.log (p : ℝ))) p + 2)))
    = ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(α * (γ_values p + 2))) := by
    congr 1
  -- ⊢ ∑ p ∈ primesUpTo X, ↑p ^ (-(Real.log 2 / Real.log 3 * ((fun p ↦ if p ≤ 2 then 1 else ε / (4 * Real.log ↑p)) p + 2))) ≤ Λ
  calc ∑ p ∈ primesUpTo X,
      (p : ℝ) ^ (-(Real.log 2 / Real.log 3 * ((fun p : ℕ ↦ if p ≤ 2 then 1 else ε / (4 * Real.log (p : ℝ))) p + 2)))
      = ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(α * (γ_values p + 2))) := by
        congr 1
        -- 両辺の関数定義が一致することを示す
        funext p
        -- γ_values, α の定義を展開して一致させる
        dsimp only [γ_values, α]
        -- if の条件を p ≤ 2 に統一すれば型が一致するので rfl で示せる
        simp only [Nat.cast_le_ofNat]
      _ = c * ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(2 * α)) := by rw [h_sum]
      _ ≤ c * ∑ n ∈ Finset.Icc 3 (2 * X + 1), (n : ℝ) ^ (-(2 * α)) := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast h_le_range
        · linarith
      _ ≤ c * S := by
        -- Finite Icc sum ≤ tsum over ℕ because series is summable and terms nonneg
        have h_fin_le_tsum : ∑ n ∈ Finset.Icc 3 (2 * X + 1), (n : ℝ) ^ (-(2 * α)) ≤ S := by
          -- S = ∑' (n : ℕ), (n : ℝ) ^ (-(2 * α)) と定義しているので、型を合わせて書き換える
          apply Summable.sum_le_tsum
          { intros n hn
            -- n ∈ Icc 3 (2 * X + 1) ⊆ ℕ なので 0 ≤ (n : ℝ) ^ ... が成立
            apply Real.rpow_nonneg_of_nonneg
            norm_cast
            linarith }
          { exact hsumm }
        apply mul_le_mul_of_nonneg_left
        · exact h_fin_le_tsum
        · linarith
      _ = Λ := by rfl





-- Use the Λ constructed for the quality γ_values to produce a density bound
lemma bad_set_density_bound_quality (ε : ℝ) (hε : 0 < ε) :
  ∃ C > 0, ∀ X ≥ const_X,
    ((Finset.filter (fun n => Bad_ε n (fun p => if p ≤ 2 then 1 else ε / (4 * Real.log (p : ℝ)))) (Finset.Icc 0 X)).card : ℝ) ≤ C * (X : ℝ) := by
  let γ_values : ℕ → ℝ := fun n => if n ≤ 2 then 1 else ε / (4 * Real.log (n : ℝ))
  -- prove positivity for g on naturals
  have hg_pos : ∀ n : ℕ, 0 < γ_values n := by
    intro n
    dsimp [γ_values]
    by_cases hn : n ≤ 2
    · -- n ≤ 2 ⇒ g n = 1
      rw [if_pos hn]; norm_num
    · -- n ≥ 3 ⇒ g n = ε/(4*log n) and log n > 0
      rw [if_neg hn]
      have hn_pos : 2 < n := Nat.lt_of_not_le hn
      have hpos : (n : ℝ) > 1 := by norm_cast; linarith [hn_pos]
      have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hpos
      exact div_pos hε (mul_pos (by norm_num : (4 : ℝ) > 0) hlog_pos)

  -- obtain Λ and its bound from construct_HΛ_for_quality
  rcases construct_HΛ_for_quality ε hε with ⟨Λ, hΛpos, hHΛ⟩
  have hΛ_nonneg : 0 ≤ Λ := le_of_lt hΛpos

  -- apply the parameterized density lemma using this Λ and HΛ
  exact bad_set_density_bound_param γ_values hg_pos Λ hΛ_nonneg (fun X hX => by simpa [γ_values] using hHΛ X hX)

end Chernoff

end ABC
