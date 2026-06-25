/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ChernoffDensity

#print "file: DkMath.ABC.ChernoffQualityDensity"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.ABC

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
  let γ_values := fun p => if p ≤ 2 then 1 else ε / (4 * Real.log p)
  let α := Real.log 2 / Real.log 3

  have hαpos : 0 < α := by
    have : 1 < (3 : ℝ) := by norm_num
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos this)

  have h2α_gt1 : 1 < 2 * α := by
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      have : Real.log 4 = Real.log (2 ^ 2) := by norm_num
      rw [this]
      rw [Real.log_pow]
      norm_num
    have hlt : Real.log 3 < 2 * Real.log 2 := by
      rw [← hlog4]
      apply Real.log_lt_log
      · norm_num
      · norm_num
    have : 1 < 2 * α := by
      have : 2 * α = (2 * Real.log 2) / Real.log 3 := by
        rw [mul_div_assoc]
      rw [this]
      rw [one_lt_div]
      · exact hlt
      · linarith
    exact this

  have hsumm : Summable fun n : ℕ => (n : ℝ) ^ (-(2 * α)) := by
    apply Real.summable_nat_rpow.mpr
    linarith [h2α_gt1]

  let S := ∑' (n : ℕ), (n : ℝ) ^ (-(2 * α))
  have hSpos : 0 < S := by
    have hnonneg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-(2 * α)) := by
      intro n
      apply Real.rpow_nonneg
      norm_cast
      exact Nat.zero_le n
    have hpos_term : 0 < (2 : ℝ) ^ (-(2 * α)) := by
      apply Real.rpow_pos_of_pos
      norm_num
    have hterm_le_tsum : (2 : ℝ) ^ (-(2 * α)) ≤ ∑' (n : ℕ), (n : ℝ) ^ (-(2 * α)) := by
      have : (2 : ℝ) = ↑(2 : ℕ) := rfl
      rw [this]
      exact Summable.le_tsum hsumm 2 (fun j hj => hnonneg j)
    linarith

  let c := Real.exp (-(α * ε / 4))
  have hcpos : 0 < c := by apply Real.exp_pos
  let Λ := c * S
  have hΛpos : 0 < Λ := mul_pos hcpos hSpos
  use Λ
  refine ⟨hΛpos, ?_⟩
  intro X hX
  have h_subset_range : (primesUpTo X : Finset ℕ) ⊆ Finset.Icc 3 (2 * X + 1) := by
    intro p hp
    simp only [primesUpTo, ge_iff_le, Finset.mem_filter, Finset.mem_range] at hp
    have h_range : p < 2 * X + 2 := hp.left
    have h_ge3 : 3 ≤ p := hp.right.right
    have hle : p ≤ 2 * X + 1 := Nat.le_pred_of_lt h_range
    exact Finset.mem_Icc.2 ⟨by linarith [h_ge3], hle⟩

  have hterm_eq : ∀ p ∈ primesUpTo X,
    (p : ℝ) ^ (-(α * (γ_values p + 2))) = c * (p : ℝ) ^ (-(2 * α)) := by
    intro p hp
    have hp_filter := Finset.mem_filter.1 hp
    have hpPrime : p.Prime := hp_filter.2.1
    have hp3 : p ≥ 3 := hp_filter.2.2
    have hγdef : γ_values p = ε / (4 * Real.log (p : ℝ)) := by
      dsimp [γ_values]
      rw [if_neg]
      have h_gt : p > 2 := Nat.lt_of_succ_le hp3
      exact not_le_of_gt (by exact_mod_cast h_gt : (p : ℝ) > 2)
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast Nat.Prime.pos hpPrime
    calc
      (p : ℝ) ^ (-(α * (γ_values p + 2)))
          = (p : ℝ) ^ (-(α * (ε / (4 * Real.log (p : ℝ)) + 2))) := by rw [hγdef]
      _ = (p : ℝ) ^ (-(α * ε / (4 * Real.log (p : ℝ)) + 2 * α)) := by ring_nf
      _ = (p : ℝ) ^ (-(α * ε / (4 * Real.log (p : ℝ)))) * (p : ℝ) ^ (-(2 * α)) := by
            rw [neg_add]
            rw [Real.rpow_add hp_pos (-(α * ε / (4 * Real.log (p : ℝ)))) (-(2 * α))]
      _ = Real.exp (-(α * ε / 4)) * (p : ℝ) ^ (-(2 * α)) := by
            have hpow :
                (p : ℝ) ^ (-(α * ε / (4 * Real.log (p : ℝ)))) = Real.exp (-(α * ε / 4)) := by
              rw [Real.rpow_def_of_pos hp_pos]
              have hlog_ne : Real.log (p : ℝ) ≠ 0 := by
                apply _root_.ne_of_gt
                apply Real.log_pos
                norm_cast
                linarith [hp3]
              have : Real.log (p : ℝ) * (-(α * ε / (4 * Real.log (p : ℝ))))
                  = (-(α * ε / (4 * Real.log (p : ℝ)))) * Real.log (p : ℝ) := by ring_nf
              rw [this]
              have : (-(α * ε / (4 * Real.log (p : ℝ)))) * Real.log (p : ℝ) = -(α * ε / 4) := by
                field_simp [hlog_ne]
              apply congr_arg Real.exp
              rw [this]
            rw [hpow]

  have h_sum :
    ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(α * (γ_values p + 2)))
      = c * ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(2 * α)) := by
    rw [Finset.sum_congr rfl hterm_eq, Finset.mul_sum]

  have h_nonneg : ∀ n ∈ Finset.Icc 3 (2 * X + 1), n ∉ primesUpTo X → 0 ≤ (n : ℝ) ^ (-(2 * α)) := by
    intro n hn _
    apply Real.rpow_nonneg_of_nonneg
    norm_cast
    linarith
  have h_le_range := Finset.sum_le_sum_of_subset_of_nonneg h_subset_range h_nonneg

  calc
    ∑ p ∈ primesUpTo X,
      (p : ℝ) ^ (-(Real.log 2 / Real.log 3 *
        ((fun p : ℕ ↦ if p ≤ 2 then 1 else ε / (4 * Real.log (p : ℝ))) p + 2)))
        = ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(α * (γ_values p + 2))) := by
            congr 1
            funext p
            dsimp only [γ_values, α]
            simp only [Nat.cast_le_ofNat]
    _ = c * ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-(2 * α)) := by rw [h_sum]
    _ ≤ c * ∑ n ∈ Finset.Icc 3 (2 * X + 1), (n : ℝ) ^ (-(2 * α)) := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast h_le_range
          · linarith
    _ ≤ c * S := by
          have h_fin_le_tsum : ∑ n ∈ Finset.Icc 3 (2 * X + 1), (n : ℝ) ^ (-(2 * α)) ≤ S := by
            apply Summable.sum_le_tsum
            · intro n hn
              apply Real.rpow_nonneg_of_nonneg
              norm_cast
              linarith
            · exact hsumm
          apply mul_le_mul_of_nonneg_left
          · exact h_fin_le_tsum
          · linarith
    _ = Λ := by rfl

lemma bad_set_density_bound_quality (ε : ℝ) (hε : 0 < ε) :
  ∃ C > 0, ∀ X ≥ const_X,
    ((Finset.filter (fun n => Bad_ε n (fun p => if p ≤ 2 then 1 else ε / (4 * Real.log (p : ℝ))))
      (Finset.Icc 0 X)).card : ℝ) ≤ C * (X : ℝ) := by
  let γ_values : ℕ → ℝ := fun n => if n ≤ 2 then 1 else ε / (4 * Real.log (n : ℝ))
  have hg_pos : ∀ n : ℕ, 0 < γ_values n := by
    intro n
    dsimp [γ_values]
    by_cases hn : n ≤ 2
    · rw [if_pos hn]
      norm_num
    · rw [if_neg hn]
      have hn_pos : 2 < n := Nat.lt_of_not_le hn
      have hpos : (n : ℝ) > 1 := by norm_cast; linarith [hn_pos]
      have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hpos
      exact div_pos hε (mul_pos (by norm_num : (4 : ℝ) > 0) hlog_pos)

  rcases construct_HΛ_for_quality ε hε with ⟨Λ, hΛpos, hHΛ⟩
  have hΛ_nonneg : 0 ≤ Λ := le_of_lt hΛpos
  exact bad_set_density_bound_param γ_values hg_pos Λ hΛ_nonneg
    (fun X hX => by simpa [γ_values] using hHΛ X hX)

end Chernoff

end DkMath.ABC
