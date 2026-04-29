/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBlockKSplit

#print "file: DkMath.ABC.MiddleBlockIndependentDyadic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleBlockIndependentTail.lean` から切り出した independent dyadic tail owner。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob

-- real 算術：n ≥ 8 ⇒ (2 n^2)/(n+8) ≥ n
/-- n が 8 以上かつ 0 以上のとき、(2 * n^2) / (n + 8) は n 以上であることを示す補題 -/
lemma two_mul_sq_over_add_ge_self {n : ℝ} (hn8 : (8 : ℝ) ≤ n) (hn0 : 0 ≤ n) :
  (2 * n^2) / (n + 8) ≥ n := by
  have hpos : 0 < n + 8 := by linarith
  -- 2 n^2 - n*(n+8) = n*(n-8) ≥ 0 when n ≥ 8
  have sub_eq : 2 * n^2 - n * (n + 8) = n * (n - 8) := by ring
  have hdiff_nonneg : 0 ≤ n - 8 := by linarith [hn8]
  have hprod_nonneg : 0 ≤ n * (n - 8) := mul_nonneg hn0 hdiff_nonneg
  have hsub_nonneg : 0 ≤ 2 * n^2 - n * (n + 8) := by simpa [sub_eq] using hprod_nonneg
  have hle : n * (n + 8) ≤ 2 * n ^ 2 := by linarith [hsub_nonneg]
  exact (le_div_iff₀ hpos).mpr hle

/- 独立版 dyadic tail 補題 -/
--
-- 独立性仮定の下で、中域の上側偏差事象 Emid の確率は k≥3 のとき二次的に指数的に減衰することを示す補題（簡易版）。
--
-- ここでは簡潔のため定数 C = 1 を用い、任意の k ≥ 3 に対して
--    μ.real (Emid μ Smap δ k X) ≤ Real.exp ( - (δ ^ 2) * (2 : ℝ) ^ k )
-- が成り立つことを主張する。実用上は定数係数を許すバージョンが有用だが、まずは形を整える。
lemma midblock_tail_indep_dyadic_strong
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ)
  {δ : ℝ} (hδ : 0 < δ) {k X : ℕ} (h2k_le : (2 : ℕ) ^ (k + 1) ≤ X + 1) (hk : 3 ≤ k) :
  μ.real (Emid (μ := μ) (Smap := Smap) δ k X) ≤ Real.exp (-(δ ^ 2 * (2 : ℝ) ^ k)) := by
  -- Use the independent Chernoff bound provided by `mid_block_upper_hp_indep` which states
  -- μ.real Emid ≤ exp ( - (δ * card)^2 / (4 * ((card / 8) + 1)) ). We will lower-bound card by 2^k
  -- using `MidBlock_card_lower_when_2k_le_X` and then simplify algebraically for k ≥ 3.
  have hmgf_bound := mid_block_upper_hp_indep (μ := μ) (Smap := Smap) (hind := hind) (δ := δ) (hδ := hδ) (k := k) (X := X)
  -- card of MidBlock as a real
  let card := (Finset.card (MidBlock k X) : ℝ)
  -- obtain integer lower bound |MidBlock k X| ≥ 2^k under the hypothesis (as Nat)
  have h_card_nat := MidBlock_card_lower_when_2k_le_X k X h2k_le
  -- cast the Nat inequality to ℝ by applying exact_mod_cast to the Nat proof
  have hcard_real : card ≥ (2 ^ k : ℝ) := by
    have : (Finset.card (MidBlock k X) : ℝ) ≥ (2 ^ k : ℝ) := by exact_mod_cast h_card_nat
    exact this
  -- show 2^k ≥ 8 for k ≥ 3, hence card ≥ 8
  have h2k_ge8 : (2 : ℝ) ^ k ≥ 8 := by
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_of_le (by norm_num : 2 ≤ 2) hk
    exact_mod_cast this

  -- 独立版の合併吸収補題: 小側はカード ≤ 3 で吸収、大側は dyadic tail を用いて抑える
  have h_card_ge8 : card ≥ 8 := ge_trans hcard_real h2k_ge8
  -- denom = 4 * ((card / 8) + 1) and we show denom ≤ card so that (card^2)/denom ≥ card ≥ 2^k
  let denom := 4 * (card / 8 + 1)
  have denom_eq : denom = card / 2 + 4 := by ring
  have denom_le_card : denom ≤ card := by
    rw [denom_eq]; linarith [h_card_ge8]
  have hpos_card : 0 < card := by
    have h2pos_nat : 0 < 2 ^ k := by apply Nat.pow_pos; norm_num
    have h2pos : 0 < (2 ^ k : ℝ) := by exact_mod_cast h2pos_nat
    linarith [hcard_real, h2pos]
  have denom_pos : 0 < denom := by
    have : 0 < card / 8 + 1 := by linarith [hpos_card]
    linarith
  -- from denom ≤ card and card ≥ 0 we get (card * card) / denom ≥ card
  have hcd : card * denom ≤ card * card := by
    have h' := mul_le_mul_of_nonneg_right denom_le_card (le_of_lt hpos_card)
    -- h' : denom * card ≤ card * card, commute the factors and finish
    rw [mul_comm] at h'
    exact h'
  have h_div_ge : (card * card) / denom ≥ card := by
    exact (le_div_iff₀ denom_pos).mpr hcd
  -- derive 2^k ≤ (card * card)/denom and multiply by δ^2 > 0 to get δ^2 * 2^k ≤ δ^2 * ((card * card)/denom)
  have h_le_div : (2 : ℝ) ^ k ≤ (card * card) / denom := by linarith [h_div_ge, hcard_real]
  have hδ2_pos : 0 < δ ^ 2 := by exact pow_pos hδ 2
  have h_final_le : (δ ^ 2) * ((2 : ℝ) ^ k) ≤ (δ ^ 2) * ((card * card) / denom) :=
    mul_le_mul_of_nonneg_left h_le_div (le_of_lt hδ2_pos)
  -- exponent comparison: show - (δ*card)^2 / denom ≤ - δ^2 * 2^k
  have exp_arg_le : - (δ * card) ^ 2 / denom ≤ -(δ ^ 2 * ((2 : ℝ) ^ k)) := by
    -- rewrite (δ*card)^2 / denom to δ^2 * ((card * card) / denom) and reuse h_final_le
    have hden_ne : denom ≠ 0 := by linarith [denom_pos]
    have hpow : (δ * card) ^ 2 = δ ^ 2 * card * card := by ring
    have eq_val : (δ * card) ^ 2 / denom = δ ^ 2 * ((card * card) / denom) := by
      calc
        (δ * card) ^ 2 / denom = (δ ^ 2 * card * card) / denom := by rw [hpow]
        _ = δ ^ 2 * ((card * card) / denom) := by field_simp [hden_ne]
    have htmp : δ ^ 2 * (2 : ℝ) ^ k ≤ (δ * card) ^ 2 / denom := by rwa [← eq_val] at h_final_le
    -- negate both sides to get the required inequality; rewrite the negation into the
    -- form (-(δ * card) ^ 2) / denom which matches the expected syntactic shape
    have hneg := neg_le_neg_iff.mpr htmp
    have left_eq : - ((δ * card) ^ 2 / denom) = (-(δ * card) ^ 2) / denom := by field_simp [hden_ne]
    rwa [left_eq] at hneg
  -- combine with hmgf_bound to finish
  calc
    μ.real (Emid (μ := μ) (Smap := Smap) δ k X)
        ≤ Real.exp ( - (δ * card) ^ 2 / denom) := by exact hmgf_bound

    _ ≤ Real.exp (-(δ ^ 2 * ((2 : ℝ) ^ k))) := by
      apply Real.exp_le_exp.mpr
      exact exp_arg_le

end Prob

end DkMath.ABC
