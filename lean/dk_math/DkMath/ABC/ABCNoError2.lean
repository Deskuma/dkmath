/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABCNoError

#print "file: DkMath.ABC.ABCNoError2"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-- `adjBadCount` は対角 `diagBadCount` に 2 倍スケールで抑え込める -/
lemma adjBadCount_le_diag (δ : ℝ) (X : ℕ) :
  adjBadCount δ X ≤ diagBadCount δ (2*X+1) := by
  let g := fun (n : ℕ) => n + 1
  -- Note: avoid locally shadowing global DecidablePred instances; adjBadCount is defined
  -- using the global instance so reusing that avoids definitional mismatches.
  have g_inj : Function.Injective g := by intro x y h; exact Nat.succ.inj h

  -- show image of s is contained in the diagonal bad set for 2*X+1
  have img_sub : (((Finset.Icc 1 X).filter fun n => Bad δ (Adj n)).image g)
    ⊆ (Finset.Icc 1 (2*X+1)).filter (fun b => is_bad_a δ (2*X+1) b (b-1)) := by
    intro b hb
    rcases Finset.mem_image.1 hb with ⟨n, hnS, rfl⟩
    rcases Finset.mem_filter.1 hnS with ⟨hnIcc, hBad⟩
    rcases Finset.mem_Icc.1 hnIcc with ⟨hn1, hnX⟩
    have h_ab_le : n ≤ 2 * X + 1 := by
      have hnX' : n ≤ X := hnX
      calc
        n ≤ X := hnX'
        _ = X * 1 := by rw [mul_one]
        _ ≤ X * 2 := by exact Nat.mul_le_mul_left X (by decide : 1 ≤ 2)
        _ = 2 * X := by rw [mul_comm]
        _ ≤ 2 * X + 1 := Nat.le_succ (2 * X)
    have h_b_le : (n+1) ≤ 2*X+1 := by
      have h2n1_le : 2 * n + 1 ≤ 2 * X + 1 := by
        have : n ≤ X := hnX
        calc
          2 * n + 1 = (2 * n) + 1 := by rw [add_comm]
          _ ≤ (2 * X) + 1 := by
            have h2 : 2 * n ≤ 2 * X := Nat.mul_le_mul_left 2 (by linarith)
            exact add_le_add h2 (by linarith)
          _ = 2 * X + 1 := by rw [add_comm]
      have : n + 1 ≤ 2 * n + 1 := by nlinarith
      exact le_trans this h2n1_le
    have h_ib : is_bad_a δ (2*X+1) (n+1) n := by
      dsimp [is_bad_a]
      refine ⟨coprime_succ n, ?_, ?_, ?_, ?_⟩
      · exact h_ab_le
      · exact h_b_le
      · have : n + (n + 1) ≤ 2*X+1 := by
          -- we prove the inequality by first showing 2*n ≤ 2*X and then
          -- adding 1 to both sides.
          have h_le : n ≤ X := hnX
          have h2n : 2 * n ≤ 2 * X := by
            exact Nat.mul_le_mul_left 2 h_le
          have : 2 * n + 1 ≤ 2 * X + 1 := by
            -- avoid a mismatched form from `add_le_add_right` by using nlinarith
            nlinarith [h2n]
          calc
            n + (n + 1) = 2 * n + 1 := by ring
            _ ≤ 2 * X + 1 := this
        exact this
      · simpa [Adj_eq_Adj'] using hBad
    have hbIcc : g n ∈ Finset.Icc 1 (2*X+1) := by
      refine Finset.mem_Icc.2 ?_
      constructor
      · exact Nat.le_trans hn1 (Nat.le_succ n)
      · exact h_b_le
    exact Finset.mem_filter.2 ⟨hbIcc, by simpa [g] using h_ib⟩

  -- (s.image g).card ≤ diagBadCount δ (2*X+1)
  have himg_le : (((Finset.Icc 1 X).filter fun n => Bad δ (Adj n)).image g).card
    ≤ diagBadCount δ (2*X+1) := by
    change (((Finset.Icc 1 X).filter fun n => Bad δ (Adj n)).image g).card
      ≤ ((Finset.Icc 1 (2*X+1)).filter (fun b => is_bad_a δ (2*X+1) b (b-1))).card
    exact Finset.card_le_card img_sub

  -- cards are equal because g is injective on the exact filter expression used in `adjBadCount`.
  have img_eq := Finset.card_image_of_injective ((Finset.Icc 1 X).filter fun n => Bad δ (Adj n)) g_inj
  have hcard_le' : ((Finset.Icc 1 X).filter fun n => Bad δ (Adj n)).card ≤ diagBadCount δ (2*X+1) := by
    have : (((Finset.Icc 1 X).filter fun n => Bad δ (Adj n)).image g).card ≤ diagBadCount δ (2*X+1) := himg_le
    rw [img_eq] at this
    exact this
  -- finish by unfolding `adjBadCount` and apply `hcard_le'`
  dsimp [adjBadCount]
  exact hcard_le'

/-- Adjacent bad は密度 0：adjBadCount(X)/X → 0 -/
theorem tendsto_adj_bad_fraction_zero :
  Tendsto (fun X : ℕ => (adjBadCount 0.435 X : ℝ) / (X : ℝ)) atTop (nhds 0) := by
  apply tendsto_order.2
  apply And.intro
  -- lower bound: sequence is ≥ 0 eventually
  · intro a' ha'
    refine Filter.eventually_atTop.2 ⟨1, fun X hXge1 => by
      have : (0 : ℝ) ≤ (adjBadCount 0.435 X : ℝ) := by exact_mod_cast (Nat.zero_le _)
      have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hXge1)
      have hnonneg := div_nonneg this (le_of_lt hXpos)
      exact lt_of_lt_of_le ha' hnonneg⟩
  -- upper bound: for any ε>0 show eventually adjBadCount/X < ε
  · intro ε hε
    let ε3 := ε / 4
    have hε3 : 0 < ε3 := by exact div_pos hε (by norm_num)
    have hdiag := eventually_diagBadCount_oX (hU := Bad_diff_uniform 0.435) ε3 hε3
    have ⟨s, hs_mem, hs_forall⟩ := Filter.eventually_iff_exists_mem.1 hdiag
    have ⟨N, hIci⟩ : ∃ N, Set.Ici N ⊆ s := by simpa using hs_mem
    let M := max 1 N
    refine Filter.eventually_atTop.2 ⟨M, fun X hM => by
      have one_le_X : 1 ≤ X := le_trans (le_max_left 1 N) hM
      have N_le_X : N ≤ X := le_trans (le_max_right 1 N) hM
      have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) one_le_X)
      -- adjBadCount ≤ diagBadCount at 2*X+1, cast and divide
      have Hnat := adjBadCount_le_diag 0.435 X
      have H : (adjBadCount 0.435 X : ℝ) ≤ (diagBadCount 0.435 (2 * X + 1) : ℝ) := by exact_mod_cast Hnat
      have hle1 := div_le_div_of_nonneg_right H (le_of_lt hXpos)
      -- ensure 2*X+1 ∈ s by showing 2*X+1 ≥ N
      have twoX1_ge_N : (2 * X + 1 : ℕ) ≥ N := by linarith [N_le_X]
      have hdiag_at := hs_forall (2 * X + 1) (hIci twoX1_ge_N)
      -- combine bounds: diagBadCount(2X+1) ≤ ε3*(2X+1)
      have hle2 : (diagBadCount 0.435 (2 * X + 1) : ℝ) / (X : ℝ) ≤ (ε3 * (2 * X + 1 : ℝ)) / (X : ℝ) := by
        have : (diagBadCount 0.435 (2 * X + 1) : ℝ) ≤ ε3 * (2 * X + 1 : ℝ) := by simpa using hdiag_at
        exact div_le_div_of_nonneg_right this (le_of_lt hXpos)
      -- Now (adjBadCount/X) ≤ ε3 * (2X+1)/X. Bound (2X+1)/X ≤ 3 by comparing integers and casting.
      have twoX1_le_3X_nat : 2 * X + 1 ≤ 3 * X := by linarith [one_le_X]
      have twoX1_le_3X : (2 * X + 1 : ℝ) ≤ 3 * (X : ℝ) := by exact_mod_cast twoX1_le_3X_nat
      have twoX1_div_X_le_3 : (2 * X + 1 : ℝ) / (X : ℝ) ≤ 3 := by
        have h := div_le_div_of_nonneg_right twoX1_le_3X (le_of_lt hXpos)
        have : (3 * (X : ℝ)) / (X : ℝ) = 3 := by field_simp [Ne.symm (by exact_mod_cast (ne_of_gt hXpos))]
        simpa [this] using h
      have bound1 : (adjBadCount 0.435 X : ℝ) / (X : ℝ) ≤ ε3 * 3 := by
        calc
          (adjBadCount 0.435 X : ℝ) / (X : ℝ) ≤ (diagBadCount 0.435 (2 * X + 1) : ℝ) / (X : ℝ) := hle1
          _ ≤ (ε3 * (2 * X + 1 : ℝ)) / (X : ℝ) := hle2
          _ = ε3 * ((2 * X + 1 : ℝ) / (X : ℝ)) := by field_simp [Ne.symm (by exact_mod_cast (ne_of_gt hXpos))]
          _ ≤ ε3 * 3 := by apply mul_le_mul_of_nonneg_left twoX1_div_X_le_3 (le_of_lt hε3)
      -- finally compare ε3 * 3 < ε since ε3 = ε/4 and 3/4 < 1
      have hlt : ε3 * 3 < ε := by
        calc
          ε3 * 3 = (ε / 4) * 3 := by dsimp [ε3]
          _ = ε * ((3 : ℝ) / 4) := by field_simp [mul_comm]
          _ < ε := by
            have : (3 : ℝ) / 4 < 1 := by norm_num
            simpa [mul_one] using mul_lt_mul_of_pos_left this hε
      have : (adjBadCount 0.435 X : ℝ) / (X : ℝ) < ε := by
        apply lt_of_le_of_lt bound1 hlt
      exact this
    ⟩

/- 小補題：eventually を区間上の有限条件に落とす -/
theorem eventually_forall_on_Icc_of_eventually {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) :
  ∃ M, ∀ X, M ≤ X → ∀ n ∈ (Finset.Icc 1 X), (n < M) ∨ P n := by
  rcases (Filter.eventually_iff_exists_mem.1 h) with ⟨S, S_mem, S_forall⟩
  have ⟨N, hN⟩ : ∃ N, Set.Ici N ⊆ S := by simpa using S_mem
  use N
  intro X hX n hn
  by_cases hnm : n < N
  · left; exact hnm
  · right
    have hge : n ≥ N := not_lt.mp hnm
    have hinS : n ∈ S := hN hge
    exact S_forall n hinS

/- 小補題：固定された prefix 長さ M に対して M / X → 0 -/
theorem prefix_over_X_tendsto_zero (M : ℕ) :
  Tendsto (fun X : ℕ => (M : ℝ) / (X : ℝ)) atTop (nhds 0) := by
  have hconstM : Tendsto (fun (_ : ℕ) => (M : ℝ)) atTop (nhds (M : ℝ)) := tendsto_const_nhds
  have hinv := @tendsto_const_div_nat_rpow_atTop_0 (1 : ℝ) (1 : ℝ) (by norm_num : 0 < (1 : ℝ))
  simpa [div_eq_mul_inv, mul_comm] using (Tendsto.mul hconstM hinv)



end ABC
