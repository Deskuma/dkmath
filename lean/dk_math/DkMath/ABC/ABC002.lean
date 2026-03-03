/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC001

#print "file: DkMath.ABC.ABC002"

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

-- -------------------------------------------------------

/--
任意の正の実数 ε に対して、1 から X までの自然数のうち
quality (Adj n) ≤ 1 + ε を満たすものの割合が X → ∞ のとき 1 に収束する、という主張です。

引数:
- `ε` : 許容誤差（実数）。
- `hε` : `0 < ε` の仮定。

内容の説明:
- 式 `((Finset.Icc 1 X).filter (fun n => quality (Adj n) ≤ 1 + ε)).card / (X : ℝ)`
  は区間 [1, X] における条件を満たす元の割合（実数としての比）を表します。
- `Tendsto ... atTop (nhds 1)` はその割合が X → ∞ の極限で 1 に収束することを意味します。
- したがって、この定理は「任意の正の ε に対して、ほとんど全ての自然数 n に対して quality (Adj n) が 1 + ε 以下である（自然密度が 1 である）」ことを表しています。

注意:
- 主張は上からの抑制（quality ≤ 1 + ε）に関するものであり、下からの近似（例えば quality → 1 を示す）を直接主張するものではありません。
- 証明の詳細や `Adj`・`quality` の定義は本文を参照してください。
- 名前の末尾 `no_equiv` は、定理が特定の等価条件を仮定していないことを示唆している可能性があります（実装依存）。
- 用途としては、集合論的・解析的手法で「良い」性質を持つ元が集合の大部分を占めることを示す状況で役立ちます。
-/
theorem adj_quality_density_one_no_equiv (ε : ℝ) (hε : 0 < ε) :
  Tendsto (fun X : ℕ => ((Finset.Icc 1 X).filter (fun n => quality (Adj n) ≤ 1 + ε)).card / (X : ℝ))
    atTop (nhds 1) := by
  -- use the eventual implication axiom: a.e. (¬Bad → quality ≤ 1+ε)
  let P := fun n => (¬ Bad 0.435 (Adj n) → quality (Adj n) ≤ 1 + ε)
  have hP_event : ∀ᶠ n in atTop, P n := Keystone_bridge_quality_adjacent_imp ε hε

  -- convert eventual pointwise statement to an interval-uniform statement: get M so that
  -- for all X ≥ M and n ∈ Icc 1 X, either n < M or P n holds.
  rcases eventually_forall_on_Icc_of_eventually hP_event with ⟨M, hM⟩
  let M0 := max M 1

  -- define the target sequence f and a convenient lower bound g
  let f := fun X => ((Finset.Icc 1 X).filter fun n => quality (Adj n) ≤ 1 + ε).card / (X : ℝ)
  let g := fun X => (1 : ℝ) - (adjBadCount 0.435 X : ℝ) / (X : ℝ) - ((M : ℝ) / (X : ℝ))

  -- show: eventually (g X ≤ f X)
  have hge_eventually : ∀ᶠ X in atTop, g X ≤ f X := by
    refine Filter.eventually_atTop.2 ⟨M0, fun X hXge => by
      -- set up some abbreviations
      let s := (Finset.Icc 1 X)
      have one_le_X : 1 ≤ X := le_trans (le_max_right M 1) hXge
      -- from hM we get for each n ∈ s: (n < M) ∨ P n
      have hcase := fun n hn => hM X (le_trans (le_max_left M 1) hXge) n hn
      -- show that all n with n ≥ M and ¬Bad are included in the filter for quality ≤ 1+ε
      have sub : (s.filter fun n => n ≥ M ∧ ¬ Bad 0.435 (Adj n))
        ⊆ (s.filter fun n => quality (Adj n) ≤ 1 + ε) := by
        intro n hn
        rcases Finset.mem_filter.1 hn with ⟨hnIcc, ⟨hnM, hnbad⟩⟩
        rcases hcase n hnIcc with (hnlt | hPn)
        · exact False.elim (lt_irrefl _ (lt_of_lt_of_le hnlt hnM))
        · have hq := hPn
          have : quality (Adj n) ≤ 1 + ε := hq hnbad
          exact Finset.mem_filter.2 ⟨hnIcc, this⟩

      -- cardinality lower bound: the right-hand filter's card is ≥ left.card
      have hcard_ge := (Finset.card_le_card sub).trans (le_refl _)
      -- relate left.card to total non-bad count minus prefix size
      let nonbad := s.filter fun n => ¬ Bad 0.435 (Adj n)
      -- restrict prefix to non-bad elements so `nonbad` partitions as `pref ∪ left`
      let pref := s.filter fun n => n < M ∧ ¬ Bad 0.435 (Adj n)
      have hnonbad_total : nonbad.card = X - adjBadCount 0.435 X := by
        let A := s.filter fun n => Bad 0.435 (Adj n)
        have add_eq := Finset.card_filter_add_card_filter_not (s := s) (p := fun n => Bad 0.435 (Adj n))
        -- convert to subtraction form robustly by normalizing the addition order, then apply Nat.eq_sub_of_add_eq
        have hsub : nonbad.card = s.card - A.card := by
          have : (nonbad.card + A.card : ℕ) = s.card := by simpa [add_comm] using add_eq
          exact Nat.eq_sub_of_add_eq this
        have hs_card_nat : s.card = X := by dsimp [s]; simp [Nat.card_Icc]
        have hbad_def : A.card = adjBadCount 0.435 X := by dsimp [adjBadCount]
        calc
          nonbad.card = s.card - A.card := by exact hsub
          _ = X - adjBadCount 0.435 X := by rw [hs_card_nat, hbad_def]

      -- prefix is subset of range M, so pref.card ≤ M
      have hpref_sub : pref ⊆ (Finset.range M) := by
        intro n hn; rcases Finset.mem_filter.1 hn with ⟨hnIcc, ⟨hnlt, _⟩⟩; apply Finset.mem_range.mpr; exact hnlt
      have hpref_le : pref.card ≤ M := by
        have h1 : pref.card ≤ (Finset.range M).card := Finset.card_le_card hpref_sub
        have h2 : (Finset.range M).card = M := by simp
        calc
          pref.card ≤ (Finset.range M).card := h1
          _ = M := by rw [h2]

      -- let `left` be the non-bad elements with n ≥ M
      let left := s.filter fun n => n ≥ M ∧ ¬ Bad 0.435 (Adj n)
      -- show nonbad = pref ∪ left
      have part : nonbad = pref ∪ left := by
        apply Finset.ext; intro a; constructor
        · intro ha; rcases Finset.mem_filter.1 ha with ⟨haIcc, hnb⟩
          by_cases hlt : a < M
          · exact (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨haIcc, ⟨hlt, hnb⟩⟩))
          · have hge : a ≥ M := le_of_not_gt hlt
            exact (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨haIcc, ⟨hge, hnb⟩⟩))
        · intro h; rcases (Finset.mem_union.1 h) with hleft | hright
          · rcases Finset.mem_filter.1 hleft with ⟨haIcc, ⟨hlt, hnb⟩⟩; exact Finset.mem_filter.2 ⟨haIcc, hnb⟩
          · rcases Finset.mem_filter.1 hright with ⟨haIcc, ⟨hge, hnb⟩⟩; exact Finset.mem_filter.2 ⟨haIcc, hnb⟩
      -- disjointness and card arithmetic
      have disj : Disjoint pref left := by
        -- show the intersection is empty by proving no element can be in both filters
        rw [Finset.disjoint_iff_inter_eq_empty]
        apply Finset.eq_empty_of_forall_notMem
        intro a ha
        rcases Finset.mem_inter.1 ha with ⟨h1, h2⟩
        rcases Finset.mem_filter.1 h1 with ⟨_, ⟨hlt, _⟩⟩
        rcases Finset.mem_filter.1 h2 with ⟨_, ⟨hge, _⟩⟩
        exact absurd hlt (not_lt_of_ge hge)
      have card_union := Finset.card_union_of_disjoint disj
      have nonbad_add : nonbad.card = pref.card + left.card := by
        have tmp := card_union
        rw [← part] at tmp
        exact tmp
      have left_eq : left.card = nonbad.card - pref.card := by
        have add_eq : left.card + pref.card = nonbad.card := by
          simpa [add_comm] using (Eq.symm nonbad_add)
        exact Nat.eq_sub_of_add_eq add_eq
      have hleft_ge : left.card ≥ (X - adjBadCount 0.435 X) - M := by
        rw [left_eq, hnonbad_total]
        -- apply monotonicity of subtraction at the specific k := X - adjBadCount 0.435 X
        exact Nat.sub_le_sub_left hpref_le (X - adjBadCount 0.435 X)
      -- combine to get filtered_card ≥ X - adjBadCount - M
      -- filtered card ≥ left.card ≥ X - adjBadCount - M
      have hfiltered_ge : ((s.filter fun n => quality (Adj n) ≤ 1 + ε)).card ≥ (X - adjBadCount 0.435 X) - M := by
        have left_le_filtered : left.card ≤ ((s.filter fun n => quality (Adj n) ≤ 1 + ε)).card := by
          exact Finset.card_le_card sub
        calc
          ((s.filter fun n => quality (Adj n) ≤ 1 + ε)).card ≥ left.card := by linarith [left_le_filtered]
          _ ≥ (X - adjBadCount 0.435 X) - M := by linarith [hleft_ge]
      -- divide by X (>0 because X ≥ M0 ≥ 1)
      have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) one_le_X)
      have hnum_nat_le : ↑(X - adjBadCount 0.435 X - M)
        ≤ (((s.filter fun n => quality (Adj n) ≤ 1 + ε)).card : ℝ) := by
        exact_mod_cast hfiltered_ge

      -- relate the real subtraction to the casted nat-subtraction:
      -- prove (X : ℝ) - adjBad - M ≤ ↑(X - adjBad - M) (as a general inequality),
      -- so we can transitively bound the real expression by the filtered card and then divide.
      have hlhs_le_cast : (X : ℝ) - (adjBadCount 0.435 X : ℝ) - (M : ℝ)
        ≤ ↑(X - adjBadCount 0.435 X - M) := by
        let sum := adjBadCount 0.435 X + M
        by_cases hsum : sum ≤ X
        · -- if sum ≤ X then nat-subtraction behaves and casts to the same real subtraction
          have hnat : (X - adjBadCount 0.435 X - M : ℕ) = X - (adjBadCount 0.435 X + M) := by
            apply Nat.sub_sub
          have heq : (X : ℝ) - (adjBadCount 0.435 X : ℝ) - (M : ℝ)
            = ↑(X - adjBadCount 0.435 X - M) := by
            calc
              (X : ℝ) - (adjBadCount 0.435 X : ℝ) - (M : ℝ)
                  = (X : ℝ) - (↑(adjBadCount 0.435 X + M) : ℝ) := by
                simp [sub_add_eq_sub_sub]
              _ = ↑(X - adjBadCount 0.435 X - M) := by
                rw [hnat]; norm_cast
          exact le_of_eq heq
        · -- if sum > X then the nat-subtraction is 0 and the real subtraction is ≤ 0, so the inequality holds
          have hgt : X < sum := lt_of_not_ge hsum
          have hnat_zero : (X - adjBadCount 0.435 X - M : ℕ) = 0 := by
            have : X < adjBadCount 0.435 X + M := hgt
            have : X - (adjBadCount 0.435 X + M) = 0 := Nat.sub_eq_zero_of_le (le_of_lt this)
            calc
              (X - adjBadCount 0.435 X - M : ℕ) = X - (adjBadCount 0.435 X + M) := by apply Nat.sub_sub
              _ = 0 := by simpa using this
          have hRhs_zero : ↑(X - adjBadCount 0.435 X - M) = (0 : ℝ) := by simp [hnat_zero]
          -- cast the strict nat inequality to ℝ and use sub ↔ < to get a negative real difference,
          -- then convert to a ≤ statement to compare with the RHS = 0.
          have hgtR : (X : ℝ) < ↑(adjBadCount 0.435 X + M) := by exact_mod_cast hgt
          have hmid : (X : ℝ) - (adjBadCount 0.435 X : ℝ) < (M : ℝ) := by
            -- X < adjBad + M implies X - adjBad < M
            refine (sub_lt_iff_lt_add).mpr ?_
            simpa [add_comm] using hgtR
          have hneg : (X : ℝ) - (adjBadCount 0.435 X : ℝ) - (M : ℝ) < 0 := by
            -- X - adjBad < M implies (X - adjBad) - M < 0
            refine (sub_lt_iff_lt_add).mpr ?_
            simpa using hmid
          -- rewrite the RHS cast to 0, then apply le_of_lt to conclude ≤ 0
          rw [hRhs_zero]
          exact le_of_lt hneg

      -- combine to get the real inequality and then divide
      have hnum_real_le : (X : ℝ) - (adjBadCount 0.435 X : ℝ) - (M : ℝ)
        ≤ (((s.filter fun n => quality (Adj n) ≤ 1 + ε)).card : ℝ) := by
        exact (le_trans hlhs_le_cast hnum_nat_le)

      have hdiv := div_le_div_of_nonneg_right hnum_real_le (le_of_lt hXpos)

      have eq_rhs : ((X - adjBadCount 0.435 X) - M : ℝ) / (X : ℝ) = 1 - (adjBadCount 0.435 X : ℝ) / (X : ℝ) - (M : ℝ) / (X : ℝ) := by
        field_simp [Ne.symm (by exact_mod_cast (ne_of_gt hXpos))]
      calc
        g X = 1 - (adjBadCount 0.435 X : ℝ) / (X : ℝ) - (M : ℝ) / (X : ℝ) := rfl
        _ = ((X - adjBadCount 0.435 X) - M : ℝ) / (X : ℝ) := by rw [←eq_rhs]
        _ ≤ ((s.filter fun n => quality (Adj n) ≤ 1 + ε)).card / (X : ℝ) := hdiv
    ⟩

  -- show: eventually (f X ≤ 1) (trivial since filtered card ≤ X)
  have hupper_eventually : ∀ᶠ X in atTop, f X ≤ 1 := by
    refine Filter.eventually_atTop.2 ⟨1, fun X hXge => by
      have : ((Finset.Icc 1 X).filter fun n => quality (Adj n) ≤ 1 + ε).card ≤ (Finset.Icc 1 X).card := by
        apply Finset.card_le_card; intro n hn; exact (Finset.mem_filter.1 hn).1
      have : ((Finset.Icc 1 X).filter fun n => quality (Adj n) ≤ 1 + ε).card ≤ X := by
        calc
          ((Finset.Icc 1 X).filter fun n => quality (Adj n) ≤ 1 + ε).card ≤ (Finset.Icc 1 X).card := this
          _ = X := by simp [Nat.card_Icc]
      have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hXge)
      have : ((Finset.Icc 1 X).filter fun n => quality (Adj n) ≤ 1 + ε).card ≤ X := this
      have : ((Finset.Icc 1 X).filter fun n => quality (Adj n) ≤ 1 + ε).card ≤ (X : ℝ) := by exact_mod_cast this
      calc
        f X = ((Finset.Icc 1 X).filter fun n => quality (Adj n) ≤ 1 + ε).card / (X : ℝ) := rfl
        _ ≤ X / (X : ℝ) := div_le_div_of_nonneg_right this (le_of_lt hXpos)
        _ = 1 := by field_simp [Ne.symm (by exact_mod_cast (ne_of_gt hXpos))]
    ⟩

  -- build limit for g: g = 1 - adjBad/X - M/X tends to 1
  -- build limit for g: use the density wrapper plus prefix lemma
  have h_adj : Tendsto (fun X => (adjBadCount 0.435 X : ℝ) / (X : ℝ)) atTop (nhds 0) := tendsto_adj_bad_fraction_zero
  have h1 := density_one_of_complement_tendsto_zero (fun X => (adjBadCount 0.435 X : ℝ) / (X : ℝ)) h_adj
  have h_pref := prefix_over_X_tendsto_zero M
  have h_g_tendsto : Tendsto g atTop (nhds 1) := by
    -- g = (1 - adjBad/X) - M/X, and both parts tend to 1 and 0 respectively
    have h_left : Tendsto (fun X => (1 : ℝ) - (adjBadCount 0.435 X : ℝ) / (X : ℝ)) atTop (nhds 1) := h1
    simpa using (h_left.sub h_pref)

  -- apply squeeze: g ≤ f ≤ 1 eventually and g → 1 and constant 1 → 1, hence f → 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_g_tendsto (tendsto_const_nhds) hge_eventually hupper_eventually

/-- Adjacent 族で `{q ≤ 1+ε}` の相対密度 → 1 -/
theorem adj_quality_density_one (ε : ℝ) (hε : 0 < ε) :
  Tendsto (fun X : ℕ => ((Finset.Icc 1 X).filter (fun n => quality (Adj n) ≤ 1 + ε)).card / (X : ℝ))
    atTop (nhds 1) := by
  exact adj_quality_density_one_no_equiv ε hε

-- -------------------------------------------------------


end ABC
