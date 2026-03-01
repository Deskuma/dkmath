/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC011

#print "file: DkMath.ABC.ABC012"

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


-- Ksmall / Klarge: split Kset X by k < 3 and k ≥ 3
def Ksmall (X : ℕ) : Finset ℕ := (Kset X).filter fun k => k < 3
def Klarge (X : ℕ) : Finset ℕ := (Kset X).filter fun k => 3 ≤ k


/-- Kset X を k<3 と k≥3 に分け、前者の個数は ≤ 3。 -/
lemma Kset_disjoint_union (X : ℕ) :
  Disjoint (Ksmall X) (Klarge X) ∧ (Ksmall X) ∪ (Klarge X) = Kset X := by
  classical
  constructor
  · -- 排反性: k<3 と 3≤k は排反
    refine Finset.disjoint_left.mpr fun k hkS hkL => ?_
    have ⟨hkK, hklt⟩ := Finset.mem_filter.1 hkS
    have ⟨_, hkle⟩ := Finset.mem_filter.1 hkL
    exact lt_irrefl k (lt_of_lt_of_le hklt hkle)
  · -- 分割の包含
    ext k; constructor
    · intro hk
      rcases Finset.mem_union.mp hk with hkS | hkL
      · exact (Finset.mem_filter.1 hkS).1
      · exact (Finset.mem_filter.1 hkL).1
    · intro hk
      have hkK : k ∈ Kset X := hk
      by_cases hklt : k < 3
      · -- build a proof k ∈ Ksmall X via simp on mem_filter, then place it into the union
        have hsmall : k ∈ Ksmall X := by simp [Ksmall, Finset.mem_filter, hkK, hklt]
        apply Finset.mem_union.mpr; left; exact hsmall
      · -- build a proof k ∈ Klarge X similarly and place it into the union
        have hkge : 3 ≤ k := Nat.not_lt.mp hklt
        have hlarge : k ∈ Klarge X := by simp [Klarge, Finset.mem_filter, hkK, hkge]
        apply Finset.mem_union.mpr; right; exact hlarge


/-- Ksmall の要素数は最大 3 -/
lemma card_Ksmall_le_three (X : ℕ) : (Ksmall X).card ≤ 3 := by
  classical
  -- Ksmall X ⊆ range 3 (i.e. {0,1,2}), since k < 3 for all k in Ksmall
  have hsub : (Ksmall X) ⊆ (Finset.range 3 : Finset ℕ) := by
    intro k hk
    have ⟨_, hklt⟩ := Finset.mem_filter.1 hk
    exact Finset.mem_range.mpr hklt
  calc
    (Ksmall X).card ≤ (Finset.range 3).card := Finset.card_le_card hsub
    _ = 3 := by simp [Finset.card_range]


/- 独立版 dyadic tail 補題 -/
--
-- 独立性仮定の下で、中域の上側偏差事象 Emid の確率は k≥3 のとき二次的に指数的に減衰することを示す補題（簡易版）。
--
-- ここでは簡潔のため定数 C = 1 を用い、任意の k ≥ 3 に対して
--    μ.real (Emid μ Smap δ k X) ≤ Real.exp ( - (δ ^ 2) * (2 : ℝ) ^ k )
-- が成り立つことを主張する。実用上は定数係数を許すバージョンが有用だが、まずは形を整える。
--/
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


/-- 独立版：固定 X の k 合併確率を midblockCstarIndep δ で吸収。 -/
theorem midblock_union_absorb_indep_const
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ)
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ≤ midblockCstarIndep δ := by
  -- split Kset into small and large indices
  let K := Kset X
  let Ksm := Ksmall X
  let Klg := Klarge X
  have hdisj_union := Kset_disjoint_union X
  have hcard_small := card_Ksmall_le_three X
  -- bound small side by card * 1 (probability ≤ 1)
  have small_bound : μ.real (⋃ k ∈ Ksm, Emid (μ := μ) (Smap := Smap) δ k X) ≤ (Ksm.card : ℝ) := by
    have h := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) Ksm (fun k => Emid (μ := μ) (Smap := Smap) δ k X)
    calc
      μ.real (⋃ k ∈ Ksm, Emid (μ := μ) (Smap := Smap) δ k X) ≤ ∑ k ∈ Ksm, μ.real (Emid (μ := μ) (Smap := Smap) δ k X) := h
      _ ≤ ∑ k ∈ Ksm, 1 := by apply Finset.sum_le_sum; intro k hk; exact prob_real_le_one μ _
      _ = (Ksm.card : ℝ) := by simp [Finset.sum_const]
  -- bound large side by dyadic tail lemma and sum
  have large_bound : μ.real (⋃ k ∈ Klg, Emid (μ := μ) (Smap := Smap) δ k X) ≤ ∑ k ∈ Klg, Real.exp (-(δ ^ 2 * (2 : ℝ) ^ k)) := by
    have hboole := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) Klg (fun k => Emid (μ := μ) (Smap := Smap) δ k X)
    have hsum_le : (∑ k ∈ Klg, μ.real (Emid (μ := μ) (Smap := Smap) δ k X)) ≤ ∑ k ∈ Klg, Real.exp (-(δ ^ 2 * (2 : ℝ) ^ k)) := by
      apply Finset.sum_le_sum
      intro k hk
      have ⟨memKset, hk_ge3⟩ := Finset.mem_filter.mp hk
      have ⟨_, h2k_le⟩ := Finset.mem_filter.mp memKset
      exact midblock_tail_indep_dyadic_strong (μ := μ) (Smap := Smap) (hind := hind) (hδ := hδ) (h2k_le) hk_ge3
    exact le_trans hboole hsum_le
  -- rewrite the bounded iUnion over Kset X into the union of the two bounded iUnions
  have union_eq : (⋃ k ∈ K, Emid (μ := μ) (Smap := Smap) δ k X) =
    (⋃ k ∈ Ksm, Emid (μ := μ) (Smap := Smap) δ k X) ∪ (⋃ k ∈ Klg, Emid (μ := μ) (Smap := Smap) δ k X) := by
    -- `Ksm ∪ Klg = Kset X` from `Kset_disjoint_union` and `K = Kset X` by `let` binding
    change (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) = _
    rw [← (Kset_disjoint_union X).2, Finset.set_biUnion_union]

  have step12 : μ.real (⋃ k ∈ K, Emid (μ := μ) (Smap := Smap) δ k X) ≤
    μ.real (⋃ k ∈ Ksm, Emid (μ := μ) (Smap := Smap) δ k X) + μ.real (⋃ k ∈ Klg, Emid (μ := μ) (Smap := Smap) δ k X) := by
    rw [union_eq]
    exact MeasureTheory.measureReal_union_le _ _
  have step3 : μ.real (⋃ k ∈ Ksm, Emid (μ := μ) (Smap := Smap) δ k X) + μ.real (⋃ k ∈ Klg, Emid (μ := μ) (Smap := Smap) δ k X)
    ≤ (Ksm.card : ℝ) + ∑ k ∈ Klg, Real.exp (-(δ ^ 2 * (2 : ℝ) ^ k)) := by linarith [small_bound, large_bound]
  have step4 : (Ksm.card : ℝ) + ∑ k ∈ Klg, Real.exp (-(δ ^ 2 * (2 : ℝ) ^ k)) ≤ 3 + ∑' k, Real.exp (-(δ ^ 2 * (2 : ℝ) ^ k)) := by
    have h3 : (Ksm.card : ℝ) ≤ 3 := by exact_mod_cast hcard_small
    -- promote finite Klg-sum to the infinite tsum using the summability lemma from ABC.lean
    have hc : 0 < (δ ^ 2) := pow_pos hδ 2
    have h_summ : Summable (fun k => Real.exp (-(δ ^ 2 * (2 : ℝ) ^ k))) := by
      have hs := summable_exp_neg_two_pow (c := δ ^ 2) hc
      simpa using hs
    have hsum_to_tsum := h_summ.sum_le_tsum Klg (fun k _ => le_of_lt (Real.exp_pos _))
    apply add_le_add h3 hsum_to_tsum
  -- chain the inequalities: full union ≤ small+large ≤ (Ksm.card + sum) ≤ 3 + tsum
  have final_le : μ.real (⋃ k ∈ K, Emid (μ := μ) (Smap := Smap) δ k X) ≤ 3 + ∑' k, Real.exp (-(δ ^ 2 * (2 : ℝ) ^ k)) :=
    (le_trans step12 (le_trans step3 step4))
  exact (le_trans final_le (by simp [midblockCstarIndep]))


/-- 独立版：GoodX の測度は `1 - midblockCstarIndep δ` 以上。 -/
lemma goodX_measure_ge_one_sub_midblockCstarIndep
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ)
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  μ.real (GoodX (μ := μ) (Smap := Smap) δ X) ≥ 1 - midblockCstarIndep δ := by
    -- bound on the union from the midblock absorption lemma
    have hU : μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ≤ midblockCstarIndep δ :=
      midblock_union_absorb_indep_const (μ := μ) (Smap := Smap) (hind := hind) (hδ := hδ) (X := X)

    -- cover: show Set.univ = (⋃ k ∈ Kset X, Emid ...) ∪ GoodX by case analysis using `goodX_compl_eq_union`
    have hcover : μ (Set.univ : Set Ω) ≤
      μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
      + μ (GoodX (μ := μ) (Smap := Smap) δ X) := by
      have : (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ∪ (GoodX (μ := μ) (Smap := Smap) δ X) = (Set.univ : Set Ω) := by
        ext ω
        show ω ∈ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ∪ GoodX (μ := μ) (Smap := Smap) δ X ↔ ω ∈ Set.univ
        constructor
        · intro _; trivial
        · intro _
          by_cases hmem : ω ∈ GoodX (μ := μ) (Smap := Smap) δ X
          · exact Or.inr hmem
          · have hex : ω ∈ (GoodX (μ := μ) (Smap := Smap) δ X)ᶜ := hmem
            have mem_ex := (goodX_compl_eq_union (μ := μ) (Smap := Smap) (δ := δ) (X := X)).symm ▸ hex
            have union_eq : (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
              = {ω | ∃ k, k ∈ Kset X ∧ ω ∈ Emid (μ := μ) (Smap := Smap) δ k X} := by
              ext x
              simp [Set.mem_iUnion]
            have mem_union := union_eq.symm ▸ mem_ex
            exact Or.inl mem_union
      have h := MeasureTheory.measure_union_le (μ := μ) (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) (GoodX (μ := μ) (Smap := Smap) δ X)
      simpa [this] using h

    -- convert ENNReal measures to real numbers carefully using toReal lemmas
    have μuniv_ne_top : μ (Set.univ : Set Ω) ≠ ⊤ := by simp [IsProbabilityMeasure.measure_univ]
    have μ_union_le_univ : μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ≤ μ (Set.univ : Set Ω) :=
      MeasureTheory.measure_mono (μ := μ) (Set.subset_univ _)
    have μ_union_ne_top : μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ≠ ⊤ :=
      ne_top_of_le_ne_top μuniv_ne_top μ_union_le_univ
    have μ_good_le_univ : μ (GoodX (μ := μ) (Smap := Smap) δ X) ≤ μ (Set.univ : Set Ω) :=
      MeasureTheory.measure_mono (μ := μ) (Set.subset_univ _)
    have μ_good_ne_top : μ (GoodX (μ := μ) (Smap := Smap) δ X) ≠ ⊤ :=
      ne_top_of_le_ne_top μuniv_ne_top μ_good_le_univ
    have sum_ne_top : (μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) + μ (GoodX (μ := μ) (Smap := Smap) δ X)) ≠ ⊤ :=
      (ENNReal.add_ne_top.mpr ⟨μ_union_ne_top, μ_good_ne_top⟩)

    have h_toReal := ENNReal.toReal_mono sum_ne_top hcover
    have h_toReal_add_le : (μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) + μ (GoodX (μ := μ) (Smap := Smap) δ X)).toReal
      ≤ (μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)).toReal
        + (μ (GoodX (μ := μ) (Smap := Smap) δ X)).toReal := ENNReal.toReal_add_le

    have : 1 ≤ μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
      + μ.real (GoodX (μ := μ) (Smap := Smap) δ X) := by
      calc
        1 = (μ (Set.univ : Set Ω)).toReal := by simp [IsProbabilityMeasure.measure_univ]
        _ ≤ (μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) + μ (GoodX (μ := μ) (Smap := Smap) δ X)).toReal := h_toReal
        _ ≤ μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
          + μ.real (GoodX (μ := μ) (Smap := Smap) δ X) := h_toReal_add_le

    have h_ge_goodx : μ.real (GoodX (μ := μ) (Smap := Smap) δ X)
        ≥ 1 - μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) := by linarith

    have h_one_sub : 1 - midblockCstarIndep δ ≤ 1 - μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) :=
      sub_le_sub_left hU (1 : ℝ)

    exact le_trans h_one_sub h_ge_goodx

end Prob

end ABC
