/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBlockIndependentDyadic

#print "file: DkMath.ABC.MiddleBlockIndependentTail"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob

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

end DkMath.ABC
