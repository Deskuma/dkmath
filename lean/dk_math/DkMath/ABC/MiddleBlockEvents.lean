/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.MiddleBlockMGF

#print "file: DkMath.ABC.MiddleBlockEvents"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleBlockTail.lean` から切り出した mid-block event owner。
  `Kset`, `Emid`, `GoodX` と、それらの点ごと・集合論的な基本補題を置く。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob

/- k の索引集合（固定 X） -/
def Kset (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1)

/- 中域の上側偏差イベント E_k（固定 X, δ） -/
def Emid
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) (δ : ℝ) (k X : ℕ) : Set Ω :=
  {ω |
    Zmid (k := k) (X := X) (Smap := Smap) ω
      ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
        + δ * (Finset.card (MidBlock k X) : ℝ)}

/- 同時良性事象（全部の k で上側偏差が起きない） -/
def GoodX
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) (δ : ℝ) (X : ℕ) : Set Ω :=
  {ω | ∀ k ∈ Kset X, ¬ (ω ∈ Emid (μ := μ) (Smap := Smap) δ k X)}

/- GoodX の補集合は k 合併そのもの。 -/
lemma goodX_compl_eq_union
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) (δ : ℝ) (X : ℕ) :
  (GoodX (μ := μ) (Smap := Smap) δ X)ᶜ
    = {ω | ∃ k, k ∈ Kset X ∧ ω ∈ Emid (μ := μ) (Smap := Smap) δ k X} := by
  classical
  ext ω
  apply Iff.intro
  · intro h
    have ⟨k, hk_imp⟩ := Classical.not_forall.mp h
    have ⟨hk, hnn⟩ := Classical.not_imp.mp hk_imp
    exact ⟨k, hk, Classical.not_not.mp hnn⟩
  · intro hbi
    rcases hbi with ⟨k, hk, hmem⟩
    intro H
    exact (H k hk) hmem

/- `ω ∈ GoodX` なら全 k∈K(X) で `Zmid ≤ 期待値 + δ·card`。 -/
lemma goodX_pointwise
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) {δ : ℝ} {X : ℕ} {ω : Ω} :
  ω ∈ GoodX (μ := μ) (Smap := Smap) δ X →
  ∀ ⦃k⦄, k ∈ Kset X →
    Zmid (k := k) (X := X) (Smap := Smap) ω
      ≤ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
        + δ * (Finset.card (MidBlock k X) : ℝ) := by
  intro hGood k hk
  exact le_of_not_ge (hGood k hk)

/- `ω ∈ GoodX` なら `Zmid ≤ expectation + (q.toReal + δ)·card`。 -/
lemma goodX_pointwise_qaddδ_card
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) {δ : ℝ} {X k : ℕ} {ω : Ω} (q : ENNReal)
  (hq_ne : q ≠ ⊤) (hprob : ∀ v ∈ MidBlock k X, μ ↑(Smap v) ≤ q) :
  ω ∈ GoodX (μ := μ) (Smap := Smap) δ X →
  k ∈ Kset X →
    Zmid (k := k) (X := X) (Smap := Smap) ω
      ≤ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + (q.toReal + δ) * (Finset.card (MidBlock k X) : ℝ) := by
  intro hGood hk
  have hZ_le_E_plus := goodX_pointwise (μ := μ) (Smap := Smap) hGood hk
  have _ := hq_ne
  have _ := hprob
  let cardR : ℝ := (Finset.card (MidBlock k X) : ℝ)
  have rhs_eq : (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * cardR + q.toReal * cardR
      = (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + (q.toReal + δ) * cardR := by
    ring
  have h_cardR_nonneg : 0 ≤ cardR := by
    exact Nat.cast_nonneg (Finset.card (MidBlock k X))
  have hq_nonneg : 0 ≤ q.toReal := ENNReal.toReal_nonneg
  have h_qr_nonneg : 0 ≤ q.toReal * cardR := mul_nonneg hq_nonneg h_cardR_nonneg
  have hstep : (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * cardR
      ≤ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * cardR + q.toReal * cardR :=
    le_add_of_nonneg_right h_qr_nonneg
  have hchain := le_trans hZ_le_E_plus hstep
  rw [rhs_eq] at hchain
  exact hchain

/- sum-over-k version. -/
lemma goodX_sum_over_k_qaddδ_card
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) {δ : ℝ} {X : ℕ} (q : ENNReal)
  (hq_ne : q ≠ ⊤)
  (hprob : ∀ k v, k ∈ Kset X → v ∈ MidBlock k X → μ ↑(Smap v) ≤ q)
  (ω : Ω) (hGood : ω ∈ GoodX (μ := μ) (Smap := Smap) δ X) :
  (∑ k ∈ Kset X, Zmid (k := k) (X := X) (Smap := Smap) ω)
    ≤ (∑ k ∈ Kset X, (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)))
      + (q.toReal + δ) * (∑ k ∈ Kset X, (Finset.card (MidBlock k X) : ℝ)) := by
  have H : ∀ k ∈ Kset X, Zmid (k := k) (X := X) (Smap := Smap) ω
      ≤ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + (q.toReal + δ) * (Finset.card (MidBlock k X) : ℝ) := by
    intro k hk
    exact (goodX_pointwise_qaddδ_card (μ := μ) (Smap := Smap) (q := q) (hq_ne := hq_ne)
      (hprob := fun v hv => hprob k v hk hv) hGood hk)
  calc
    (∑ k ∈ Kset X, Zmid (k := k) (X := X) (Smap := Smap) ω)
        ≤ ∑ k ∈ Kset X, ((∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + (q.toReal + δ) * (Finset.card (MidBlock k X) : ℝ)) :=
      Finset.sum_le_sum H
    _ = (∑ k ∈ Kset X, (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)))
        + (q.toReal + δ) * (∑ k ∈ Kset X, (Finset.card (MidBlock k X) : ℝ)) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]

/- Kset is monotone in X. -/
lemma Kset_mono {X Y : ℕ} (hXY : X ≤ Y) : Kset X ≤ Kset Y := by
  intro k hk
  let ⟨hmem_range_mem, hpred⟩ := Finset.mem_filter.mp hk
  let hmem_range := Finset.mem_range.mp hmem_range_mem
  have hmem_range' : k < Y + 1 := Nat.lt_of_lt_of_le hmem_range (Nat.succ_le_succ hXY)
  have hpred' : (2 : ℕ) ^ (k + 1) ≤ Y + 1 := le_trans hpred (Nat.succ_le_succ hXY)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmem_range', hpred'⟩

/- GoodX is antitone in X, assuming monotonicity of the underlying events. -/
lemma GoodX_antitone
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) {δ : ℝ} {X Y : ℕ} (hXY : X ≤ Y)
  (hEmid_mono : ∀ k, k ∈ Kset X → Emid (μ := μ) (Smap := Smap) δ k X ⊆ Emid (μ := μ) (Smap := Smap) δ k Y) :
  (GoodX (μ := μ) (Smap := Smap) δ Y) ⊆ (GoodX (μ := μ) (Smap := Smap) δ X) := by
  intro ω h
  have hK := Kset_mono hXY
  intro k hk
  simp only [GoodX] at h
  have hnY : ¬ ω ∈ Emid (μ := μ) (Smap := Smap) δ k Y := h k (hK hk)
  have : Emid (μ := μ) (Smap := Smap) δ k X ⊆ Emid (μ := μ) (Smap := Smap) δ k Y := hEmid_mono k hk
  intro hcontra
  exact hnY (this hcontra)

end Prob

end DkMath.ABC
