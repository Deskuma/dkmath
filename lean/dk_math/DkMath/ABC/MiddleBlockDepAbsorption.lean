/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBlockDyadicTail

#print "file: DkMath.ABC.MiddleBlockDepAbsorption"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleBlockTail.lean` から切り出した dependent absorption owner。
  `midblockCstar` と dependent union / GoodX absorption を置く。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob


/- 中域・依存版の合併確率を吸収する X 非依存定数（C⋆）。 -/
noncomputable def midblockCstar (P : SubGammaParam) (δ : ℝ) : ℝ :=
  Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) *
    (∑' k : ℕ, Real.exp ( - (P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k)))


lemma midblockCstar_nonneg (P : SubGammaParam) (δ : ℝ) :
  0 ≤ midblockCstar P δ := by
  have h1 : 0 ≤ Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) :=
    le_of_lt (Real.exp_pos _)
  have h2 : 0 ≤ (∑' k : ℕ, Real.exp ( - (P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k))) :=
    tsum_nonneg (fun k => le_of_lt (Real.exp_pos _))
  simpa [midblockCstar] using mul_nonneg h1 h2


lemma union_over_k_midblock_bound_dep
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
    (h_sub : ∀ {k X : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
        μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
          - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
        Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  ∃ (C cθ : ℝ), 0 ≤ C ∧ 0 < cθ ∧
    let K : Finset ℕ :=
      (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1)
    let E : ℕ → Set Ω := fun k => Emid (μ := μ) (Smap := Smap) δ k X
    μ.real (⋃ k ∈ K, E k)
      ≤ ∑ k ∈ K, C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
  classical
  let C := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let cθ := (P.lambda0 / 2) * δ
  have hC : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hcθ : 0 < cθ := mul_pos (by simpa using half_pos P.hlambda0) hδ
  refine ⟨C, cθ, hC, hcθ, ?_⟩
  intro K E
  have : ∀ {k}, k ∈ K → μ.real (E k) ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
    intro k hk
    have h2k_le : (2 : ℕ) ^ (k + 1) ≤ X + 1 := by
      simpa [K] using (Finset.mem_filter.mp hk).2
    have hcard_bound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one h_sub (hδ := hδ)
    have h_card_nat := MidBlock_card_lower_when_2k_le_X k X h2k_le
    have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ (2 : ℝ) ^ k := by exact_mod_cast h_card_nat
    have mono : Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ))
        ≤ Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
      have negc_nonpos : -((P.lambda0 / 2) * δ) ≤ 0 := le_of_lt (neg_lt_zero.mpr hcθ)
      have le_arg : -((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ) ≤ -((P.lambda0 / 2) * δ) * ((2 : ℝ) ^ k) :=
        mul_le_mul_of_nonpos_left h_card_real negc_nonpos
      exact Real.exp_le_exp.mpr le_arg
    calc
      μ.real (E k) = μ.real {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)} := by rfl
      _ ≤ Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := hcard_bound
      _ = C * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by rfl
      _ ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by apply mul_le_mul_of_nonneg_left mono hC
  have hboole := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) K E
  exact le_trans hboole (Finset.sum_le_sum (by intro k hk; exact this hk))


/- 固定 X について、条件 `2^(k+1) ≤ X+1` を満たすすべての k で
    上側偏差イベントの合併確率を Boole で束ねる（Janson/Suen 受け口） -/
lemma union_over_k_midblock_bound_dep'
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
    (h_sub : ∀ {k X : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
        μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
          - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
        Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  ∃ (C cθ : ℝ), 0 ≤ C ∧ 0 < cθ ∧
    let K : Finset ℕ :=
      (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1)
    let E : ℕ → Set Ω := fun k =>
      {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
            + δ * (Finset.card (MidBlock k X) : ℝ)}
    μ.real (⋃ k ∈ K, E k)
      ≤ ∑ k ∈ K, C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
  classical
  let C := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let cθ := (P.lambda0 / 2) * δ
  have hC : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hcθ : 0 < cθ := mul_pos (by simpa using half_pos P.hlambda0) hδ
  refine ⟨C, cθ, hC, hcθ, ?_⟩
  intro K E
  have : ∀ {k}, k ∈ K → μ.real (E k) ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
    intro k hk
    have h2 : (2 : ℕ) ^ (k + 1) ≤ X + 1 := by
      simpa [K] using (Finset.mem_filter.mp hk).2
    have hcard_bound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one (fun h0 hL => h_sub h0 hL) (hδ := hδ)
    have h_card_nat := MidBlock_card_lower_when_2k_le_X k X h2
    have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ (2 : ℝ) ^ k := by exact_mod_cast h_card_nat
    have mono : Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ))
        ≤ Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
      have negc_nonpos : -((P.lambda0 / 2) * δ) ≤ 0 := le_of_lt (neg_lt_zero.mpr hcθ)
      have le_arg : -((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ) ≤ -((P.lambda0 / 2) * δ) * ((2 : ℝ) ^ k) :=
        mul_le_mul_of_nonpos_left h_card_real negc_nonpos
      exact Real.exp_le_exp.mpr le_arg
    calc
      μ.real (E k) = μ.real {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)} := by rfl
      _ ≤ Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := hcard_bound
      _ = C * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by rfl
      _ ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by apply mul_le_mul_of_nonneg_left mono hC
  have hboole := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) K E
  refine le_trans hboole ?_
  exact Finset.sum_le_sum (by intro k hk; exact this hk)


/- Finite-union の Boole と可和性を組み合わせて X 非依存の定数に吸収する補題。 -/
theorem midblock_union_absorb_dep
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ℕ} (Smap : ℕ → Finset Ω)
  (P : SubGammaParam) (h1 : 0 < P.v) (h2 : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {k X' : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X') (Smap := Smap) ω
        - (∑ v ∈ MidBlock k X', (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) :
  ∃ Cstar : ℝ, 0 ≤ Cstar ∧
    μ.real (⋃ k ∈ (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1),
      {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω ≥
          (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)})
    ≤ Cstar := by
  rcases Prob.union_over_k_midblock_bound_dep (μ := μ) (Smap := Smap) P h1 h2 (h_sub) hδ X
    with ⟨C, cθ, hC, hcθ, hsum_bound⟩
  let K := (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1)
  have hC_nonneg := hC
  have h_summ := Prob.summable_exp_neg_two_pow cθ hcθ
  have hsum_all : ∑ k ∈ K, C * Real.exp (- cθ * ((2 : ℝ) ^ k))
    ≤ C * (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))) := by
    have : ∑ k ∈ K, C * Real.exp (-cθ * ((2 : ℝ) ^ k))
        = C * ∑ k ∈ K, Real.exp (-cθ * ((2 : ℝ) ^ k)) := by
      simp [Finset.mul_sum]
    rw [this]
    have h_range_le_tsum := (h_summ : Summable fun k => Real.exp (-cθ * ((2 : ℝ) ^ k))).sum_le_tsum K (fun k _ => le_of_lt (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_left h_range_le_tsum hC_nonneg
  have final_bound : μ.real (⋃ k ∈ (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1),
      {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω ≥
          (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)})
    ≤ C * (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))) := by
    calc
      μ.real (⋃ k ∈ K, {ω | _}) ≤ ∑ k ∈ K, C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := hsum_bound
      _ ≤ C * (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))) := hsum_all
  have h_tsum_nonneg : 0 ≤ (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))) :=
    tsum_nonneg (fun k => le_of_lt (Real.exp_pos _))
  refine ⟨C * (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))), mul_nonneg hC_nonneg h_tsum_nonneg, final_bound⟩


theorem midblock_union_absorb_dep_const
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Smap : ℕ → Finset Ω)
  (P : SubGammaParam) (h1 : 0 < P.v) (h2 : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {k X' : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X') (Smap := Smap) ω
        - (∑ v ∈ MidBlock k X', (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ≤ midblockCstar P δ := by
  let K := Kset X
  let C0 := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let c0 := (P.lambda0 / 2) * δ
  have hC0_nonneg : 0 ≤ C0 := le_of_lt (Real.exp_pos _)
  have hc0_pos : 0 < c0 := mul_pos (by simpa using half_pos P.hlambda0) hδ
  have hterm : ∀ {k}, k ∈ K → μ.real (Emid (μ := μ) (Smap := Smap) δ k X) ≤ C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := by
    intro k hk
    have h2k_le : (2 : ℕ) ^ (k + 1) ≤ X + 1 := by simpa [K] using (Finset.mem_filter.mp hk).2
    have hcard_bound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h1 h2 h_sub (hδ := hδ)
    have h_card_nat := MidBlock_card_lower_when_2k_le_X k X h2k_le
    have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ (2 : ℝ) ^ k := by exact_mod_cast h_card_nat
    have mono : Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ))
        ≤ Real.exp (- c0 * ((2 : ℝ) ^ k)) := by
      have negc_nonpos : -((P.lambda0 / 2) * δ) ≤ 0 := le_of_lt (neg_lt_zero.mpr hc0_pos)
      have le_arg : -((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ) ≤ -((P.lambda0 / 2) * δ) * ((2 : ℝ) ^ k) :=
        mul_le_mul_of_nonpos_left h_card_real negc_nonpos
      exact Real.exp_le_exp.mpr le_arg
    calc
      μ.real (Emid (μ := μ) (Smap := Smap) δ k X) = μ.real {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)} := by rfl
      _ ≤ Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := hcard_bound
      _ = C0 * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by rfl
      _ ≤ C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := by apply mul_le_mul_of_nonneg_left mono hC0_nonneg
  have hboole := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) K (fun k => Emid (μ := μ) (Smap := Smap) δ k X)
  have sum_le : μ.real (⋃ k ∈ K, Emid (μ := μ) (Smap := Smap) δ k X) ≤ ∑ k ∈ K, C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := by
    calc
      μ.real (⋃ k ∈ K, Emid (μ := μ) (Smap := Smap) δ k X) ≤ ∑ k ∈ K, μ.real (Emid (μ := μ) (Smap := Smap) δ k X) := hboole
      _ ≤ ∑ k ∈ K, C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := Finset.sum_le_sum (fun k hk => hterm hk)
  have h_summ := Prob.summable_exp_neg_two_pow c0 hc0_pos
  have hsum_all : ∑ k ∈ K, C0 * Real.exp (- c0 * ((2 : ℝ) ^ k))
    ≤ C0 * (∑' k, Real.exp (- c0 * ((2 : ℝ) ^ k))) := by
    have : ∑ k ∈ K, C0 * Real.exp (-c0 * ((2 : ℝ) ^ k)) = C0 * ∑ k ∈ K, Real.exp (-c0 * ((2 : ℝ) ^ k)) := by simp [Finset.mul_sum]
    rw [this]
    have h_range_le_tsum := (h_summ : Summable fun k => Real.exp (-c0 * ((2 : ℝ) ^ k))).sum_le_tsum K (fun k _ => le_of_lt (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_left h_range_le_tsum hC0_nonneg
  calc
    μ.real (⋃ k ∈ K, Emid (μ := μ) (Smap := Smap) δ k X) ≤ ∑ k ∈ K, C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := sum_le
    _ ≤ C0 * (∑' k, Real.exp (- c0 * ((2 : ℝ) ^ k))) := hsum_all


lemma goodX_measure_ge_one_sub_midblockCstar
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) (P : SubGammaParam)
  (h1 : 0 < P.v) (h2 : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {k X' : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X') (Smap := Smap) ω
        - (∑ v ∈ MidBlock k X', (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  μ.real (GoodX (μ := μ) (Smap := Smap) δ X) ≥ 1 - midblockCstar P δ := by
  classical
  have hU :
    μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
      ≤ midblockCstar P δ :=
    Prob.midblock_union_absorb_dep_const (μ:=μ) (Smap := Smap) P h1 h2 (h_sub) hδ X
  have hcover :
    μ (Set.univ : Set Ω) ≤
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
  have := sub_le_iff_le_add'.mpr this
  have h_ge_goodx : μ.real (GoodX (μ := μ) (Smap := Smap) δ X)
      ≥ 1 - μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) := by
    linarith
  have h_one_sub : 1 - midblockCstar P δ ≤ 1 - μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) :=
    sub_le_sub_left hU (1 : ℝ)
  exact le_trans h_one_sub h_ge_goodx


end Prob

end DkMath.ABC
