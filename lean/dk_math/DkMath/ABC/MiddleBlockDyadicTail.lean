/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBlockEvents

#print "file: DkMath.ABC.MiddleBlockDyadicTail"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleBlockTail.lean` から切り出した dyadic tail owner。
  `2^k` への指数吸収、`exp(-c * 2^k)` の可和性、
  依存版 mid-block dyadic tail の受け口を置く。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob


/-- `|MidBlock k X| ≥ c0·2^k` があるとき，指数を `2^k` に吸わせる受け口。 -/
theorem mid_block_upper_hp_dep_twoPow_exists
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
         - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ)
  (c0 : ℝ) (hc0 : 0 < c0)
  (h_card : (Finset.card (MidBlock k X) : ℝ) ≥ c0 * ((2 : ℝ) ^ k)) :
  ∃ (C cθ : ℝ), 0 ≤ C ∧ 0 < cθ ∧
    μ.real {ω |
      Zmid (k := k) (X := X) (Smap := Smap) ω
        ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
          + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
  obtain ⟨C, c, hC_nonneg, hc_pos, hbound⟩ :=
    mid_block_upper_hp_dep_expCard_exists (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one h_sub (hδ := hδ)
  let cθ := c * c0
  have hcθ_pos : 0 < cθ := mul_pos hc_pos hc0
  have mono :
      Real.exp (- c * (Finset.card (MidBlock k X) : ℝ))
        ≤ Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
    have negc_nonpos : -c ≤ 0 := le_of_lt (neg_lt_zero.mpr hc_pos)
    have h_card_le : c0 * ((2 : ℝ) ^ k) ≤ (Finset.card (MidBlock k X) : ℝ) :=
      (ge_iff_le.mp h_card)
    have le_arg :
        - c * (Finset.card (MidBlock k X) : ℝ)
          ≤ - c * (c0 * ((2 : ℝ) ^ k)) :=
      mul_le_mul_of_nonpos_left h_card_le negc_nonpos
    have : - c * (c0 * ((2 : ℝ) ^ k)) = - (c * c0) * ((2 : ℝ) ^ k) := by ring
    simpa [cθ, this] using Real.exp_le_exp.mpr le_arg
  refine ⟨C, cθ, hC_nonneg, hcθ_pos, ?_⟩
  exact
    (le_trans hbound
      (mul_le_mul_of_nonneg_left mono hC_nonneg))


/-- `2^(k+1) ≤ X+1` のとき，mid-block 上側尾を `C · exp( - cθ · 2^k )` へ。 -/
theorem mid_block_upper_hp_dep_twoPow_exists_of_2k_le_X
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
         - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ)
  (hX : (2 : ℕ) ^ (k + 1) ≤ X + 1) :
  ∃ (C cθ : ℝ), 0 ≤ C ∧ 0 < cθ ∧
    μ.real {ω |
      Zmid (k := k) (X := X) (Smap := Smap) ω
        ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
          + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤ C * Real.exp ( - cθ * ((2 : ℝ) ^ k) ) := by
  have h_card_nat : (MidBlock k X).card ≥ 2 ^ k :=
    MidBlock_card_lower_when_2k_le_X k X hX
  have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ 1 * ((2 : ℝ) ^ k) := by
    have : (Finset.card (MidBlock k X) : ℝ) ≥ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h_card_nat
    simpa [one_mul, Nat.cast_pow, Nat.cast_ofNat] using this
  exact
    mid_block_upper_hp_dep_twoPow_exists (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one h_sub hδ
      (c0 := 1) (hc0 := by norm_num) (h_card := by simpa [one_mul] using h_card_real)


/-- `a_{k+1} = exp(-θ·2^{k+1}) ≤ exp(-θ) * exp(-θ·2^k)` を示す補助。 -/
lemma exp_neg_two_pow_ratio_le
  (theta : ℝ) (hθ : 0 < theta) :
  ∀ k : ℕ,
    Real.exp (-theta * ((2 : ℝ) ^ (k + 1)))
      ≤ Real.exp (-theta) * Real.exp (-theta * ((2 : ℝ) ^ k)) := by
  intro k
  have : ((2 : ℝ) ^ (k + 1)) = (2 : ℝ) ^ k * 2 := by simp [pow_succ]
  have eq : -theta * ((2 : ℝ) ^ (k + 1)) = (-theta * ((2 : ℝ) ^ k)) + (-theta * ((2 : ℝ) ^ k)) := by
    simp [this]; ring
  calc
    Real.exp (-theta * ((2 : ℝ) ^ (k + 1))) = Real.exp ((-theta * ((2 : ℝ) ^ k)) + (-theta * ((2 : ℝ) ^ k))) := by simp [eq, Real.exp_add]
    _ = Real.exp (-theta * ((2 : ℝ) ^ k)) * Real.exp (-theta * ((2 : ℝ) ^ k)) := by simp [Real.exp_add]
    _ ≤ Real.exp (-theta * ((2 : ℝ) ^ k)) * Real.exp (-theta) := by
      have one_le_pow : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
        have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
        exact_mod_cast this
      have mul_le : -theta * ((2 : ℝ) ^ k) ≤ -theta := by
        have hpow : ((2 : ℝ) ^ k) ≥ 1 := by simpa using one_le_pow
        calc
          -theta * ((2 : ℝ) ^ k) ≤ -theta * 1 := by
            apply mul_le_mul_of_nonpos_left
            · simpa using hpow
            · exact le_of_lt (neg_lt_zero.mpr hθ)
          _ = -theta := by simp
      have exp_le := Real.exp_le_exp.mpr (by simpa [mul_le])
      exact mul_le_mul_of_nonneg_left exp_le (Real.exp_nonneg _)
    _ = Real.exp (-theta) * Real.exp (-theta * ((2 : ℝ) ^ k)) := by ring


/-- 反復で `exp(-θ·2^k) ≤ (exp(-θ))^(k+1)` を得る。 -/
lemma exp_neg_two_pow_le_geom (theta : ℝ) (hθ : 0 < theta) :
  ∀ k : ℕ, Real.exp (-theta * ((2 : ℝ) ^ k)) ≤ (Real.exp (-theta)) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have step := exp_neg_two_pow_ratio_le theta hθ k
    have mul_bound : Real.exp (-theta) * Real.exp (-theta * ((2 : ℝ) ^ k)) ≤ Real.exp (-theta) * (Real.exp (-theta) ^ (k + 1)) := by
      apply mul_le_mul_of_nonneg_left
      · exact ih
      · exact le_of_lt (Real.exp_pos _)
    calc
      Real.exp (-theta * ((2 : ℝ) ^ (k + 1))) ≤ Real.exp (-theta) * Real.exp (-theta * ((2 : ℝ) ^ k)) := step
      _ ≤ Real.exp (-theta) * (Real.exp (-theta) ^ (k + 1)) := mul_bound
      _ = (Real.exp (-theta)) ^ ((k + 1) + 1) := by ring


/-- `∑ exp(-c · 2^k)` は収束する（`c>0`）。 -/
lemma summable_exp_neg_two_pow (c : ℝ) (hc : 0 < c) :
  Summable (fun k : ℕ => Real.exp (- c * ((2 : ℝ) ^ k))) := by
  have major := exp_neg_two_pow_le_geom c hc
  have rpos : 0 < Real.exp (-c) := Real.exp_pos _
  have rlt1 : Real.exp (-c) < 1 := by
    have : -c < 0 := neg_lt_zero.mpr hc
    simpa using Real.exp_lt_one_iff.mpr this
  have geom : Summable (fun k => (Real.exp (-c)) ^ (k + 1)) := by
    let r := Real.exp (-c)
    have h : Summable (fun n => r ^ n) := summable_geometric_of_lt_one (le_of_lt rpos) rlt1
    have shifted : Summable (fun n => r * (r ^ n)) := h.mul_left r
    have eq_fun : (fun n => r ^ (n + 1)) = fun n => r * r ^ n := by
      funext n
      simp only [pow_succ]
      rw [mul_comm]
    exact eq_fun ▸ shifted
  refine Summable.of_nonneg_of_le (fun _ => Real.exp_nonneg _) (fun k => ?_) geom
  simpa using major k


/-- card(MidBlock) に基づく存在形を dyadic (2^k) 指数に落とす補題。 -/
lemma midblock_tail_dep_dyadic
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {k X : ℕ} (Smap : ℕ → Finset Ω)
  (P : SubGammaParam) (h1 : 0 < P.v) (h2 : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
        - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  (h2k_le : (2 : ℕ) ^ (k + 1) ≤ X + 1)
  {δ : ℝ} (hδ : 0 < δ) :
  ∃ C c, 0 ≤ C ∧ 0 < c ∧
  μ.real {ω |
  Zmid (k := k) (X := X) (Smap := Smap) ω ≥
    (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤ C * Real.exp (- c * ((2 : ℝ) ^ k)) := by
  let C := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let c := P.lambda0 / 2 * δ
  have hC_nonneg : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hc_pos : 0 < c := mul_pos (by simpa using half_pos P.hlambda0) hδ
  have hbound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
    P h1 h2 (h_sub) (hδ := hδ)
  have h_card_nat := MidBlock_card_lower_when_2k_le_X k X h2k_le
  have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ (2 : ℝ) ^ k := by exact_mod_cast h_card_nat
  have mono : Real.exp (-(P.lambda0 / 2 * δ) * (Finset.card (MidBlock k X) : ℝ))
      ≤ Real.exp (-(P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k)) := by
    have negc_nonpos : -(P.lambda0 / 2 * δ) ≤ 0 := le_of_lt (neg_lt_zero.mpr (by simpa using mul_pos (by simpa using half_pos P.hlambda0) hδ))
    have le_arg : -(P.lambda0 / 2 * δ) * (Finset.card (MidBlock k X) : ℝ) ≤ -(P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k) :=
      mul_le_mul_of_nonpos_left h_card_real negc_nonpos
    exact Real.exp_le_exp.mpr le_arg
  refine ⟨C, c, hC_nonneg, hc_pos, ?_⟩
  have hpost := mul_le_mul_of_nonneg_left mono hC_nonneg
  have hR := le_trans hbound hpost
  have rhs_eq : Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * Real.exp (-(P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k))
      = C * Real.exp (- c * ((2 : ℝ) ^ k)) := by
    simp [C, c]
  rw [rhs_eq] at hR
  exact hR


end Prob

end DkMath.ABC
