/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBandJansonSkeleton
import DkMath.ABC.MiddleDyadicCompose

#print "file: DkMath.ABC.MiddleZmidBasic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleBlockTail.lean` から切り出した Zmid / mid-block finite-sum owner。
  `MidBlock` の cardinal lower bound, `Zmid`, `BadCountOnRV`,
  および `Prob.indR` finite-sum の可測性・可積分性を置く。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/--
If `2^(k+1) ≤ X+1`, then `MidBlock k X` contains the full dyadic interval
`[2^k, 2^(k+1)-1]`, hence has cardinality at least `2^k`.
-/
theorem MidBlock_card_lower_when_2k_le_X (k X : ℕ) (h : (2 : ℕ) ^ (k + 1) ≤ X + 1) :
  (MidBlock k X).card ≥ 2 ^ k := by
  have hle : (2:ℕ)^(k + 1) - 1 ≤ X := by
    have hpos : 0 < (2:ℕ)^(k + 1) := by apply Nat.pow_pos; norm_num
    have : (2:ℕ)^(k + 1) - 1 < (2:ℕ)^(k + 1) := Nat.pred_lt (Nat.pos_iff_ne_zero.mp hpos)
    have hlt := lt_of_lt_of_le this h
    exact Nat.le_pred_of_lt hlt
  have sub : Finset.Icc (2 ^ k) ((2:ℕ)^(k + 1) - 1) ⊆ MidBlock k X := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hL, hU⟩
    dsimp [MidBlock]
    apply Finset.mem_Icc.mpr
    constructor
    · exact hL
    · have h1 : n ≤ (2:ℕ)^(k + 1) - 1 := hU
      have h2 : (2:ℕ)^(k + 1) - 1 ≤ X := hle
      exact le_min h1 (le_trans h1 h2)
  have card_sub : (Finset.Icc (2 ^ k) ((2:ℕ)^(k + 1) - 1)).card ≤ (MidBlock k X).card := by
    exact Finset.card_le_card sub
  have img_sub : (Finset.range (2 ^ k)).image (fun i => 2 ^ k + i) ⊆ Finset.Icc (2 ^ k) ((2:ℕ)^(k + 1) - 1) := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨i, hi_range, rfl⟩
    have hi_lt : i < 2 ^ k := Finset.mem_range.1 hi_range
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · apply Nat.le_add_right
    · have hi_le : i ≤ 2 ^ k - 1 := Nat.le_pred_of_lt hi_lt
      have sum_le' : 2 ^ k + i ≤ 2 ^ k + (2 ^ k - 1) := by
        apply Nat.add_le_add_left; exact hi_le
      have one_le : 1 ≤ 2 ^ k := by
        have hpos : 0 < 2 ^ k := by apply Nat.pow_pos; norm_num
        exact Nat.succ_le_iff.mpr hpos
      have top_eq : 2 ^ k + (2 ^ k - 1) = (2:ℕ)^(k + 1) - 1 := by
        have hassoc := Nat.add_sub_assoc (by exact one_le) (2 ^ k)
        calc
          2 ^ k + (2 ^ k - 1) = (2 ^ k + 2 ^ k) - 1 := by rw [← hassoc]
          _ = 2 * 2 ^ k - 1 := by ring_nf
          _ = 2 ^ k * 2 - 1 := by rw [mul_comm]
          _ = (2:ℕ)^(k + 1) - 1 := by rw [pow_add, pow_one]
      calc
        2 ^ k + i ≤ 2 ^ k + (2 ^ k - 1) := by exact sum_le'
        _ = (2:ℕ)^(k + 1) - 1 := by rw [top_eq]
  have img_card_eq : ((Finset.range (2 ^ k)).image (fun i => 2 ^ k + i)).card = (Finset.range (2 ^ k)).card :=
    Finset.card_image_of_injective (Finset.range (2 ^ k)) fun a b h => by
      omega
  have range_card : (Finset.range (2 ^ k)).card = 2 ^ k := by simp [Finset.card_range]
  have le_icc : (Finset.range (2 ^ k)).card ≤ (Finset.Icc (2 ^ k) ((2:ℕ)^(k + 1) - 1)).card := by
    have img_card_le := Finset.card_le_card img_sub
    calc
      (Finset.range (2 ^ k)).card = ((Finset.range (2 ^ k)).image fun i => 2 ^ k + i).card := by rw [img_card_eq]
      _ ≤ (Finset.Icc (2 ^ k) ((2:ℕ)^(k + 1) - 1)).card := by exact img_card_le
  have two_le_mid : 2 ^ k ≤ (MidBlock k X).card := by
    calc
      2 ^ k = (Finset.range (2 ^ k)).card := by rw [range_card]
      _ ≤ (Finset.Icc (2 ^ k) ((2:ℕ)^(k + 1) - 1)).card := by exact le_icc
      _ ≤ (MidBlock k X).card := by exact card_sub
  exact two_le_mid

namespace Prob

/-- Alternative definition of the middle-band block bound that reuses α and the bound from `middleBandBlockBound`. -/
noncomputable def middleBandBlockBound_alt : BlockBound 0.435 :=
  { α := middleBandBlockBound.α,
    hα := middleBandBlockBound.hα,
    bound := fun ε hε => middleBandBlockBound.bound ε hε }

/-- AE bound: `Z = sum indR ∈ [0, card]` a.e. -/
lemma mid_block_sum_ae_bounds {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (k X : ℕ) (Smap : ℕ → Finset Ω) :
  ∀ᵐ ω ∂μ,
    0 ≤ (Finset.sum (MidBlock k X) (fun v => Prob.indR (Smap v)) ω)
    ∧ (Finset.sum (MidBlock k X) (fun v => Prob.indR (Smap v)) ω)
        ≤ (MidBlock k X).card := by
  have pointwise : ∀ ω, 0 ≤ (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v)) ω ∧
    (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v)) ω ≤ (MidBlock k X).card := by
    intro ω
    let s := MidBlock k X
    have hsum_nonneg : 0 ≤ (Finset.sum s fun v => Prob.indR (Smap v)) ω := by
      have : (Finset.sum s fun v => Prob.indR (Smap v)) ω = Finset.sum s fun v => Prob.indR (Smap v) ω := by simp [Finset.sum_apply]
      rw [this]; apply Finset.sum_nonneg; intro v hv; exact (indR_range01 (S := Smap v) ω).1
    have hsum_le_raw : (Finset.sum s fun v => Prob.indR (Smap v)) ω ≤ s.card • (1 : ℝ) := by
      have : (Finset.sum s fun v => Prob.indR (Smap v)) ω = Finset.sum s fun v => Prob.indR (Smap v) ω := by simp [Finset.sum_apply]
      rw [this]; apply Finset.sum_le_card_nsmul; intros v hv; exact (indR_range01 (S := Smap v) ω).2
    have hsum_le : (Finset.sum s fun v => Prob.indR (Smap v)) ω ≤ (s.card : ℝ) := by
      simpa [nsmul_eq_mul, mul_one] using hsum_le_raw
    exact And.intro hsum_nonneg hsum_le
  exact MeasureTheory.ae_of_all μ pointwise

/-- AE bound: duplicate historical form retained for compatibility. -/
lemma mid_block_sum_ae_bounds' {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (k X : ℕ) (Smap : ℕ → Finset Ω) :
  ∀ᵐ ω ∂μ,
    0 ≤ (Finset.sum (MidBlock k X) (fun v => Prob.indR (Smap v)) ω)
    ∧ (Finset.sum (MidBlock k X) (fun v => Prob.indR (Smap v)) ω)
        ≤ (MidBlock k X).card := by
  have pointwise : ∀ a, (0 ≤ Finset.sum (MidBlock k X) (fun v => Prob.indR (Smap v)) a)
    ∧ (Finset.sum (MidBlock k X) (fun v => Prob.indR (Smap v)) a ≤ ((MidBlock k X).card : ℝ)) := by
    intro a
    have hnonneg : ∀ v ∈ MidBlock k X, 0 ≤ Prob.indR (Smap v) a := by
      intro v hv; exact (indR_range01 (S := Smap v) a).1
    have hsum_nonneg := Finset.sum_nonneg fun v hv => hnonneg v hv
    have hsum_nonneg' : 0 ≤ Finset.sum (MidBlock k X) (fun v => Prob.indR (Smap v)) a := by
      simpa [Finset.sum_apply] using hsum_nonneg
    have hsum_le := Finset.sum_le_card_nsmul (MidBlock k X) (fun v => Prob.indR (Smap v) a) (1 : ℝ)
      fun v hv => (indR_range01 (S := Smap v) a).2
    have hsum_le' : Finset.sum (MidBlock k X) (fun v => Prob.indR (Smap v)) a ≤ ((MidBlock k X).card : ℝ) := by
      simpa [MulOneClass.mul_one, Nat.cast_mul] using hsum_le
    exact ⟨hsum_nonneg', hsum_le'⟩
  exact MeasureTheory.ae_of_all μ pointwise

/-- The finite mid-block sum of indicators is a.e. strongly measurable. -/
theorem mid_block_sum_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) (k X : ℕ) (Smap : ℕ → Finset Ω) :
  AEStronglyMeasurable (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v)) μ := by
  let s := MidBlock k X
  have h := Finset.aestronglyMeasurable_sum s fun v hv =>
    Prob.indR_aestronglyMeasurable (μ := μ) (S := Smap v)
  change AEStronglyMeasurable (Finset.sum s fun v => Prob.indR (Smap v)) μ
  exact h

/-- The finite mid-block sum of indicators is integrable on a probability space. -/
theorem mid_block_sum_integrable {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (k X : ℕ)
  (Smap : ℕ → Finset Ω) :
  Integrable (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v)) μ := by
  let s := (MidBlock k X)
  have H : ∀ v ∈ s, Integrable (fun ω => Prob.indR (Smap v) ω) μ := by
    intro v hv
    have hbound : ∀ᵐ ω ∂μ, 0 ≤ Prob.indR (Smap v) ω ∧ Prob.indR (Smap v) ω ≤ 1 :=
      Prob.indR_range01_ae_of_all (μ := μ) (S := Smap v)
    have hmeas := (Prob.indR_aestronglyMeasurable (μ := μ) (S := Smap v)).aemeasurable
    exact Integrable.of_mem_Icc 0 1 hmeas hbound
  exact integrable_finset_sum' s fun v hv => H v hv

/-- Definition: `Zmid` is the mid-block indicator sum. -/
noncomputable def Zmid {Ω : Type*} [DecidableEq Ω] {k X : ℕ} (Smap : ℕ → Finset Ω) : Ω → ℝ :=
  fun ω => Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω

/-- RV version of the bad-count: expose `Zmid` as a named random variable. -/
noncomputable def BadCountOnRV {Ω : Type*} [DecidableEq Ω] {k X : ℕ} (Smap : ℕ → Finset Ω) : Ω → ℝ :=
  Zmid (k := k) (X := X) (Smap := Smap)

/-- Integrability of `exp(lambda * Zmid)` by domination on a probability space. -/
lemma integrable_exp_of_mid_block {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (k X : ℕ) (Smap : ℕ → Finset Ω) (lambda : ℝ) :
  Integrable (fun ω => Real.exp (lambda * (Finset.sum (MidBlock k X) (fun v => Prob.indR (Smap v) ω)))) μ := by
  have ae_bound := mid_block_sum_ae_bounds (μ := μ) (k := k) (X := X) (Smap := Smap)
  have hexp_le :
      (fun ω => Real.exp (lambda * (∑ v ∈ MidBlock k X, Prob.indR (Smap v) ω)))
        ≤ᵐ[μ] fun _ => Real.exp (|lambda| * (MidBlock k X).card) := by
    filter_upwards [ae_bound] with ω h
    · have hpos : 0 ≤ (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω) := by simpa [Finset.sum_apply] using h.1
      have hle_card : (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω) ≤ (MidBlock k X).card := by simpa [Finset.sum_apply] using h.2
      have hmul_le : lambda * (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω) ≤ |lambda| * (MidBlock k X).card := by
        calc
          lambda * (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω) ≤ |lambda| * (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω) := by
            exact mul_le_mul_of_nonneg_right (le_abs_self lambda) hpos
          _ ≤ |lambda| * (MidBlock k X).card := by
            exact mul_le_mul_of_nonneg_left hle_card (abs_nonneg lambda)
      exact Real.exp_le_exp.mpr hmul_le
  have hconst : Integrable (fun _ => Real.exp (|lambda| * (MidBlock k X).card)) μ := by
    haveI : IsFiniteMeasure μ := inferInstance
    apply integrable_const
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (lambda * (∑ v ∈ MidBlock k X, Prob.indR (Smap v) ω))) μ := by
    let hsum := mid_block_sum_aestronglyMeasurable (μ := μ) (k := k) (X := X) (Smap := Smap)
    let hsum_mul := AEStronglyMeasurable.const_mul hsum lambda
    have h_aemeas : AEMeasurable (fun x => lambda * ∑ v ∈ MidBlock k X, Prob.indR (Smap v) x) μ := by
      simpa [Finset.sum_apply] using hsum_mul.aemeasurable
    have h_exp_aemeas : AEMeasurable (fun ω => Real.exp (lambda * (∑ v ∈ MidBlock k X, Prob.indR (Smap v) ω))) μ :=
      measurable_exp.comp_aemeasurable h_aemeas
    exact AEMeasurable.aestronglyMeasurable h_exp_aemeas
  have hnorm_le : ∀ᵐ ω ∂μ,
      ‖Real.exp (lambda * (∑ v ∈ MidBlock k X, Prob.indR (Smap v) ω))‖
        ≤ Real.exp (|lambda| * (MidBlock k X).card) := by
    filter_upwards [hexp_le] with ω h
    simpa [norm_eq_abs, abs_exp] using h
  exact hconst.mono' hmeas hnorm_le

/-- `BadCountOnRV` and `Zmid` coincide for the given `Smap`, `k`, and `X`. -/
lemma BadCountOnRV_eq_Zmid {Ω : Type*} [DecidableEq Ω] {k X : ℕ} (Smap : ℕ → Finset Ω) :
  BadCountOnRV (k := k) (X := X) Smap = Zmid (k := k) (X := X) (Smap := Smap) := rfl

end Prob

end DkMath.ABC
