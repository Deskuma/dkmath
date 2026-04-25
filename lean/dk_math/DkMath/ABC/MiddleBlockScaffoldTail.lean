/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBlockDepAbsorption

#print "file: DkMath.ABC.MiddleBlockScaffoldTail"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleBlockTail.lean` から切り出した scaffold / independent wrapper owner。
  旧 ABC010 relay に残っていた witness scaffold と expectation helper を置く。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob


/-- There exist k0, C, A (with A>0, C≥0) such that for X ≥ 2^k and k ≥ k0 the BadCountOn 0.435 (MidBlock k X) is bounded by C * (2^k)^(A + ε). -/
lemma mid_block_chernoff_tail (ε : ℝ) (hε : 0 < ε) :
  ∃ (k0 : ℕ) (C : ℝ) (A : ℝ),
    0 < A ∧ 0 ≤ C ∧
    (∀ ⦃X k : ℕ⦄, X ≥ (2 : ℕ) ^ k → k ≥ k0 →
      (↑(BadCountOn 0.435 (MidBlock k X)) : ℝ) ≤ C * ((2 : ℕ) ^ k : ℝ) ^ (A + ε)) := by
  have h := middleBandBlockBound.bound ε hε
  obtain ⟨k0, C, hC_nonneg, hb⟩ := h
  let A := middleBandBlockBound.α
  have hApos : 0 < A := middleBandBlockBound.hα
  refine ⟨k0, C, A, hApos, hC_nonneg, ?_⟩
  intro X k hX hk_ge
  exact hb hX hk_ge


/-- If p v ≤ q for all v ∈ S and q ≠ ⊤, then ∑ v in S, (p v).toReal ≤ S.card • q.toReal. -/
lemma badcount_by_expect
  {Γ : Type*}
  (S : Finset Γ) (p : Γ → ENNReal) (q : ENNReal) (hq : q ≠ ⊤)
  (h : ∀ v ∈ S, p v ≤ q) :
  (∑ v ∈ S, (p v).toReal) ≤ S.card • q.toReal := by
  have hterm : ∀ v ∈ S, (p v).toReal ≤ q.toReal := by
    intro v hv
    apply ENNReal.toReal_mono hq (h v hv)
  exact Finset.sum_le_card_nsmul S (fun v => (p v).toReal) q.toReal hterm


/-- Existence of k0, C, A (A>0, C≥0) giving a polynomial tail bound in 2^k for the normalized BadCountOn on mid blocks under the given independence assumption. -/
theorem mid_block_chernoff_tail_indep
  (ε : ℝ) (hε : 0 < ε)
  {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  [MeasureSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (_hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ) :
  ∃ (k0 : ℕ) (C : ℝ) (A : ℝ), 0 < A ∧ 0 ≤ C ∧
    (∀ ⦃X k : ℕ⦄, X ≥ (2 : ℕ) ^ k → k ≥ k0 →
      (↑(BadCountOn 0.49 (MidBlock k X)) : ℝ) ≤ C * ((2 : ℕ) ^ k : ℝ) ^ (A + ε)) := by
  have h := middleBandBlockBound.bound ε hε
  obtain ⟨k0, C, hC_nonneg, hb⟩ := h
  let A := middleBandBlockBound.α
  have hApos : 0 < A := middleBandBlockBound.hα
  use k0, C, A
  constructor
  · exact hApos
  constructor
  · exact hC_nonneg
  intro X k hX hk_ge
  have Hmgf : QuadMGF (μ := μ) (Zmid (k := k) (X := X) (Smap := Smap))
    (Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ))
    ((↑(Finset.card (MidBlock k X)) / 8) + 1) := by
    exact mgf_midblock_via_indep (μ := μ) (Smap := Smap) (_hind)
  let card := (Finset.card (MidBlock k X) : ℝ)
  have hcard_nonneg : 0 ≤ card := by exact Nat.cast_nonneg _
  have hτ_pos : 0 ≤ Real.sqrt card := by
    exact Real.sqrt_nonneg card
  let τ := Real.sqrt card
  have chernoff_bound := mid_block_chernoff_fixed (μ := μ) (Smap := Smap) (H := Hmgf) (hτ := hτ_pos)
  have h_tau_sq : τ ^ 2 = card := by dsimp [τ]; exact Real.sq_sqrt hcard_nonneg
  have _tail_exp_bound : μ.real {ω | Zmid (k := k) (X := X) (Smap := Smap) ω ≤
      (Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ)) - τ }
      ≤ Real.exp ( - (τ ^ 2) / (4 * ((card / 8) + 1)) ) := by
    exact chernoff_bound
  have _hE : (∫ ω, Zmid (k := k) (X := X) (Smap := Smap) ω ∂μ) = (∑ v ∈ MidBlock k X, (μ ↑(Smap v)).toReal) := by
    exact EZmid_eq_sum_probs (μ := μ) (Smap := Smap)
  exact hb (by assumption) (by assumption)


/-- Independent scaffold: finite union bound with a trivial X-dependent prefactor. -/
lemma union_over_k_midblock_bound_indep
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (_hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ)
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
  let cθ := δ / 4
  let C := Real.exp (cθ * ((2 : ℝ) ^ X))
  have hC : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hcθ : 0 < cθ := by exact div_pos hδ (by norm_num)
  refine ⟨C, cθ, hC, hcθ, ?_⟩
  intro K E
  have hboole := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) K E
  have hterm : ∀ {k}, k ∈ K → μ.real (E k) ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
    intro k hk
    have k_le : k ≤ X := by
      have mem := (Finset.mem_filter.mp hk).1
      have k_lt : k < X + 1 := Finset.mem_range.mp mem
      exact Nat.lt_succ_iff.mp k_lt
    have pow_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ X := by
      have nat_pow_le := Nat.pow_le_pow_of_le (by norm_num : 2 ≤ 2) k_le
      exact_mod_cast nat_pow_le
    have diff_nonneg : 0 ≤ cθ * ((2 : ℝ) ^ X - (2 : ℝ) ^ k) := by
      apply mul_nonneg
      · exact le_of_lt hcθ
      · exact sub_nonneg.mpr pow_le
    have one_le_rhs : 1 ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
      calc
        C * Real.exp (- cθ * ((2 : ℝ) ^ k)) = Real.exp (cθ * (2 ^ X)) * Real.exp (- cθ * (2 ^ k)) := by rfl
        _ = Real.exp (cθ * (2 ^ X) + -cθ * (2 ^ k)) := by rw [Real.exp_add]
        _ = Real.exp (cθ * ((2 : ℝ) ^ X - (2 : ℝ) ^ k)) := by ring_nf
        _ ≥ Real.exp 0 := by apply Real.exp_le_exp.mpr; exact diff_nonneg
        _ = 1 := by simp
    have μE_le_univ : μ (E k) ≤ μ (Set.univ : Set Ω) := MeasureTheory.measure_mono (μ := μ) (Set.subset_univ (E k))
    have μuniv_ne_top : μ (Set.univ : Set Ω) ≠ ⊤ := by simp [IsProbabilityMeasure.measure_univ]
    have toreal_m := ENNReal.toReal_mono μuniv_ne_top μE_le_univ
    have prob_le_one : μ.real (E k) ≤ 1 := by
      calc
        μ.real (E k) = (μ (E k)).toReal := rfl
        _ ≤ (μ (Set.univ : Set Ω)).toReal := toreal_m
        _ = 1 := by simp [IsProbabilityMeasure.measure_univ]
    exact le_trans prob_le_one one_le_rhs
  exact le_trans hboole (Finset.sum_le_sum (by intro k hk; exact hterm hk))


/-- Zmid の期待値を、各頂点確率の一様上界から `|MidBlock| • q.toReal` で抑える補題。 -/
lemma EZmid_expect_le_card_smul_q
  {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (q : ENNReal) (hq : q ≠ ⊤)
  (h : ∀ v ∈ MidBlock k X, μ ↑(Smap v) ≤ q) :
    (∫ ω, Zmid (k := k) (X := X) (Smap := Smap) ω ∂μ)
    ≤ (Finset.card (MidBlock k X) : ℕ) • q.toReal := by
  have hEZ := EZmid_eq_sum_probs (μ := μ) (Smap := Smap) (k := k) (X := X)
  rw [hEZ]
  exact badcount_by_expect (S := MidBlock k X) (p := fun v => μ ↑(Smap v)) (q := q) hq (fun v hv => h v hv)


end Prob

end DkMath.ABC
