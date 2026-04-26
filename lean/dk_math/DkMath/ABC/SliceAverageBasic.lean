/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.RatioBound

#print "file: DkMath.ABC.SliceAverageBasic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `SliceDiagonalCounting.lean` から切り出した slice-average / Markov owner。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-
slice_average_bound: average化 → 大多数のスライスが小さい（Markov 的引数）
ここではまず有限スライス上の簡潔な不等式を Lean 化する。後続で `eventually_badcount_le_eps`
を組み合わせれば `∀ᶠ b, sliceBadCount δ X b ≤ η * X` の形に持ち込める。
-/

/-- η以上のsliceBadCountを持つbの個数は、BadCount δ X / (η * (X + 1)) 以下であることを示す補題 -/
lemma slice_heavy_card_le {δ : ℝ} (η : ℝ) (hη : 0 < η) (X : ℕ) :
  ((Finset.range (X+1)).filter fun b => ((sliceBadCount (δ := δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ))).card ≤
    (BadCount δ X : ℝ) / (η * ((X + 1 : ℕ) : ℝ)) := by
  -- convert counting inequality to numeric bound: each heavy slice contributes at least η*(X+1) to the sum
  let S := (Finset.range (X+1)).filter fun b => ((sliceBadCount (δ := δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ))
  -- each element of S has value ≥ η * (X+1)
  have hge : ∀ b ∈ S, (sliceBadCount (δ := δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ) := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  -- sum over S ≥ S.card * η * (X+1)
  have hsumS : (∑ b ∈ S, (sliceBadCount (δ := δ) X b : ℝ)) ≥ (S.card : ℝ) * (η * ((X + 1 : ℕ) : ℝ)) := by
    have eq : (S.card : ℝ) * (η * ((X + 1 : ℕ) : ℝ)) = (∑ b ∈ S, η * ((X + 1 : ℕ) : ℝ)) := by
      simp [Finset.sum_const, mul_comm]
    rw [eq]
    apply Finset.sum_le_sum (by intro b hb; exact hge b hb)
  -- extend S-sum to full range using nonnegativity of sliceBadCount
  have hnonneg : ∀ b, 0 ≤ (sliceBadCount (δ := δ) X b : ℝ) := by intro b; exact Nat.cast_nonneg _
  have hfull : (∑ b ∈ S, (sliceBadCount (δ := δ) X b : ℝ)) ≤ (∑ b ∈ Finset.range (X+1), (sliceBadCount (δ := δ) X b : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b hb _ => hnonneg b)
  have hsum : (S.card : ℝ) * (η * ((X + 1 : ℕ) : ℝ)) ≤ (∑ b ∈ Finset.range (X+1), (sliceBadCount (δ := δ) X b : ℝ)) :=
    le_trans hsumS hfull
  -- now use slice_sum_le_badcount to bound the RHS by BadCount (cast to ℝ)
  have hbad_sum : (∑ b ∈ Finset.range (X+1), (sliceBadCount (δ := δ) X b : ℝ)) ≤ (BadCount δ X : ℝ) :=
    by exact_mod_cast (slice_sum_le_badcount (δ := δ) X)
  have mul_le : (S.card : ℝ) * (η * ((X + 1 : ℕ) : ℝ)) ≤ (BadCount δ X : ℝ) := by linarith [hsum, hbad_sum]
  -- divide by η * (X+1) > 0
  have hXpos : 0 < ((X + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ X
  have hpos : 0 < η * ((X + 1 : ℕ) : ℝ) := mul_pos hη hXpos
  exact (le_div_iff₀ hpos).mpr mul_le

/-- Eventualization of the slice-average Markov bound.
Given δ and positive η, ε', eventually (for large X) the number of heavy slices
with sliceBadCount ≥ η*(X+1) is at most (ε'/η) * X. This combines the finite
`slice_heavy_card_le` with `eventually_badcount_le_eps` (for δ = 0.435 or general δ
when an appropriate eventually_badcount lemma is available).
-/
theorem eventually_slice_heavy_sublinear
  {δ : ℝ} (hδ_eq : δ = 0.435)
  (η ε' : ℝ) (hη : 0 < η) (hε' : 0 < ε') :
  ∀ᶠ X in atTop,
    ((Finset.range (X+1)).filter
      (fun b => (sliceBadCount (δ:=δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ))).card
      ≤ (ε' / η) * (X : ℝ) := by
  -- BadCount ≤ ε' X^2 eventually（既存）
  have hBC := eventually_badcount_le_eps (hδ := hδ_eq) (η := ε') hε'
  -- X≥1 eventually
  have ev1 := (Filter.eventually_atTop.2 ⟨1, by intro k hk; exact hk⟩)
  refine (ev1.and hBC).mono ?_
  intro X ⟨_, hBadLe⟩
  -- 有限版 Markov：|heavy| ≤ BadCount / (η (X+1))
  have h_fin := slice_heavy_card_le (δ:=δ) (η:=η) (hη:=hη) (X:=X)
  -- 右辺を ε' で上から挟む
  have hposX1 : 0 < ((X + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos X
  have denom_pos : 0 < η * ((X + 1 : ℕ) : ℝ) := mul_pos hη hposX1
  have step1 :
    (BadCount δ X : ℝ) / (η * ((X + 1 : ℕ) : ℝ))
      ≤ (ε' * (X : ℝ)^2) / (η * ((X + 1 : ℕ) : ℝ)) :=
    (div_le_div_of_nonneg_right hBadLe (le_of_lt denom_pos))
  -- さらに (X^2)/(X+1) ≤ X
  have x2_over_x1_le_x :
    ((X : ℝ)^2) / ((X + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
    have hX1pos : 0 < ((X + 1 : ℕ) : ℝ) := hposX1
    -- rewrite (X^2)/(X+1) = X - X/(X+1)
    have hne : ((X + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero X)
    have eq : ((X : ℝ) ^ 2) / ((X + 1 : ℕ) : ℝ) = (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by
      calc
        ((X : ℝ) ^ 2) / ((X + 1 : ℕ) : ℝ)
          = ((X : ℝ) * ((X + 1 : ℕ) : ℝ) - (X : ℝ)) / ((X + 1 : ℕ) : ℝ) := by
            have rfl_cast : ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 := by simp [Nat.cast_add, Nat.cast_one]
            rw [rfl_cast]; simp [pow_two, mul_add]
        _ = (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by field_simp [hne]
    rw [eq]
    -- X/(X+1) ≥ 0, so X - X/(X+1) ≤ X
    have nonneg_div : 0 ≤ (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by
      apply div_nonneg
      · exact_mod_cast Nat.zero_le X
      · exact le_of_lt hX1pos
    linarith
  -- まとめ
  have step2 :
    (ε' * (X : ℝ)^2) / (η * ((X + 1 : ℕ) : ℝ))
      ≤ (ε' / η) * (X : ℝ) := by
    have coef_nonneg : 0 ≤ ε' / η := div_nonneg (le_of_lt hε') (le_of_lt hη)
    have eq : (ε' * (X : ℝ)^2) / (η * ((X + 1 : ℕ) : ℝ))
         = (ε'/η) * (((X : ℝ)^2) / ((X + 1 : ℕ) : ℝ)) := by
      have hη0 : (η:ℝ) ≠ 0 := ne_of_gt hη
      have hX0 : ((X + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hposX1
      field_simp [hη0, hX0, mul_comm, mul_left_comm, mul_assoc]
    rw [eq]
    exact mul_le_mul_of_nonneg_left x2_over_x1_le_x coef_nonneg
  exact (le_trans h_fin (le_trans step1 step2))

/-- If the total bad count is subquadratic, then for any ε' > 0, the number of slices with bad count at least η times the slice size is sublinear in X. -/
lemma eventually_slice_heavy_sublinear_of_badcount_subquad
  {δ η : ℝ} (hη : 0 < η)
  (hTot : ∀ ε'' > 0, ∀ᶠ X in atTop, (BadCount δ X : ℝ) ≤ ε'' * (X : ℝ) ^ 2) :
  ∀ ε' > 0, ∀ᶠ X in atTop,
  ((Finset.range (X+1)).filter (fun b =>
    (sliceBadCount (δ:=δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ))).card
      ≤ (ε' / η) * (X : ℝ) := by
  intro ε' hε'
  -- apply hTot with ε' to bound BadCount by ε' * X^2 eventually
  have hBC := hTot ε' (by linarith)
  have eventual_bound := hBC.mono fun X hbad => by
    have h_fin := slice_heavy_card_le (δ := δ) (η := η) (hη := hη) (X := X)
    -- h_fin : card ≤ BadCount / (η*(X+1)); combine with hbad: BadCount ≤ ε'*X^2
    have hpos_denom : 0 < η * ((X + 1 : ℕ) : ℝ) := by
      have hXpos : 0 < ((X + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ X
      exact mul_pos hη hXpos
    have h_div := div_le_div_of_nonneg_right hbad (le_of_lt hpos_denom)
    have heavy_le : ((Finset.range (X+1)).filter fun b => (sliceBadCount (δ:=δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ)).card
        ≤ (ε' * (X : ℝ) ^ 2) / (η * ((X + 1 : ℕ) : ℝ)) := by
      exact le_trans h_fin h_div
    -- since (X : ℝ)^2 / (X+1) ≤ X for X ≥ 0, we get desired bound by algebra
    have hne : ((X + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero X)
    have eq_div : (X : ℝ) ^ 2 / ((X + 1 : ℕ) : ℝ) = (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by
      calc
        (X : ℝ) ^ 2 / ((X + 1 : ℕ) : ℝ) = ((X : ℝ) * ((X + 1 : ℕ) : ℝ) - (X : ℝ)) / ((X + 1 : ℕ) : ℝ) := by
          have rfl_cast : ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 := by simp [Nat.cast_add, Nat.cast_one]
          rw [rfl_cast]; simp [pow_two, mul_add]
        _ = (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by field_simp [hne]
    have nonneg_div_X : 0 ≤ (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by
      apply div_nonneg
      · exact_mod_cast (Nat.zero_le X)
      · exact le_of_lt (by exact_mod_cast Nat.zero_lt_succ X)
    have frac_le : (ε' * (X : ℝ) ^ 2) / (η * ((X + 1 : ℕ) : ℝ)) ≤ (ε' / η) * (X : ℝ) := by
      have hη_ne : η ≠ 0 := ne_of_gt hη
      have hX1_ne : ((X + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero X)
      have eq_field : (ε' * (X : ℝ) ^ 2) / (η * ((X + 1 : ℕ) : ℝ)) = (ε' / η) * ((X : ℝ) ^ 2 / ((X + 1 : ℕ) : ℝ)) := by
        field_simp [hη_ne, hX1_ne]
      rw [eq_field]
      -- replace (X^2)/(X+1) by X - X/(X+1) and use nonnegativity
      have : (ε' / η) * ((X : ℝ) ^ 2 / ((X + 1 : ℕ) : ℝ)) = (ε' / η) * ((X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ)) := by rw [eq_div]
      rw [this]
      have nonneg_coef : 0 ≤ ε' / η := div_nonneg (le_of_lt hε') (le_of_lt hη)
      have le_sub : (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by linarith [nonneg_div_X]
      exact mul_le_mul_of_nonneg_left le_sub nonneg_coef
    exact le_trans heavy_le frac_le
  exact eventual_bound

end DkMath.ABC
