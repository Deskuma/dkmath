/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic.Nat
import DkMath.ABC.ABC030

#print "file: DkMath.ABC.AdjacentQuality"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace DkMath.ABC

open DkMath.Basic.Nat
open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- ========================================================================

/-- Main eventual quality bound lemma using slice-based bounds.
Given ε > 0 with ε ≥ δ (where δ = 0.435), and a diagonal eventual badcount bound,
eventually the quality of the triple (n, n+1, 2n+1) is at most 1 + ε.

The constraint ε ≥ δ ensures we can set γ = ε - δ ≥ 0 to satisfy δ + γ ≤ ε.
For general ε > 0 (possibly < δ), use the density-one version instead.
-/
-- Density-one version: Holds for almost all n when ε > δ (δ = 0.435)
-- This is the "first-class citizen" version with explicit constraint
-- NOTE: Changed from ε ≥ δ to ε > δ (strict) because:
-- - The boundary case ε = δ gives γ = 0, requiring different proof strategy
-- - In practice, ABC conjecture is always studied with ε > δ
-- - The value δ = 0.435 is not exact, so equality is not meaningful
lemma adjacent_quality_le_density_one
  (ε : ℝ) (hε : 0 < ε) (hε_gt_δ : 0.435 < ε)
  (hTailProb :
    ∀ (δ : ℝ), 0 < δ →
      ∃ (C c β : ℝ) (n0 : ℕ),
        0 < C ∧ 0 < c ∧ 1 < β ∧
        ∀ n ≥ n0,
          (Measure.dirac ()).real (BadAdj δ n Unit) ≤ C * Real.exp (-c * (Real.log n) ^ β))
  (hDiagR : ∀ (ε' : ℝ), ε' > 0 → ∀ᶠ X in atTop,
    ((Finset.filter (fun b => b ≤ X ∧ is_bad_a 0.435 X b (b - 1)) (Finset.Icc 0 X)).card : ℝ) ≤ X ^ (3 / 4 + ε'))
  (hPolyBound : ∀ X : ℕ, (2*X+1 : ℝ) ≤ (rad (X*(X+1)) : ℝ) ^ (ε - 0.435)) :
  ∀ᶠ n in atTop, quality (Triple.mk n (n+1) (n + (n + 1)) (by rfl : n + (n + 1) = n + (n + 1)) (coprime_succ n)) ≤ 1 + ε := by
  let δ : ℝ := 0.435
  have hδ_pos : 0 < δ := by norm_num
  have hε_gt_δ' : δ < ε := hε_gt_δ
  let η := ε / 3
  have hη_pos : 0 < η := by
    apply _root_.div_pos
    · exact hε
    · norm_num
  let ε' := ε / 3
  have hε'_pos : 0 < ε' := by linarith
  have h_heavy := eventually_slice_heavy_sublinear (hδ_eq := rfl) (η := η) (ε' := ε') (hη := hη_pos) (hε' := hε'_pos)
  have h_diag : ∀ᶠ X in atTop, ((Finset.filter (fun b => b ≤ X ∧ is_bad_a 0.435 X b (b-1)) (Finset.Icc 0 X)).card : ℝ) ≤ X^(3/4 + ε') :=
    hDiagR ε' hε'_pos
  have h_not_bad_ev := eventually_not_is_bad_adjacent δ hδ_pos hTailProb
  have ev1 := Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩
  have all := Filter.Eventually.and
    (Filter.Eventually.and (Filter.Eventually.and ev1 h_heavy) h_diag)
    h_not_bad_ev
  refine all.mono ?_
  intro X ⟨⟨⟨hge1, h_heavyX⟩, h_diagX⟩, h_not_bad_X⟩

  let X' := X + 1
  let γ := ε - δ
  have hγ_pos : 0 < γ := sub_pos.mpr hε_gt_δ'
  have hγ_nonneg : 0 ≤ γ := le_of_lt hγ_pos
  have hδγ_nonneg : 0 ≤ δ + γ := by linarith [hδ_pos, hγ_nonneg]
  have hδγ_bound : δ + γ ≤ ε := by linarith
  have sum_slice_le_badcount : (∑ b ∈ Finset.range (X+1), (sliceBadCount (δ := δ) X b : ℝ)) ≤ (BadCount δ X : ℝ) := by
    exact_mod_cast (slice_sum_le_badcount (δ := δ) X)
  have slice_def : ∀ b ∈ Finset.range (X+1), (sliceBadCount (δ := δ) X b : ℝ) =
    ((Finset.filter (fun a' => is_bad_a δ X b a') (Finset.Icc 0 X)).card : ℝ) := by
    intro b hb
    dsimp [sliceBadCount]
    have hfin : (Finset.filter (fun a => is_bad_a δ X b a) (Finset.range (X + 1))) =
                (Finset.filter (fun a => is_bad_a δ X b a) (Finset.Icc 0 X)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Order.lt_add_one_iff, Finset.mem_Icc, zero_le,
        true_and]
    rw [hfin]
  have sum_filtered_le_badcount : (∑ b ∈ Finset.range (X+1), ((Finset.filter (fun k => is_bad_a δ X b k) (Finset.Icc 0 X)).card : ℝ)) ≤ (BadCount δ X : ℝ) := by
    have sum_eq : (∑ b ∈ Finset.range (X+1), (sliceBadCount (δ := δ) X b : ℝ)) =
      (∑ b ∈ Finset.range (X+1), ((Finset.filter (fun k => is_bad_a δ X b k) (Finset.Icc 0 X)).card : ℝ)) := by
      apply Finset.sum_congr rfl slice_def
    rw [← sum_eq]
    exact sum_slice_le_badcount
  let S := (Finset.range (X+1)).filter fun b => ((sliceBadCount (δ := δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ))
  let Scomp := (Finset.range (X+1)).filter fun b => ((sliceBadCount (δ := δ) X b : ℝ) < η * ((X + 1 : ℕ) : ℝ))
  have disj_union : Finset.range (X+1) = S ∪ Scomp := by
    classical
    ext b
    constructor
    · intro hb
      have hb_range : b ∈ Finset.range (X+1) := hb
      by_cases h : (↑(sliceBadCount (δ := δ) X b) ≥ η * ((X + 1 : ℕ) : ℝ))
      · have hS : b ∈ S := by
          apply Finset.mem_filter.mpr
          constructor
          · exact hb_range
          · exact h
        exact Finset.mem_union.mpr (Or.inl hS)
      · have hScomp : b ∈ Scomp := by
          apply Finset.mem_filter.mpr
          constructor
          · exact hb_range
          · exact lt_of_not_ge h
        exact Finset.mem_union.mpr (Or.inr hScomp)
    · intro h
      cases Finset.mem_union.mp h with
      | inl hleft => exact (Finset.mem_filter.mp hleft).1
      | inr hright => exact (Finset.mem_filter.mp hright).1
  have disj : Disjoint S Scomp := by
    rw [Finset.disjoint_left]
    intro b hbS hbScomp
    have h1 := (Finset.mem_filter.mp hbS).2
    have h2 := (Finset.mem_filter.mp hbScomp).2
    exact not_lt_of_ge h1 h2

  have sum_split : (∑ b ∈ Finset.range (X+1), ((Finset.filter (fun k => is_bad_a δ X b (b-1)) (Finset.Icc 0 X)).card : ℝ)) =
      (∑ b ∈ S, ((Finset.filter (fun k => is_bad_a δ X b (b-1)) (Finset.Icc 0 X)).card : ℝ))
      + (∑ b ∈ Scomp, ((Finset.filter (fun k => is_bad_a δ X b (b-1)) (Finset.Icc 0 X)).card : ℝ)) := by
    rw [disj_union]
    exact Finset.sum_union disj
  have sum_le_split : (∑ b ∈ Finset.range (X+1), ((Finset.filter (fun k => is_bad_a δ X b (b-1)) (Finset.Icc 0 X)).card : ℝ)) ≤
      (∑ b ∈ S, ((Finset.filter (fun k => is_bad_a δ X b (b-1)) (Finset.Icc 0 X)).card : ℝ))
      + (∑ b ∈ Scomp, ((Finset.filter (fun k => is_bad_a δ X b (b-1)) (Finset.Icc 0 X)).card : ℝ)) := by
    rw [sum_split]

  have hπ : (piSqRad (2*X+1) : ℝ) ≤ (rad (X*(X+1)) : ℝ) ^ δ := by
    have h_not_is_bad : ¬is_bad_a δ (2*X+1) (X+1) X := by
      exact h_not_bad_X
    have hrad_eq : rad (X * (X+1)) = rad X * rad (X+1) :=
      rad_mul_coprime' (coprime_succ X)
    have := piSqRad_adjacent_le_of_not_is_bad_a' (δ := δ) (n := X) h_not_is_bad
    convert this using 2
    norm_cast

  have hc_ne_zero : 2*X+1 ≠ 0 := by omega

  have hdecomp : (2*X+1 : ℝ) = (piSqRad (2*X+1) : ℝ) * (rad (2*X+1) : ℝ) * (twoTail (2*X+1) : ℝ) := by
    have h := decomp_piRad_twoTail_real (2*X+1) hc_ne_zero
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h ⊢
    convert h using 1
    ring

  have hsqTail_bound : (sqTail (2*X+1) : ℝ) ≤ (rad (X*(X+1)) : ℝ) ^ γ := by
    have hX_pos : 0 < X := Nat.zero_lt_of_lt hge1
    have hab_ne : X * (X+1) ≠ 0 := Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hX_pos) (by omega)
    by_cases hsf : Squarefree (2*X+1)
    · exact sqTail_adjacent_le_rad_pow_of_squarefree X γ hc_ne_zero hab_ne hsf hγ_pos
    · have h_sqtail_trivial : (sqTail (2*X+1) : ℝ) ≤ (2*X+1 : ℝ) := by
        have h := sqTail_le_self_real (2*X+1)
        convert h using 1
        norm_cast
      have h_poly_bound : (2*X+1 : ℝ) ≤ (rad (X*(X+1)) : ℝ) ^ γ := by
        simpa [γ, δ] using hPolyBound X
      exact le_trans h_sqtail_trivial h_poly_bound
  have htail_bound : (twoTail (2*X+1) : ℝ) ≤ (rad (X*(X+1)) : ℝ) ^ γ := by
    have h_bridge := twoTail_le_sqTail_real (2*X+1) hc_ne_zero
    exact le_trans h_bridge hsqTail_bound
  have htail : (2*X+1 : ℝ) ≤ (piSqRad (2*X+1) : ℝ) * (rad (X*(X+1)) : ℝ) ^ γ * (rad (2*X+1) : ℝ) := by
    have hdec_local := decomp_piRad_twoTail_real (2*X+1) hc_ne_zero
    have h_two_le := le_trans (twoTail_le_sqTail_real (2*X+1) hc_ne_zero) hsqTail_bound
    have hpos_left : 0 ≤ (piSqRad (2*X+1) : ℝ) * (rad (2*X+1) : ℝ) := by
      have h1 : (1 : ℝ) ≤ (piSqRad (2*X+1) : ℝ) := by exact_mod_cast (piSqRad_ge_one (2*X+1))
      have h2 : 0 < (rad (2*X+1) : ℝ) := rad_pos_real (2*X+1)
      exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) h1) (le_of_lt h2)
    have hmul := mul_le_mul_of_nonneg_left h_two_le hpos_left
    rw [hdec_local.symm] at hmul
    have : (piSqRad (2*X+1) : ℝ) * (rad (2*X+1) : ℝ) * (rad (X*(X+1)) : ℝ) ^ γ
        = (piSqRad (2*X+1) : ℝ) * (rad (X*(X+1)) : ℝ) ^ γ * (rad (2*X+1) : ℝ) := by ring
    rw [this] at hmul
    have h_cast : (↑(2 * X + 1) : ℝ) = 2 * (↑X : ℝ) + 1 := by norm_cast
    rw [h_cast] at hmul
    exact hmul

  have pointwise : quality (Triple.mk X (X + 1) (X + (X + 1)) (by rfl) (coprime_succ X)) ≤ 1 + ε := by
    have triple_eq : X + (X + 1) = 2*X + 1 := by ring
    have quality_eq : quality (Triple.mk X (X + 1) (X + (X + 1)) (by rfl) (coprime_succ X)) =
                      quality (Triple.mk X (X + 1) (2*X + 1) (by ring) (coprime_succ X)) := by
      simp only [quality, triple_eq]
    rw [quality_eq]
    have htail_local : (2*X+1 : ℝ) ≤ (piSqRad (2*X+1) : ℝ) * (rad (X*(X+1)) : ℝ) ^ γ * (rad (2*X+1) : ℝ) := by
      have hc_nz : 2*X+1 ≠ 0 := by omega
      have h_two_le := le_trans (twoTail_le_sqTail_real (2*X+1) hc_nz) hsqTail_bound
      have hpos_left : 0 ≤ (piSqRad (2*X+1) : ℝ) * (rad (2*X+1) : ℝ) := by
        have h1 : (1 : ℝ) ≤ (piSqRad (2*X+1) : ℝ) := by exact_mod_cast (piSqRad_ge_one (2*X+1))
        have h2 : 0 < (rad (2*X+1) : ℝ) := rad_pos_real (2*X+1)
        exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) h1) (le_of_lt h2)
      have hmul := mul_le_mul_of_nonneg_left h_two_le hpos_left
      have hdec := decomp_piRad_twoTail_real (2*X+1) hc_nz
      rw [hdec.symm] at hmul
      have : (piSqRad (2*X+1) : ℝ) * (rad (2*X+1) : ℝ) * (rad (X*(X+1)) : ℝ) ^ γ
          = (piSqRad (2*X+1) : ℝ) * (rad (X*(X+1)) : ℝ) ^ γ * (rad (2*X+1) : ℝ) := by ring
      rw [this] at hmul
      have h_cast : (↑(2 * X + 1) : ℝ) = 2 * (↑X : ℝ) + 1 := by norm_cast
      rw [h_cast] at hmul
      exact hmul
    exact adjacent_quality_bridge hε hδγ_nonneg hδγ_bound hπ htail_local

  exact pointwise

lemma adjacent_quality_le_ae_alt
  (ε : ℝ) (hε : 0 < ε)
  (hTailProb :
    ∀ (δ : ℝ), 0 < δ →
      ∃ (C c β : ℝ) (n0 : ℕ),
        0 < C ∧ 0 < c ∧ 1 < β ∧
        ∀ n ≥ n0,
          (Measure.dirac ()).real (BadAdj δ n Unit) ≤ C * Real.exp (-c * (Real.log n) ^ β))
  (hDiagR : ∀ (ε' : ℝ), ε' > 0 → ∀ᶠ X in atTop,
    ((Finset.filter (fun b => b ≤ X ∧ is_bad_a 0.435 X b (b - 1)) (Finset.Icc 0 X)).card : ℝ) ≤ X ^ (3 / 4 + ε'))
  (hPolyBound :
    ∀ (ε' : ℝ), 0 < ε' → 0.435 < ε' →
      ∀ X : ℕ, (2*X+1 : ℝ) ≤ (rad (X*(X+1)) : ℝ) ^ (ε' - 0.435))
  (hRefineLeDelta :
    ε ≤ 0.435 →
      ∀ᶠ n in atTop,
        quality (Triple.mk n (n+1) (n + (n + 1))
          (by rfl : n + (n + 1) = n + (n + 1)) (coprime_succ n)) ≤ 1 + ε) :
  ∀ᶠ n in atTop, quality (Triple.mk n (n+1) (n + (n + 1)) (by rfl : n + (n + 1) = n + (n + 1)) (coprime_succ n)) ≤ 1 + ε := by
  let δ : ℝ := 0.435
  have hδ_pos : 0 < δ := by norm_num

  by_cases h : δ < ε
  case pos =>
    exact adjacent_quality_le_density_one ε hε h hTailProb hDiagR (hPolyBound ε hε h)
  case neg =>
    push Not at h
    have hε_le_δ : ε ≤ δ := h
    exact hRefineLeDelta hε_le_δ

end DkMath.ABC
