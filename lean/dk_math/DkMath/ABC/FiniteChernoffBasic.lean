/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.ABC018

#print "file: DkMath.ABC.FiniteChernoffBasic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

lemma markov_card_bound
  (X : ℕ) (Y : ℕ → ℝ) (hY : ∀ n ≤ X, 0 ≤ Y n) {A : ℝ} (hA : 0 < A) :
  ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ)
    ≤ (Finset.sum (Finset.Icc 0 X) (fun n => Y n)) / A := by
  classical
  have h_calc :
      ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ) * A ≤
        Finset.sum (Finset.Icc 0 X) (fun n => Y n) := by
    calc
      ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ) * A =
          Finset.sum (Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)) (fun _ => A) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ Finset.sum (Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)) (fun n => Y n) := by
            apply Finset.sum_le_sum
            intro n hn
            simp [Finset.mem_filter] at hn
            linarith [hn.2]
      _ ≤ Finset.sum (Finset.Icc 0 X) (fun n => Y n) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · apply Finset.filter_subset
            · intro n hn _
              have : n ∈ Finset.Icc 0 X := hn
              rw [Finset.mem_Icc] at this
              exact hY n this.2
  calc
    ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ) =
        (((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ) * A) / A := by
          field_simp
    _ ≤ (Finset.sum (Finset.Icc 0 X) (fun n => Y n)) / A := by
          apply div_le_div_of_nonneg_right h_calc
          positivity

lemma sum_Icc_telescope (m : ℕ) (f : ℕ → ℝ) :
  Finset.sum (Finset.Icc 1 m) (fun k => f k - f (k - 1)) = f m - f 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · induction m with
    | zero =>
        simp at hm
    | succ m ihm =>
        by_cases hm0 : m = 0
        · simp [hm0]
        · rw [Finset.sum_Icc_succ_top]
          · rw [ihm hm0]
            simp
          · omega

lemma exp_layer_cake
  (X : ℕ) (t : ℝ) (ht : 0 < t) (V : ℕ → ℕ)
  (hVbd : ∀ n ≤ X, V n ≤ X + 1) :
  (Finset.sum (Finset.Icc 0 X) (fun n => Real.exp (t * (V n : ℝ))))
    ≤ (X + 1 : ℝ) + (Real.exp t - 1) *
        (Finset.sum (Finset.Icc 1 (X + 1)) (fun k =>
          Real.exp (t * ((k : ℝ) - 1)) *
          ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ))) := by
  classical
  have h_decomp : ∀ n ≤ X, Real.exp (t * (V n : ℝ))
      = 1 + Finset.sum (Finset.Icc 1 (V n))
        (fun k => Real.exp (t * (k : ℝ)) - Real.exp (t * ((k - 1) : ℝ))) := by
    intro n _
    by_cases hV : V n = 0
    · simp [hV]
    · have h_tele :
          Finset.sum (Finset.Icc 1 (V n))
            (fun k => Real.exp (t * (k : ℝ)) - Real.exp (t * ((k - 1) : ℝ))) =
            Real.exp (t * (V n : ℝ)) - 1 := by
        have h := sum_Icc_telescope (V n) (fun k => Real.exp (t * (k : ℝ)))
        simp only [Nat.cast_zero, mul_zero, Real.exp_zero] at h
        refine Eq.trans ?_ h
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        norm_cast
      rw [h_tele]
      ring
  calc
    Finset.sum (Finset.Icc 0 X) (fun n => Real.exp (t * (V n : ℝ))) =
        Finset.sum (Finset.Icc 0 X) (fun n =>
          1 + Finset.sum (Finset.Icc 1 (V n))
            (fun k => Real.exp (t * (k : ℝ)) - Real.exp (t * ((k - 1) : ℝ)))) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_Icc] at hn
          exact h_decomp n hn.2
    _ = (X + 1) + Finset.sum (Finset.Icc 0 X) (fun n =>
          Finset.sum (Finset.Icc 1 (V n))
            (fun k => Real.exp (t * (k : ℝ)) - Real.exp (t * ((k - 1) : ℝ)))) := by
          rw [Finset.sum_add_distrib, Finset.sum_const]
          have h_card : (Finset.Icc 0 X).card = X + 1 := by
            rw [Nat.card_Icc]
            omega
          rw [h_card]
          simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    _ ≤ (X + 1 : ℝ) + (Real.exp t - 1) *
          Finset.sum (Finset.Icc 1 (X + 1)) (fun k =>
            Real.exp (t * ((k : ℝ) - 1)) *
            ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ)) := by
          have h_factor : ∀ k : ℕ, 1 ≤ k →
              Real.exp (t * (k : ℝ)) - Real.exp (t * ((k - 1) : ℝ)) =
                (Real.exp t - 1) * Real.exp (t * ((k - 1) : ℝ)) := by
            intro k hk
            have h_eq : (k : ℝ) = ((k - 1) : ℝ) + 1 := by simp
            rw [h_eq, mul_add, Real.exp_add]
            ring_nf
          have h_rewrite :
              ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n),
                (Real.exp (t * (k : ℝ)) - Real.exp (t * ((k - 1) : ℝ))) =
              (Real.exp t - 1) * ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n),
                Real.exp (t * ((k - 1) : ℝ)) := by
            trans
              (∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n),
                (Real.exp t - 1) * Real.exp (t * ((k - 1) : ℝ)))
            · apply Finset.sum_congr rfl
              intro n _
              apply Finset.sum_congr rfl
              intro k hk
              exact h_factor k (Finset.mem_Icc.mp hk).1
            · simp [Finset.mul_sum]
          rw [h_rewrite]
          have ht_pos : 0 ≤ Real.exp t - 1 := by
            have : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr (le_of_lt ht)
            linarith
          gcongr
          calc
            ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n), Real.exp (t * ((k - 1) : ℝ)) =
                ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (X + 1),
                  if k ≤ V n then Real.exp (t * ((k - 1) : ℝ)) else 0 := by
                    apply Finset.sum_congr rfl
                    intro n hn
                    have hV : V n ≤ X + 1 := hVbd n (Finset.mem_Icc.mp hn).2
                    rw [← Finset.sum_filter]
                    apply Finset.sum_congr
                    · ext k
                      simp only [Finset.mem_filter, Finset.mem_Icc]
                      constructor
                      · intro h
                        exact ⟨⟨h.1, Nat.le_trans h.2 hV⟩, h.2⟩
                      · intro h
                        exact ⟨h.1.1, h.2⟩
                    · intro k _
                      rfl
            _ = ∑ k ∈ Finset.Icc 1 (X + 1), ∑ n ∈ Finset.Icc 0 X,
                  if k ≤ V n then Real.exp (t * ((k - 1) : ℝ)) else 0 := by
                    exact Finset.sum_comm
            _ = ∑ k ∈ Finset.Icc 1 (X + 1), Real.exp (t * ((k : ℝ) - 1)) *
                  (Finset.filter (fun n => k ≤ V n) (Finset.Icc 0 X)).card := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [← Finset.sum_filter, Finset.sum_const]
                    simp [nsmul_eq_mul, mul_comm]
            _ ≤ ∑ k ∈ Finset.Icc 1 (X + 1), Real.exp (t * ((k : ℝ) - 1)) *
                  (Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card := by
                    apply Finset.sum_le_sum
                    intro k _
                    apply mul_le_mul_of_nonneg_left
                    · norm_cast
                      apply Finset.card_le_card
                      intro n hn
                      simp [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
                      omega
                    · positivity

end DkMath.ABC
