/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBlockDyadicTail

#print "file: DkMath.ABC.TailUnionBasic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `TailRadicalBasic.lean` から切り出した finite-union / independent Cstar owner。
  middle-block independent absorption と確率測度の基本上界だけを置く。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory


/-- Finite union (Boole) lemma: measure of finite union ≤ sum of measures. -/
lemma measure_union_over_k
  {Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  (K : Finset ℕ) (A : ℕ → Set Ω) :
  μ.real (⋃ k ∈ K, A k) ≤ ∑ k ∈ K, μ.real (A k) := by
  exact MeasureTheory.measureReal_biUnion_finset_le K A


/-- If each `μ.real (A k)` is bounded by `B k` on `K`, then the finite union is bounded by the sum of `B`. -/
lemma measure_union_over_k_bound
  {Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  (K : Finset ℕ) (A : ℕ → Set Ω) (B : ℕ → ℝ)
  (h : ∀ k ∈ K, μ.real (A k) ≤ B k) :
  μ.real (⋃ k ∈ K, A k) ≤ ∑ k ∈ K, B k := by
  calc
    μ.real (⋃ k ∈ K, A k) ≤ ∑ k ∈ K, μ.real (A k) := MeasureTheory.measureReal_biUnion_finset_le K A
    _ ≤ ∑ k ∈ K, B k := Finset.sum_le_sum (fun k hk => h k hk)


/-- `C * exp(-c * 2^k)` is summable for `c > 0`. -/
lemma summable_exp_neg_two_pow_mul {C c : ℝ} (_hC : 0 ≤ C) (hc : 0 < c) :
  Summable (fun k : ℕ => C * Real.exp (- c * ((2 : ℝ) ^ k))) := by
  have hsum := Prob.summable_exp_neg_two_pow c hc
  exact Summable.mul_left C hsum


/- 中域・独立版の合併確率を吸収する X 非依存定数（C⋆₍indep₎）。 -/
noncomputable def midblockCstarIndep (δ : ℝ) : ℝ :=
  (3 : ℝ) + (∑' k : ℕ, Real.exp (-(δ ^ 2) * (2 : ℝ) ^ k))


/- Simple helper: probability-measure の下で任意事象の実数化測度は ≤ 1。 -/
lemma prob_real_le_one {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (A : Set Ω) : μ.real A ≤ 1 := by
  have hle := MeasureTheory.measure_mono (μ := μ) (Set.subset_univ A)
  have htop : μ (Set.univ : Set Ω) ≠ ⊤ := by simp [IsProbabilityMeasure.measure_univ]
  have : (μ A).toReal ≤ (μ (Set.univ : Set Ω)).toReal := ENNReal.toReal_mono htop hle
  calc
    μ.real A = (μ A).toReal := rfl
    _ ≤ (μ (Set.univ : Set Ω)).toReal := this
    _ = 1 := by simp [IsProbabilityMeasure.measure_univ]


end DkMath.ABC
