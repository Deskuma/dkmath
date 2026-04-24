/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ChernoffDyadic
import DkMath.ABC.HeavyPrimeBudget
import DkMath.ABC.HeavyPrimeCounting
import DkMath.ABC.HeavyPrimeSelection
import DkMath.ABC.TailSquareBridge
import DkMath.ABC.SquareTailBasic

#print "file: DkMath.ABC.AdjacentTailDensity"

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

/- Union bound over non-heavy primes
   Sum Chernoff bounds over all primes not in S_heavy -/
/--
$\gamma > 0$ を実数、$X$ を自然数、$S_{\mathrm{heavy}}$ を有限部分集合 $\mathbb{N}$ とする。
$S_{\mathrm{heavy}}$ の各元 $p$ について $p$ は素数かつ $p^3 > X$ であると仮定する。

このとき、ある自然数 $K_{\mathrm{chernoff}}$ が存在して、次の集合
$$
\left\{ n \in [0, X] \mid \sum_{\substack{p \mid 2n+1 \\ p \notin S_{\mathrm{heavy}}}} \left((v_p(2n+1) - 2) \log p \right) > \gamma \log \operatorname{rad}(n(n+1)) \right\}
$$
の濃度（要素数）は $K_{\mathrm{chernoff}}$ 以下である。

ここで、$v_p(m)$ は $m$ の $p$ 進指数、$\operatorname{rad}(m)$ は $m$ の radical（異なる素因数の積）を表す。
この補題は、Chernoff型の確率的手法を用いた和集合界（union bound）に関する主張である。
-/
lemma union_bound_chernoff_log_rad (γ : ℝ) (_hγ : 0 < γ) (X : ℕ)
  (S_heavy : Finset ℕ)
  (_hS : ∀ p ∈ S_heavy, p.Prime ∧ p ^ 3 > X) :
    ∃ (K_chernoff : ℕ),
    (Finset.filter (fun n => n ≤ X ∧
      (Finset.sum ((2*n+1).factorization.support.filter (fun p => p ∉ S_heavy)) fun p =>
        ((((2*n+1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ)
      ) > γ * Real.log (rad (n*(n+1)) : ℝ)
    ) (Finset.Icc 0 X)).card ≤ K_chernoff := by
  have h_sub :
    (Finset.filter (fun (n : ℕ) => n ≤ X ∧
        (Finset.sum ((2 * n + 1).factorization.support.filter fun p => p ∉ S_heavy)
          fun p => ((((2 * n + 1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ))
          > γ * Real.log (rad (n * (n + 1)) : ℝ))
      (Finset.Icc 0 X)) ⊆ Finset.Icc 0 X := by
    apply Finset.filter_subset
  have h_card_le : (Finset.filter (fun (n : ℕ) => n ≤ X ∧
        (Finset.sum ((2 * n + 1).factorization.support.filter fun p => p ∉ S_heavy)
          fun p => ((((2 * n + 1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ))
          > γ * Real.log (rad (n * (n + 1)) : ℝ))
      (Finset.Icc 0 X)).card ≤ (Finset.Icc 0 X).card := Finset.card_le_card h_sub
  have h_Icc_sub_range : Finset.Icc 0 X ⊆ Finset.range (X + 1) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨_, hle⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have h_Icc_card_le : (Finset.Icc 0 X).card ≤ (Finset.range (X + 1)).card := Finset.card_le_card h_Icc_sub_range
  use X + 1
  calc (Finset.filter (fun (n : ℕ) => n ≤ X ∧
        (Finset.sum ((2 * n + 1).factorization.support.filter fun p => p ∉ S_heavy)
          fun p => ((((2 * n + 1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ))
          > γ * Real.log (rad (n * (n + 1)) : ℝ))
      (Finset.Icc 0 X)).card
      ≤ (Finset.Icc 0 X).card := h_card_le
  _ ≤ (Finset.range (X + 1)).card := h_Icc_card_le
  _ = X + 1 := by simp [Finset.card_range]

lemma chernoff_single_prime_uniform (γ : ℝ) (hγ : 0 < γ) :
  ∃ (t0 : ℝ) (U : ℝ), 0 < t0 ∧ t0 ≤ 1 / 2 ∧ 0 < U ∧
    ∀ p (_hp : p.Prime), ∃ (t : ℝ) (C : ℝ), 0 < t ∧ t ≤ 1/2 ∧ C > 0 ∧
      ∀ X (_hX : X ≥ 100),
        (Finset.filter (fun n => n ≤ X ∧
          (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ)
        > γ * Real.log (p : ℝ)) (Finset.Icc 0 X)).card
        ≤ C * (X : ℝ) * Real.exp (- t * γ * Real.log (p : ℝ)) := by
  let t0 := min (γ / 4) (1 / 4)
  let U := 1
  have ht0_pos : 0 < t0 := by
    apply lt_min
    · linarith [hγ]
    · norm_num
  have ht0_le_half : t0 ≤ 1 / 2 := by
    calc t0 = min (γ / 4) (1 / 4) := rfl
      _ ≤ (1 : ℝ) / 4 := min_le_right _ _
      _ ≤ 1 / 2 := by norm_num
  have hU_pos : (0 : ℝ) < U := by norm_num
  use t0, U, ht0_pos, ht0_le_half, hU_pos
  intro p hp
  obtain ⟨t, C, ht, ht_half, hC_pos, hbound⟩ := chernoff_single_prime p hp γ hγ
  use t, C, ht, ht_half, hC_pos, hbound

lemma chernoff_single_prime_uniform_easy (γ : ℝ) (hγ : 0 < γ) :
  ∃ (t0 : ℝ) (U : ℝ), 0 < t0 ∧ t0 ≤ 1 / 2 ∧ 0 < U ∧
    ∀ p (_hp : p.Prime), ∃ (t : ℝ) (C : ℝ), 0 < t ∧ t ≤ 1/2 ∧ C > 0 ∧
      ∀ X (_hX : X ≥ 100),
        (Finset.filter (fun n => n ≤ X ∧
          (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ)
        > γ * Real.log (p : ℝ)) (Finset.Icc 0 X)).card
        ≤ C * (X : ℝ) * Real.exp (- t * γ * Real.log (p : ℝ)) := by
  let t0 := min (γ / 4) (1 / 4)
  let U := (12 : ℝ)
  have ht0_pos : 0 < t0 := by
    apply lt_min
    · linarith
    · norm_num
  have ht0_le : t0 ≤ 1/2 := by
    dsimp [t0]
    apply le_trans (min_le_right _ _) (by norm_num)
  have hU_pos : 0 < U := by norm_num
  use t0, U, ht0_pos, ht0_le, hU_pos
  intro p hp
  obtain ⟨t, C, ht, ht_half, hC_pos, hbound⟩ := chernoff_single_prime p hp γ hγ
  use t, C, ht, ht_half, hC_pos

def EventuallyChernoffBudgetAdjacentHypothesis : Prop :=
  ∀ (γ ε' : ℝ), (hγ : 0 < γ) → (hε' : 0 < ε') →
  ∀ᶠ (X : ℕ) in atTop,
    (let B : ℕ := 4; let K_full := ⌈(X : ℝ)^(3/4 + ε')⌉₊;
     let K_heavy := ⌈(X : ℝ)^(3/4 + ε') / (B + 1)⌉₊;
     let K_chernoff := K_full - B * K_heavy;
     (Finset.filter
       (fun (n : ℕ) => n ≤ X ∧
         (Finset.sum (2*n+1).factorization.support fun (p : ℕ) =>
           ((((2*n+1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ)
         ) > γ * Real.log (rad (n*(n+1)) : ℝ)
       )
       (Finset.Icc 0 X)
     ).card ≤ K_chernoff)

lemma twoTail_log_bound_adjacent_density_one
    (γ ε' : ℝ) (hγ : 0 < γ) (hε' : 0 < ε')
    (hChernoffBudget : EventuallyChernoffBudgetAdjacentHypothesis)
    : ∀ᶠ X in atTop,
        (Finset.filter (fun n => n ≤ X ∧
           Real.log (twoTail (2*n+1) : ℝ)
             ≤ γ * Real.log (rad (n*(n+1)) : ℝ))
          (Finset.Icc 0 X)).card
        ≥ (X + 1 : ℕ) - ⌈(X : ℝ)^(3/4 + ε')⌉₊ := by
  classical
  have h_heavy : ∀ᶠ (X : ℕ) in atTop, ∃ (S_heavy : Finset ℕ),
    (let B : ℕ := 4; let K_heavy := ⌈(X : ℝ)^(3/4 + ε') / (B + 1)⌉₊;
     S_heavy.card ≤ K_heavy ∧ ∀ p ∈ S_heavy, p ^ 3 > X ∧ p.Prime ∧
      ∃ (n : ℕ), n ≤ X ∧ (n*(n+1)).factorization p ≥ 2 + ⌈γ⌉₊) := eventually_of_forall fun X => by
      let B : ℕ := 4
      let K_heavy := ⌈(X : ℝ)^(3/4 + ε') / (B + 1)⌉₊
      let S := S_heavy_def γ X
      let S_heavy := Finset.filter (fun p => p ^ 3 > X) (S ∩ (Finset.range K_heavy))
      use S_heavy
      constructor
      · -- ⊢ S_heavy.card ≤ ⌈↑X ^ (3 / 4 + ε') / (↑4 + 1)⌉₊
        have hsub : S_heavy ⊆ Finset.range K_heavy := by
          intro p hp
          have hmem := Finset.mem_filter.mp hp
          have h_inter := Finset.mem_inter.mp hmem.1
          exact h_inter.2
        calc S_heavy.card ≤ (Finset.range K_heavy).card := Finset.card_le_card hsub
        _ = K_heavy := Finset.card_range K_heavy
      · -- ⊢ ∀ p ∈ S_heavy, p ^ 3 > X ∧ Nat.Prime p ∧ ∃ n ≤ X, (n * (n + 1)).factorization p ≥ 2 + ⌈γ⌉₊
        intro p hp
        have ⟨h_inter, h_p3⟩ := Finset.mem_filter.mp hp
        have hS_mem : p ∈ S := (Finset.mem_inter.mp h_inter).1
        rcases witness_n_for_S_heavy hS_mem with ⟨n, hn, hfac⟩
        have ⟨_, ⟨hprime, _⟩⟩ := Finset.mem_filter.mp hS_mem
        exact ⟨h_p3, hprime, ⟨n, hn, hfac⟩⟩

  have h_chernoff : ∀ᶠ (X : ℕ) in atTop,
    (let B : ℕ := 4; let K_full := ⌈(X : ℝ)^(3/4 + ε')⌉₊;
     let K_heavy := ⌈(X : ℝ)^(3/4 + ε') / (B + 1)⌉₊;
     let K_chernoff := K_full - B * K_heavy;
     (Finset.filter
       (fun (n : ℕ) => n ≤ X ∧
         (Finset.sum (2*n+1).factorization.support fun (p : ℕ) =>
           ((((2*n+1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ)
         ) > γ * Real.log (rad (n*(n+1)) : ℝ)
       )
       (Finset.Icc 0 X)
     ).card ≤ K_chernoff) :=
    hChernoffBudget γ ε' hγ hε'

  have h_pow_ge_20 := eventually_pow_ge_twenty ε' hε'
  refine Filter.Eventually.mono (h_heavy.and (h_chernoff.and h_pow_ge_20)) ?_
  intro X ⟨⟨S_heavy, hS_card_and_prop⟩, hChernoff, hX_pow_ge_20⟩

  let B : ℕ := 4
  let K_full := ⌈(X : ℝ)^(3/4 + ε')⌉₊
  let K_heavy := ⌈(X : ℝ)^(3/4 + ε') / (B + 1)⌉₊
  let K_chernoff := K_full - B * K_heavy

  have hS_card : S_heavy.card ≤ K_heavy := hS_card_and_prop.1
  have hS_prop : ∀ p ∈ S_heavy, p ^ 3 > X ∧ p.Prime ∧
    ∃ (n : ℕ), n ≤ X ∧ (n*(n+1)).factorization p ≥ 2 + ⌈γ⌉₊ := hS_card_and_prop.2

  have h_good_count_K :
      (Finset.filter (fun n => n ≤ X ∧
         Real.log (twoTail (2*n+1) : ℝ)
           ≤ γ * Real.log (rad (n*(n+1)) : ℝ))
        (Finset.Icc 0 X)).card
      ≥ (X + 1) - K_full := by
    have hS_heavy_p3 : ∀ p ∈ S_heavy, p ^ 3 > X := fun p hp => (hS_prop p hp).1

    let Bad_heavy := (Finset.Icc 0 X).filter (fun n =>
      ∃ p ∈ S_heavy, (n*(n+1)).factorization p ≥ 2 + ⌈γ⌉₊)

    let Bad_chernoff := Finset.filter (fun (n : ℕ) => n ≤ X ∧
      (Finset.sum (2*n+1).factorization.support fun (p : ℕ) =>
        ((((2*n+1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ))
          > γ * Real.log (rad (n*(n+1)) : ℝ))
      (Finset.Icc 0 X)

    have h_heavy_bound : Bad_heavy.card ≤ B * K_heavy := by
      have hS_prime' : ∀ p ∈ S_heavy, p.Prime := fun p hp => (hS_prop p hp).2.1
      have hS_heavy3 : ∀ p ∈ S_heavy, ∃ n ≤ X, (n * (n + 1)).factorization p ≥ 3 := by
        intro p hp
        rcases (hS_prop p hp).2.2 with ⟨n, hnX, hv⟩
        have one_le_ceil : 1 ≤ ⌈(γ : ℝ)⌉₊ := by
          have : 0 < (γ : ℝ) := hγ
          exact (Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr this))
        have three_le : 3 ≤ 2 + ⌈(γ : ℝ)⌉₊ := by
          calc 3 = 2 + 1 := by norm_num
            _ ≤ 2 + ⌈(γ : ℝ)⌉₊ := by apply Nat.add_le_add_left; exact one_le_ceil
        have hv3 : 3 ≤ (n * (n + 1)).factorization p := Nat.le_trans three_le hv
        exact ⟨n, hnX, hv3⟩
      let big_bound := heavy_primes_affect_sublinear_n S_heavy X K_heavy hS_card hS_prime' hS_heavy3
      have subset_bad : Bad_heavy ⊆ (Finset.Icc 0 X).filter fun n => ∃ p ∈ S_heavy, (n * (n + 1)).factorization p ≥ 3 := by
        intro n hn
        rcases Finset.mem_filter.mp hn with ⟨hnX, ⟨p, hpS, hpv⟩⟩
        have one_le_ceil : 1 ≤ ⌈(γ : ℝ)⌉₊ := by
          have : 0 < (γ : ℝ) := hγ
          exact (Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr this))
        have three_le : 3 ≤ 2 + ⌈(γ : ℝ)⌉₊ := by
          calc 3 = 2 + 1 := by norm_num
            _ ≤ 2 + ⌈(γ : ℝ)⌉₊ := by apply Nat.add_le_add_left; exact one_le_ceil
        have hv3 := Nat.le_trans three_le hpv
        exact Finset.mem_filter.mpr ⟨hnX, ⟨p, hpS, hv3⟩⟩
      have le_sum := le_trans (Finset.card_le_card subset_bad) big_bound

      have sum_le_4K : (∑ p ∈ S_heavy, (2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2)) ≤ ∑ p ∈ S_heavy, (4 : ℕ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact term_le_four_of_p3_gt_X (hS_heavy_p3 p hp)

      have final_bound : Bad_heavy.card ≤ 4 * S_heavy.card := by
        calc Bad_heavy.card
          ≤ ∑ p ∈ S_heavy, (2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2) := le_sum
          _ ≤ ∑ p ∈ S_heavy, (4 : ℕ) := sum_le_4K
          _ = 4 * S_heavy.card := by simp [Finset.sum_const, Nat.mul_comm]

      calc Bad_heavy.card
        ≤ 4 * S_heavy.card := final_bound
        _ ≤ 4 * K_heavy := Nat.mul_le_mul_left 4 hS_card
        _ = B * K_heavy := by rfl

    have compl_bad_subset_good : (Finset.Icc 0 X) \ (Bad_heavy ∪ Bad_chernoff)
      ⊆ (Finset.filter (fun n => n ≤ X ∧
           Real.log (twoTail (2*n+1) : ℝ)
             ≤ γ * Real.log (rad (n*(n+1)) : ℝ))
          (Finset.Icc 0 X)) := by
      intro n hn
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
      rcases hn with ⟨i_mem, hnot⟩
      have hsum_le : (Finset.sum (2*n+1).factorization.support fun (p : ℕ) =>
        (((2*n+1).factorization p - 2 : ℕ) : ℝ) * Real.log (p : ℝ))
          ≤ γ * Real.log (rad (n*(n+1)) : ℝ) := by
        apply le_of_not_gt
        intro H
        have mem : n ∈ Bad_chernoff := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr i_mem, And.intro i_mem.2 H⟩
        exact hnot (Finset.mem_union_right Bad_heavy mem)
      have hc : (2*n + 1) ≠ 0 := by linarith
      have hlog_le := log_twoTail_le_excess_sum (2*n+1) hc
      have final_le := le_trans hlog_le hsum_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr i_mem, And.intro i_mem.2 final_le⟩

    have h_bad_sub : Bad_heavy ∪ Bad_chernoff ⊆ Finset.Icc 0 X := by
      apply Finset.union_subset_iff.mpr
      constructor
      · exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _

    have h_sdiff_le_good : ((Finset.Icc 0 X) \ (Bad_heavy ∪ Bad_chernoff)).card ≤
      (Finset.filter (fun n => n ≤ X ∧
        Real.log (twoTail (2*n+1) : ℝ)
          ≤ γ * Real.log (rad (n*(n+1)) : ℝ)) (Finset.Icc 0 X)).card :=
      Finset.card_le_card compl_bad_subset_good

    have h_sdiff_eq := Finset.card_sdiff_of_subset h_bad_sub

    have h_good_ge_Icc_sub_bad :
      (Finset.filter (fun n => n ≤ X ∧
        Real.log (twoTail (2*n+1) : ℝ)
          ≤ γ * Real.log (rad (n*(n+1)) : ℝ)) (Finset.Icc 0 X)).card
      ≥ (Finset.Icc 0 X).card - (Bad_heavy ∪ Bad_chernoff).card := by
      calc (Finset.filter (fun n => n ≤ X ∧
             Real.log (twoTail (2*n+1) : ℝ)
               ≤ γ * Real.log (rad (n*(n+1)) : ℝ)) (Finset.Icc 0 X)).card
          ≥ ((Finset.Icc 0 X) \ (Bad_heavy ∪ Bad_chernoff)).card := by exact h_sdiff_le_good
        _ = (Finset.Icc 0 X).card - (Bad_heavy ∪ Bad_chernoff).card := by rw [h_sdiff_eq]

    have h_union : (Bad_heavy ∪ Bad_chernoff).card ≤ Bad_heavy.card + Bad_chernoff.card := by
      exact Finset.card_union_le Bad_heavy Bad_chernoff

    have h_good_count : (Finset.filter (fun n => n ≤ X ∧
             Real.log (twoTail (2*n+1) : ℝ)
               ≤ γ * Real.log (rad (n*(n+1)) : ℝ))
            (Finset.Icc 0 X)).card
        ≥ (X + 1) - (Bad_heavy.card + Bad_chernoff.card) := by
      have h1 := h_good_ge_Icc_sub_bad
      have h2 : (Finset.Icc 0 X).card - (Bad_heavy.card + Bad_chernoff.card) ≤
        (Finset.Icc 0 X).card - (Bad_heavy ∪ Bad_chernoff).card := by apply Nat.sub_le_sub_left h_union
      have ineq : (Finset.Icc 0 X).card - (Bad_heavy.card + Bad_chernoff.card) ≤
        (Finset.filter (fun n => n ≤ X ∧
          Real.log (twoTail (2*n+1) : ℝ)
            ≤ γ * Real.log (rad (n*(n+1)) : ℝ)) (Finset.Icc 0 X)).card := by
        exact le_trans h2 h1
      have card_eq : (Finset.Icc 0 X).card = X + 1 := by rw [Nat.card_Icc]; omega
      rw [card_eq] at ineq
      exact ineq

    have total_bound : (Bad_heavy.card + Bad_chernoff.card) ≤ K_full := by
      have sum_eq_K : B * K_heavy + K_chernoff = K_full := by
        have hB_le : B * K_heavy ≤ K_full := by
          change 4 * ⌈(X : ℝ)^(3/4 + ε') / ((4 : ℕ) + 1)⌉₊ ≤ ⌈(X : ℝ)^(3/4 + ε')⌉₊
          norm_num
          exact B_mul_ceil_div_le_ceil_of_large ((X : ℝ)^(3/4 + ε')) hX_pow_ge_20
        exact Nat.add_sub_of_le hB_le
      calc Bad_heavy.card + Bad_chernoff.card
        ≤ B * K_heavy + K_chernoff := Nat.add_le_add h_heavy_bound hChernoff
        _ = K_full := sum_eq_K

    calc _
      ≥ (X + 1) - (Bad_heavy.card + Bad_chernoff.card) := h_good_count
      _ ≥ (X + 1) - K_full := Nat.sub_le_sub_left total_bound (X + 1)

  exact h_good_count_K

end DkMath.ABC
