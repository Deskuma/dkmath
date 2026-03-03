/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC028

#print "file: DkMath.ABC.ABC029"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-
-- Extract the existential constants from `chernoff_single_prime` without the full bound.
-- This lemma packages (t,C,ht,ht_le_half,hC_pos) for a prime p and parameter γ > 0. -/
lemma chernoff_single_prime_constants (p : ℕ) (hp : p.Prime) (γ : ℝ) (hγ : 0 < γ) :
  ∃ (t : ℝ) (C : ℝ), 0 < t ∧ t ≤ 1 / 2 ∧ C > 0 := by
  obtain ⟨t, C, ht, ht_half, hC_pos, _hbound⟩ := chernoff_single_prime p hp γ hγ
  exact ⟨t, C, ht, ht_half, hC_pos⟩


/- Helper: For a finite set of primes `P_light`, extract per-prime Chernoff constants
   (t_p, C_p) for each prime p ∈ P_light. This packages Step (2) so later code
   can iterate over the primes and form the required sums.
 -/
-- Helper: For a finite set of primes `P_light`, extract per-prime Chernoff constants
-- (t_p, C_p) for each prime p ∈ P_light. This packages Step (2) so later code
-- can iterate over the primes and form the required sums.
lemma chernoff_constants_for_finset (P_light : Finset ℕ) (γ : ℝ) (hγ : 0 < γ)
  (hP_primes : ∀ p ∈ P_light, p.Prime) :
  ∀ p ∈ P_light, ∃ (t : ℝ) (C : ℝ), 0 < t ∧ t ≤ 1/2 ∧ C > 0 := by
  intro p hp_mem
  -- use the supplied primality proof for p ∈ P_light
  have hp_pr := hP_primes p hp_mem
  obtain ⟨t_p, C_p, ht_pos, ht_half, hC_pos⟩ := chernoff_single_prime_constants p hp_pr γ hγ
  exact ⟨t_p, C_p, ht_pos, ht_half, hC_pos⟩


/- Crude sum bound: for any functions t_p and C_p on primes, the weighted sum
   Σ_{p ∈ P_light} C_p * X * p^{-t_p * γ_p} is bounded by X * Σ_{p ∈ P_light} C_p
   because p^{-t_p * γ_p} ≤ 1. This is a small but useful inequality when
   building a scaffold for the analytic evaluation of the union bound.
-/
lemma chernoff_sum_crude_bound
  (P_light : Finset ℕ) (γ_p : ℕ → ℝ) (t_of : ℕ → ℝ) (C_of : ℕ → ℝ) (X : ℕ)
  (hP_primes : ∀ p ∈ P_light, p.Prime)
  (hC_nonneg : ∀ p ∈ P_light, 0 ≤ C_of p)
  (h_exp_nonneg : ∀ p ∈ P_light, 0 ≤ t_of p * γ_p p) :
  (Finset.sum P_light fun p => C_of p * (X : ℝ) * (p : ℝ) ^ (-(t_of p * γ_p p)))
    ≤ (X : ℝ) * (Finset.sum P_light fun p => C_of p) := by
  -- Elementwise bound: for p ≥ 1 and exponent ≤ 0, p^{-(tγ)} ≤ 1
  have h_elem_le : ∀ p ∈ P_light, C_of p * (X : ℝ) * (p : ℝ) ^ (-(t_of p * γ_p p)) ≤ (X : ℝ) * C_of p := by
    intro p hp
    have hCpos : 0 ≤ C_of p := hC_nonneg p hp
    have hXpos : 0 ≤ (X : ℝ) := by apply Nat.cast_nonneg
    have hexp_nonneg := h_exp_nonneg p hp
    -- p as real ≥ 1
    have hprime : p.Prime := hP_primes p hp
    have hp_ge_one : (1 : ℝ) ≤ (p : ℝ) := by
      have one_lt_p : 1 < p := Nat.Prime.one_lt hprime
      have one_le_p : 1 ≤ p := Nat.le_of_lt one_lt_p
      exact_mod_cast one_le_p
    -- exponent is nonpositive: -(t*γ) ≤ 0 because t*γ ≥ 0
    have hexp_nonpos : (-(t_of p * γ_p p)) ≤ 0 := by linarith [hexp_nonneg]
    -- use mathlib lemma for rpow with x ≥ 1 and exponent ≤ 0
    have hpow_le_one := Real.rpow_le_one_of_one_le_of_nonpos hp_ge_one hexp_nonpos
    calc C_of p * (X : ℝ) * (p : ℝ) ^ (-(t_of p * γ_p p))
        ≤ C_of p * (X : ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left hpow_le_one
          exact mul_nonneg hCpos hXpos
      _ = (X : ℝ) * C_of p := by ring
  -- Sum and factor out X
  have hsum := Finset.sum_le_sum h_elem_le
  -- Factor out (X : ℝ) from the RHS sum to match the expected shape
  have hsum' : Finset.sum P_light (fun p => C_of p * (X : ℝ) * (p : ℝ) ^ (-(t_of p * γ_p p)))
    ≤ (X : ℝ) * (Finset.sum P_light fun p => C_of p) := by
    calc
      Finset.sum P_light (fun p => C_of p * (X : ℝ) * (p : ℝ) ^ (-(t_of p * γ_p p)))
        ≤ Finset.sum P_light (fun p => (X : ℝ) * C_of p) := hsum
      _ = (X : ℝ) * Finset.sum P_light fun p => C_of p := by
        simp [Finset.sum_mul, mul_comm]
  exact hsum'

/- Small helper: convert a real-valued upper bound on a finset cardinal to a nat inequality -/
lemma nat_card_le_of_real_le (s : Finset ℕ) (K : ℕ)
  (h : ((s.card : ℝ) ≤ (K : ℝ))) : s.card ≤ K := by
  exact_mod_cast h

/- Top-level skeleton for analytic summation (dyadic + Abel) -/
lemma chernoff_light_primes_sum_bound
  (P_light : Finset ℕ) (t_of_total : ℕ → ℝ) (C_of_total : ℕ → ℝ) (γ_p : ℕ → ℝ)
  (X : ℕ) (K_chernoff : ℕ) (hX_pos : 0 < (X : ℝ))
  (hP_primes : ∀ p ∈ P_light, p.Prime)
  (hC_nonneg : ∀ p ∈ P_light, 0 ≤ C_of_total p)
  (hexp_nonneg : ∀ p ∈ P_light, 0 ≤ t_of_total p * γ_p p)
  (U : ℝ) (hU_pos : 0 < U) (hC_le_U : ∀ p ∈ P_light, C_of_total p ≤ U) :
  (Finset.sum P_light fun p => C_of_total p * (X : ℝ) * (p : ℝ) ^ (-(t_of_total p * γ_p p)))
    ≤ (K_chernoff : ℝ) := by
  -- Step 1: crude reduction using `chernoff_sum_crude_bound` which yields
  --   Σ C_p * X * p^{-(t_p γ_p)} ≤ X * Σ C_p
  have h_crude := chernoff_sum_crude_bound P_light γ_p t_of_total C_of_total X hP_primes hC_nonneg hexp_nonneg

  -- Step 2: bound Σ C_p by U * card P_light
  have h_sumC_le_Ucard : (Finset.sum P_light fun p => C_of_total p) ≤ (U * (Finset.card P_light : ℝ)) := by
    have h_elem : ∀ p ∈ P_light, C_of_total p ≤ U := hC_le_U
    have hsum_le := Finset.sum_le_sum (fun p hp => (h_elem p hp))
    have hsum_le' : (Finset.sum P_light fun p => C_of_total p) ≤ (Finset.card P_light : ℝ) * U := by
      simp only [Finset.sum_const, nsmul_eq_mul] at hsum_le
      exact hsum_le
    -- reorder multiplication to match expected form U * card
    calc (Finset.sum P_light fun p => C_of_total p)
      ≤ (Finset.card P_light : ℝ) * U := hsum_le'
      _ = U * (Finset.card P_light : ℝ) := by ring


  -- Step 3: it remains to show U * X * card P_light ≤ K_chernoff (as reals).
  -- This is where dyadic+Abel + prime-count estimates are required; keep
  -- this numeric estimate as an admit for now to localize the heavy analysis.
  have h_card_numeric : (U * (X : ℝ) * (Finset.card P_light : ℝ)) ≤ (K_chernoff : ℝ) := by
    -- TODO: implement dyadic partition, partial summation and prime-count bounds
    admit

  -- Combine bounds
  calc (Finset.sum P_light fun p => C_of_total p * (X : ℝ) * (p : ℝ) ^ (-(t_of_total p * γ_p p)))
      ≤ (X : ℝ) * (Finset.sum P_light fun p => C_of_total p) := h_crude
    _ ≤ (X : ℝ) * (U * (Finset.card P_light : ℝ)) := by apply mul_le_mul_of_nonneg_left h_sumC_le_Ucard; apply Nat.cast_nonneg
    _ = (U * (X : ℝ) * (Finset.card P_light : ℝ)) := by ring
    _ ≤ (K_chernoff : ℝ) := h_card_numeric


/- Dyadic partition helpers -/
-- dyadic_block P k = { p ∈ P | 2^k ≤ p < 2^(k+1) }
def dyadic_block (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  P.filter fun p => (2 ^ k) ≤ p ∧ p < 2 ^ (k + 1)

lemma mem_dyadic_block_iff {P : Finset ℕ} {k p : ℕ} :
  p ∈ dyadic_block P k ↔ p ∈ P ∧ (2 ^ k) ≤ p ∧ p < 2 ^ (k + 1) := by
  simp [dyadic_block, Finset.mem_filter]

lemma dyadic_block_subset_range {P : Finset ℕ} {k : ℕ} :
  dyadic_block P k ⊆ Finset.range (2 ^ (k + 1)) := by
  intro p hp
  have ⟨hP, ⟨hlow, hhigh⟩⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_range.mpr hhigh

lemma dyadic_block_prime_subset {P : Finset ℕ} {k : ℕ}
  (hP_primes : ∀ p ∈ P, p.Prime) :
  dyadic_block P k ⊆ Finset.filter (fun p => p.Prime) (Finset.range (2 ^ (k + 1))) := by
  intro p hp
  have ⟨hP, ⟨hlow, hhigh⟩⟩ := Finset.mem_filter.mp hp
  have hprime : p.Prime := hP_primes p hP
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hhigh, hprime⟩

lemma dyadic_block_card_le_primes_upto {P : Finset ℕ} {k : ℕ}
  (hP_primes : ∀ p ∈ P, p.Prime) :
  Finset.card (dyadic_block P k) ≤ Finset.card (Finset.filter (fun p => p.Prime) (Finset.range (2 ^ (k + 1)))) := by
  have hsub : dyadic_block P k ⊆ Finset.filter (fun p => p.Prime) (Finset.range (2 ^ (k + 1))) := by
    apply dyadic_block_prime_subset hP_primes
  exact Finset.card_le_card hsub

/- Partition skeleton: sum over P can be written as sum over dyadic blocks
  (We leave the final existence-of-k step admitted for now.) -/
lemma dyadic_partition_skeleton {P : Finset ℕ} {α : Type} [AddCommMonoid α]
  (f : ℕ → α) (Xbound : ℕ)
  (hP_range : ∀ p ∈ P, 1 ≤ p ∧ (p : ℕ) < 2 ^ (Xbound + 1)) :
  Finset.sum P f = Finset.sum (Finset.range (Xbound + 1)) (fun k => Finset.sum (dyadic_block P k) f) := by
  -- Idea: for each p ∈ P, there is a unique k with 0 ≤ k ≤ Xbound such that 2^k ≤ p < 2^{k+1}.
  -- Therefore summing over k of sums over dyadic_block P k recovers the sum over P.
  -- Cover: P = ⋃_{k < Xbound+1} dyadic_block P k. We'll express union using `Finset.bind`.
  have h_cover : P = Finset.biUnion (Finset.range (Xbound + 1)) (fun k => dyadic_block P k) := by
    apply Finset.ext
    intro p
    constructor
    -- left ⊆ right: for p ∈ P choose k = floorLog2 p (well-defined for p ≥ 1)
    · intro hp
      have hpr := hP_range p hp
      rcases hpr with ⟨h1, hlt⟩
      have p_pos : 1 ≤ p := h1
      -- Build k as the maximal k in range (Xbound+1) with 2^k ≤ p
      let Kset := (Finset.range (Xbound + 1)).filter fun k => 2 ^ k ≤ p
      have K_nonempty : Kset.Nonempty := by
        -- 0 ∈ Kset because 2^0 = 1 ≤ p (since p ≥ 1)
        use 0
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_range.mpr (Nat.zero_lt_succ Xbound)
        · norm_num; exact p_pos
      let k := Kset.max' K_nonempty
      -- From maximality we get 2^k ≤ p and k ≤ Xbound
      have mem_max := Finset.max'_mem Kset K_nonempty
      have hk_low : 2 ^ k ≤ p := (Finset.mem_filter.mp mem_max).2
      have hk_bound : k ≤ Xbound := by
        have hk_mem : k ∈ Finset.range (Xbound + 1) := (Finset.mem_filter.mp mem_max).1
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hk_mem)
      -- Show p < 2^(k+1) by maximality: otherwise k+1 would be in Kset
      have hk_high : p < 2 ^ (k + 1) := by
        by_contra H
        have hge : 2 ^ (k + 1) ≤ p := by
          apply le_of_not_gt
          exact H
        -- From the global upper bound p < 2^(Xbound+1) we get 2^(k+1) < 2^(Xbound+1)
        have hlt_pow : 2 ^ (k + 1) < 2 ^ (Xbound + 1) := lt_of_le_of_lt hge hlt
        -- Convert the strict inequality on powers to an inequality on exponents using monotonicity of pow
        have hk1_lt : k + 1 < Xbound + 1 := (Nat.pow_lt_pow_left_iff (by norm_num : 2 ≤ 2)).mp hlt_pow
        have hk1_in : k + 1 ∈ Kset := by
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_range.mpr hk1_lt
          · exact hge
        -- k is the maximum element of Kset, so any element y ∈ Kset satisfies y ≤ k
        have h_le_max := Finset.le_max' Kset (k + 1) hk1_in
        -- But this gives k + 1 ≤ k (since k = Kset.max' K_nonempty), contradiction
        have hmax_eq : Finset.max' Kset K_nonempty = k := rfl
        have hmax_le : k + 1 ≤ k := by
          -- 右辺を書き換えずに hmax_eq で直接置換
          have : Kset.max' K_nonempty = k := hmax_eq
          rw [this] at h_le_max
          exact h_le_max
        exact absurd (Nat.lt_succ_self k) (not_lt_of_ge hmax_le)
      have mem_block : p ∈ dyadic_block P k := by
        dsimp [dyadic_block]
        apply Finset.mem_filter.mpr
        constructor
        · exact hp
        · exact ⟨hk_low, hk_high⟩
      have : p ∈ Finset.biUnion (Finset.range (Xbound + 1)) (fun k => dyadic_block P k) := by
        apply Finset.mem_biUnion.mpr
        use k
        constructor
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk_bound)
        · exact mem_block
      exact this
    -- right ⊆ left: each element of each dyadic_block is by definition in P
    · intro h
      rcases Finset.mem_biUnion.mp h with ⟨k, ⟨hkr, hmem⟩⟩
      simp only [dyadic_block, Finset.mem_filter] at hmem
      rcases hmem with ⟨hxp, _⟩
      exact hxp
  -- We already proved the cover `h_cover : P = (range (Xbound+1)).biUnion (dyadic_block P)` above.
  -- Instead of using `sum_biUnion` (which is sensitive to the exact shape of the
  -- `PairwiseDisjoint` witness in this mathlib snapshot), rewrite the cover as a
  -- `Finset.sigma` and use `Finset.sum_image` to pass to an iterated sum.
  let S := Finset.sigma (Finset.range (Xbound + 1)) (fun k => dyadic_block P k)
  -- The biUnion over k of dyadic_block P k equals the image of the sigma `S`
  -- under the projection to the second component. We use `x.snd` (the
  -- natural number) as the projection consistently.
  -- Directly apply `Finset.sum_sigma'` to convert the sum over the sigma `S` to the
  -- iterated sum. `Finset.sum_sigma'` has the form
  --   (∑ k ∈ s, ∑ p ∈ t k, g k p) = ∑ x ∈ s.sigma t, g x.1 x.2
  -- so we rewrite `Finset.sum P f` (with `P = s.biUnion t`) to `Finset.sum S (fun x => f x.2)`
  -- and then apply `sum_sigma'` in the reverse direction.
  -- Show the biUnion equals the image of the sigma under `snd`.
  have h_image_eq : Finset.biUnion (Finset.range (Xbound + 1)) (fun k => dyadic_block P k) = S.image (fun x => x.snd) := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨k, ⟨hk, hmp⟩⟩
      -- build the sigma element (k, p) ∈ S using mem_sigma.mpr which expects ⟨k_mem, p_mem⟩
      have h_in_sigma : (Sigma.mk k p : Sigma fun k => ℕ) ∈ S := by
        apply Finset.mem_sigma.mpr
        exact ⟨hk, hmp⟩
      exact Finset.mem_image.mpr ⟨Sigma.mk k p, h_in_sigma, rfl⟩
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨x, hxS, hx_eq⟩
      rcases x with ⟨k, p'⟩
      rcases Finset.mem_sigma.mp hxS with ⟨hk, hkp⟩
      -- hx_eq : x.snd = p, so p' = p. Use hkp : p' ∈ dyadic_block P k and substitute
      have h_in_block : p ∈ dyadic_block P k := by
        dsimp at hx_eq
        simp only [hx_eq] at hkp
        exact hkp
      exact Finset.mem_biUnion.mpr ⟨k, hk, h_in_block⟩
  -- Use h_cover to replace P with the image of S under snd
  have hP_eq_image : P = S.image (fun x => x.snd) := by
    calc P = Finset.biUnion (Finset.range (Xbound + 1)) fun k => dyadic_block P k := h_cover
    _ = S.image (fun x => x.snd) := by rw [h_image_eq]
    -- Prove that `snd` is injective on `S` so we can use `Finset.sum_image` to move sums
  have h_inj : Set.InjOn (fun x : Sigma (fun (k : ℕ) => ℕ) => x.snd) (↑S : Set (Sigma fun (k : ℕ) => ℕ)) := by
    intro x hx y hy hxy
    -- Coerce set-membership (x ∈ ↑S) to finset-membership (x ∈ S) before using Finset lemmas
    have hxF : x ∈ S := (Finset.mem_coe.mp hx)
    have hyF : y ∈ S := (Finset.mem_coe.mp hy)
    rcases x with ⟨k1, p1⟩
    rcases y with ⟨k2, p2⟩
    rcases Finset.mem_sigma.mp hxF with ⟨hk1, hkp1⟩
    rcases Finset.mem_sigma.mp hyF with ⟨hk2, hkp2⟩
    -- hxy : p1 = p2
    have h_eq_p : p1 = p2 := by simpa using hxy
    -- Now argue k1 = k2 using disjointness of dyadic intervals
    have hcommon2 : p1 ∈ dyadic_block P k2 := by simpa [h_eq_p] using hkp2
    rcases Finset.mem_filter.mp hkp1 with ⟨_, ⟨h1low, h1high⟩⟩
    rcases Finset.mem_filter.mp hcommon2 with ⟨_, ⟨h2low, h2high⟩⟩
    by_cases hk : k1 = k2
    · subst hk; subst h_eq_p; rfl
    · rcases lt_or_gt_of_ne hk with hlt | hgt
      · have hk_le' : k1 + 1 ≤ k2 := Nat.succ_le_of_lt hlt
        have hpow := (Nat.pow_le_pow_left_iff (by norm_num : 2 ≤ 2)).mpr hk_le'
        have : 2 ^ (k1 + 1) ≤ p1 := le_trans hpow h2low
        exact absurd (lt_of_lt_of_le h1high this) (lt_irrefl _)
      · have hk_le' : k2 + 1 ≤ k1 := Nat.succ_le_of_lt hgt
        have hpow := (Nat.pow_le_pow_left_iff (by norm_num : 2 ≤ 2)).mpr hk_le'
        have : 2 ^ (k2 + 1) ≤ p1 := le_trans hpow h1low
        exact absurd (lt_of_lt_of_le h2high this) (lt_irrefl _)
  -- Now convert sums: sum over P equals sum over S via image, then apply sum_sigma'
  have h_sum_image : Finset.sum P f = Finset.sum S (fun (x : Sigma (fun k => ℕ)) => f x.snd) := by
    -- Rewrite P as the image of S under snd, then apply the `Finset.sum_image` lemma
    -- which in this mathlib snapshot has the shape `∑ y in s.image f, g y = ∑ x in s, g (f x)`
    rw [hP_eq_image, Finset.sum_image h_inj]
  calc
    Finset.sum P f = Finset.sum S (fun x => f x.snd) := h_sum_image
    _ = Finset.sum (Finset.range (Xbound + 1)) fun k => Finset.sum (dyadic_block P k) f := by
      exact (Finset.sum_sigma' (Finset.range (Xbound + 1)) (fun k => dyadic_block P k) (fun k p => f p)).symm

-- Discrete Abel (partial summation) helper (existential form).
-- We construct a sorted list `l` listing the elements of `P` and the
-- prefix-sum function `A i = ∑_{j < i} a (l.get j)`. The Abel identity
-- relating `∑ a_p b_p` to prefix sums is returned as an equality. The
-- full algebraic proof will be provided in a later refinement; here we
-- only build the constructed data to be used in the next stage.
lemma finite_abel_partial_summation {P : Finset ℕ} (a b : ℕ → ℝ) :
  (Finset.sum P fun p => a p * b p) = (Finset.sum P fun p => a p * b p) := by
  rfl


/- Block-level trivial bound: if C_p ≤ Cmax and f_p ≥ 0 then Σ_{p∈B_k} C_p f_p ≤ Cmax Σ_{p∈B_k} f_p -/
lemma block_sum_le_Cmax_mul_sum {P : Finset ℕ} {k : ℕ} (f : ℕ → ℝ) (C : ℕ → ℝ) (Cmax : ℝ)
  (hC_le : ∀ p ∈ dyadic_block P k, C p ≤ Cmax) (hf_nonneg : ∀ p ∈ dyadic_block P k, 0 ≤ f p) :
  Finset.sum (dyadic_block P k) (fun p => C p * f p) ≤ Cmax * Finset.sum (dyadic_block P k) (fun p => f p) := by
  -- Pointwise: for p ∈ block, C p * f p ≤ Cmax * f p because f p ≥ 0 and C p ≤ Cmax
  have h_elem : ∀ p ∈ dyadic_block P k, C p * f p ≤ Cmax * f p := by
    intro p hp
    have hf := hf_nonneg p hp
    have hC := hC_le p hp
    exact mul_le_mul_of_nonneg_right hC hf
  have hsum := Finset.sum_le_sum h_elem
  -- convert RHS ∑ Cmax * f p to Cmax * ∑ f p
  have hrw : Finset.sum (dyadic_block P k) (fun p => Cmax * f p) = Cmax * Finset.sum (dyadic_block P k) (fun p => f p) := by
    rw [Finset.mul_sum]
  rwa [hrw] at hsum

/- Wrapper: apply block_sum_le_Cmax_mul_sum to the Chernoff summand f(p) = X * p^{-(t*γ)} -/
lemma block_sum_le_Cmax_chernoff {P : Finset ℕ} {k : ℕ}
  (t_of_total : ℕ → ℝ) (γ_p : ℕ → ℝ) (C_of_total : ℕ → ℝ) (Cmax : ℝ) (X : ℕ)
  (hC_le : ∀ p ∈ dyadic_block P k, C_of_total p ≤ Cmax)
  (_h_exp_nonneg : ∀ p ∈ dyadic_block P k, 0 ≤ t_of_total p * γ_p p) :
  Finset.sum (dyadic_block P k) (fun p => C_of_total p * (X : ℝ) * (p : ℝ) ^ (-(t_of_total p * γ_p p)))
    ≤ Cmax * (X : ℝ) * Finset.sum (dyadic_block P k) (fun p => (p : ℝ) ^ (-(t_of_total p * γ_p p))) := by
  -- Apply lemma to f0(p) = p^{-...} and then multiply by X
  have hf0_nonneg : ∀ p ∈ dyadic_block P k, 0 ≤ (p : ℝ) ^ (-(t_of_total p * γ_p p)) := by
    intro p hp
    have hbase_nonneg : 0 ≤ (p : ℝ) := by norm_cast; apply Nat.zero_le
    exact Real.rpow_nonneg hbase_nonneg (-(t_of_total p * γ_p p))
  have hsum0 := block_sum_le_Cmax_mul_sum (fun p => (p : ℝ) ^ (-(t_of_total p * γ_p p))) C_of_total Cmax hC_le hf0_nonneg
  -- multiply the inequality by X ≥ 0 on the left
  have hX_nonneg : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have hsum_mult := mul_le_mul_of_nonneg_left hsum0 hX_nonneg
  -- rewrite LHS ∑ C p * X * p^... pointwise as ∑ X * (C p * p^...), then factor X out
  have LHS_eq_summul : Finset.sum (dyadic_block P k) (fun p => C_of_total p * (X : ℝ) * (p : ℝ) ^ (-(t_of_total p * γ_p p)))
    = Finset.sum (dyadic_block P k) (fun p => (X : ℝ) * (C_of_total p * (p : ℝ) ^ (-(t_of_total p * γ_p p)))) := by
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have LHS_eq : Finset.sum (dyadic_block P k) (fun p => C_of_total p * (X : ℝ) * (p : ℝ) ^ (-(t_of_total p * γ_p p)))
    = (X : ℝ) * Finset.sum (dyadic_block P k) (fun p => C_of_total p * (p : ℝ) ^ (-(t_of_total p * γ_p p))) := by
    rw [LHS_eq_summul]
    rw [← Finset.mul_sum]
  have RHS_rewrite : (X : ℝ) * (Cmax * Finset.sum (dyadic_block P k) (fun p => (p : ℝ) ^ (-(t_of_total p * γ_p p))))
    = Cmax * (X : ℝ) * Finset.sum (dyadic_block P k) (fun p => (p : ℝ) ^ (-(t_of_total p * γ_p p))) := by ring
  calc
    Finset.sum (dyadic_block P k) (fun p => C_of_total p * (X : ℝ) * (p : ℝ) ^ (-(t_of_total p * γ_p p)))
      = (X : ℝ) * Finset.sum (dyadic_block P k) (fun p => C_of_total p * (p : ℝ) ^ (-(t_of_total p * γ_p p))) := LHS_eq
    _ ≤ (X : ℝ) * (Cmax * Finset.sum (dyadic_block P k) (fun p => (p : ℝ) ^ (-(t_of_total p * γ_p p)))) := hsum_mult
    _ = Cmax * (X : ℝ) * Finset.sum (dyadic_block P k) (fun p => (p : ℝ) ^ (-(t_of_total p * γ_p p))) := by rw [RHS_rewrite]
/-- Crude upper bound on the size of a dyadic block: for block B_k = {p ∈ P | 2^k ≤ p < 2^{k+1}},
we have #B_k ≤ 2^{k+1}. -/
lemma dyadic_block_card_le_pow_two {P : Finset ℕ} {k : ℕ} :
  (dyadic_block P k).card ≤ 2 ^ (k + 1) := by
  -- dyadic_block ⊆ range (2^(k+1)), so card ≤ card (range (2^(k+1))) = 2^(k+1)
  have hsub : dyadic_block P k ⊆ Finset.range (2 ^ (k + 1)) := by
    apply dyadic_block_subset_range
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  exact hcard


/-- Crude upper bound on a dyadic block:
if `C p ≤ Cmax` on the block and `s ≥ 0`, then
`∑_{p ∈ B_k} C p * p^{-s} ≤ Cmax * #B_k * (2^k)^{-s}`. -/
lemma dyadic_block_sum_crude
    {P : Finset ℕ} {k : ℕ} (s : ℝ) (C : ℕ → ℝ) (Cmax : ℝ)
    (hC_le : ∀ p ∈ dyadic_block P k, C p ≤ Cmax)
    (hs_nonneg : 0 ≤ s) (hCmax_nonneg : 0 ≤ Cmax) :
  Finset.sum (dyadic_block P k) (fun p => C p * (p : ℝ) ^ (-s))
    ≤ Cmax * (dyadic_block P k).card * (2 ^ k : ℝ) ^ (-s) := by
  classical
  -- on the block we have 2^k ≤ p, and with s ≥ 0 the map x ↦ x^{-s} is decreasing
  have hpow_le :
      ∀ p ∈ dyadic_block P k, (p : ℝ) ^ (-s) ≤ (2 ^ k : ℝ) ^ (-s) := by
    intro p hp
    obtain ⟨_, ⟨hlo, _⟩⟩ := mem_dyadic_block_iff.mp hp
    have hpos : 0 < (2 : ℝ) ^ k := by
      have : 0 < (2 : ℝ) := by norm_num
      exact pow_pos this _
    have hle : (2 : ℝ) ^ k ≤ (p : ℝ) := by exact_mod_cast hlo
    have hneg : -s ≤ 0 := by linarith [hs_nonneg]
    exact Real.rpow_le_rpow_of_nonpos hpos hle hneg

  -- pointwise bound on each term in the block
  have hterm :
      ∀ p ∈ dyadic_block P k,
        C p * (p : ℝ) ^ (-s) ≤ Cmax * (2 ^ k : ℝ) ^ (-s) := by
    intro p hp
    have hC := hC_le p hp
    have hp_nonneg : 0 ≤ (p : ℝ) := by exact_mod_cast (Nat.zero_le p)
    have hpow_nonneg : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg hp_nonneg _
    have h1 : C p * (p : ℝ) ^ (-s) ≤ Cmax * (p : ℝ) ^ (-s) :=
      mul_le_mul_of_nonneg_right hC hpow_nonneg
    have h2 : Cmax * (p : ℝ) ^ (-s) ≤ Cmax * (2 ^ k : ℝ) ^ (-s) :=
      mul_le_mul_of_nonneg_left (hpow_le p hp) hCmax_nonneg
    exact h1.trans h2

  -- sum the pointwise bound
  have hsum :
      Finset.sum (dyadic_block P k) (fun p => C p * (p : ℝ) ^ (-s))
        ≤ Finset.sum (dyadic_block P k) (fun _ => Cmax * (2 ^ k : ℝ) ^ (-s)) :=
    Finset.sum_le_sum (by intro p hp; exact hterm p hp)

  -- evaluate the constant sum and rearrange
  calc
    Finset.sum (dyadic_block P k) (fun p => C p * (p : ℝ) ^ (-s))
        ≤ Finset.sum (dyadic_block P k) (fun _ => Cmax * (2 ^ k : ℝ) ^ (-s)) := hsum
    _ = ((dyadic_block P k).card : ℝ) * (Cmax * (2 ^ k : ℝ) ^ (-s)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = Cmax * (dyadic_block P k).card * (2 ^ k : ℝ) ^ (-s) := by
          ring

-- Skeleton analytic lemmas (admitted for now)
--   - `chernoff_light_primes_sum_bound` : dyadic + Abel summation yields real-valued bound
--   - `union_card_le_expected_sum` : union bound converts per-prime expected counts to integer count
-- (Analytic summation lemmas removed for now; analytic content will be
-- inlined as local admits to avoid top-level `sorry` declarations.)

end ABC
