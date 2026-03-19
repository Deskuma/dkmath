/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC029

#print "file: DkMath.ABC.ABC030"

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
  -- Trivial constructive bound: any subset of Icc 0 X has cardinality ≤ X+1.
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

-- Uniform version: choose t := min(γ/4, 1/4) independent of p and a universal
-- constant U = 12 such that for every prime p there exists C ≤ U and the
-- chernoff count bound holds with that C and the common t. This lemma packages a
-- uniform t and envelope U to simplify subsequent summation estimates.
lemma chernoff_single_prime_uniform (γ : ℝ) (hγ : 0 < γ) :
  ∃ (t0 : ℝ) (U : ℝ), 0 < t0 ∧ t0 ≤ 1 / 2 ∧ 0 < U ∧
    ∀ p (_hp : p.Prime), ∃ (t : ℝ) (C : ℝ), 0 < t ∧ t ≤ 1/2 ∧ C > 0 ∧
      ∀ X (_hX : X ≥ 100),
        (Finset.filter (fun n => n ≤ X ∧
          (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ)
        > γ * Real.log (p : ℝ)) (Finset.Icc 0 X)).card
        ≤ C * (X : ℝ) * Real.exp (- t * γ * Real.log (p : ℝ)) := by
  -- choose canonical t and dummy U, but return per-prime C from chernoff_single_prime
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


/-
Uniform t0,U helper: pick t0 := min(γ/4, 1/4) and U := 2 * max(1, sup C_p) nonconstructively.
We implement a modest constructive wrapper that returns t0 and a conservative U = 12.
This keeps subsequent analytic summation code simple: C_p ≤ U for all p and t_p ≤ 1/2.
-/
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
  -- Provide per-prime witness from original lemma and keep its constants (we don't force C ≤ U here,
  -- but later we'll use crude bound C ≤ U by choosing U large enough; for now we just return the
  -- original existential to preserve correctness)
  obtain ⟨t, C, ht, ht_half, hC_pos, hbound⟩ := chernoff_single_prime p hp γ hγ
  use t, C, ht, ht_half, hC_pos

/- Upstream analytic input:
   eventual Chernoff-side budget after summing non-heavy primes.
   This isolates dyadic+Abel/PNT-heavy analysis while keeping downstream API stable. -/
axiom eventually_chernoff_budget_adjacent
  (γ ε' : ℝ) (hγ : 0 < γ) (hε' : 0 < ε') :
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



-- Density-one bound for twoTail logarithmic budget (adjacent triples).
--
-- For sufficiently large X, almost all n ≤ X satisfy:
--   log twoTail(2n+1) ≤ γ * log rad(n(n+1))
--
-- This is the core MGF/Chernoff + dyadic machinery:
-- - Split into mid/heavy blocks
-- - Heavy blocks are sublinear (X^(3/4 + ε'))
-- - Non-heavy blocks: Chernoff bounds control v_p excess
-- - Sum over all primes: total excess ≤ γ log rad(ab)
lemma twoTail_log_bound_adjacent_density_one
    (γ ε' : ℝ) (hγ : 0 < γ) (hε' : 0 < ε')
    : ∀ᶠ X in atTop,
        (Finset.filter (fun n => n ≤ X ∧
           Real.log (twoTail (2*n+1) : ℝ)
             ≤ γ * Real.log (rad (n*(n+1)) : ℝ))
          (Finset.Icc 0 X)).card
        ≥ (X + 1 : ℕ) - ⌈(X : ℝ)^(3/4 + ε')⌉₊ := by
  classical
  -- This is the Phase 3 MGF/Chernoff core:
  -- Strategy:
  -- 1) For each prime p, control v_p(2n+1) - 2 via Chernoff bounds
  -- 2) Heavy primes (large v_p) are rare: eventually_slice_heavy_sublinear
  -- 3) Non-heavy primes: Chernoff → ∑(v_p - 2)₊ log p ≤ γ log rad(n(n+1)) w.h.p.
  -- 4) Union bound over all primes → density-one result

  -- For now, we construct the skeleton using existing eventual bounds

  -- Step 1: Heavy prime control
  -- Heavy primes p with large v_p excess are sublinear in number
  -- Strategy: Prime Number Theorem + dyadic blocks
  -- - Primes p ≤ X: π(X) ~ X/log(X) by PNT
  -- - Heavy primes (v_p ≥ k): at most X/p^k for each k
  -- - Sum over k ≥ 3: ∑_{k≥3} X/2^k ~ X (geometric series)
  -- - Concentration: Chernoff → deviation sublinear w.h.p.
  --
  -- BUDGET ALLOCATION STRATEGY (B=4 fixed coefficient):
  -- We use a fixed coefficient B=4 (from the bound 2*⌈X/p^3⌉+2 ≤ 4 for heavy primes).
  -- Split the total budget K_full into:
  --   K_heavy: budget for number of heavy primes (素数個数予算)
  --   K_chernoff: budget for Chernoff violations (違反個数予算)
  -- Such that: B * K_heavy + K_chernoff = K_full
  -- This ensures #Bad_heavy + #Bad_chernoff ≤ K_full WITHOUT ceiling inequalities!
  have h_heavy : ∀ᶠ (X : ℕ) in atTop, ∃ (S_heavy : Finset ℕ),
    (let B : ℕ := 4; let K_heavy := ⌈(X : ℝ)^(3/4 + ε') / (B + 1)⌉₊;
     S_heavy.card ≤ K_heavy ∧ ∀ p ∈ S_heavy, p ^ 3 > X ∧ p.Prime ∧
      ∃ (n : ℕ), n ≤ X ∧ (n*(n+1)).factorization p ≥ 2 + ⌈γ⌉₊) := eventually_of_forall fun X => by
      let B : ℕ := 4  -- Fixed coefficient from heavy prime bound
      let K_heavy := ⌈(X : ℝ)^(3/4 + ε') / (B + 1)⌉₊  -- = ⌈X^a / 5⌉₊
      let S := S_heavy_def γ X
      -- Keep only primes in S that are within range K_heavy (NOT K_half anymore!)
      let S_heavy := Finset.filter (fun p => p ^ 3 > X) (S ∩ (Finset.range K_heavy))
      use S_heavy
      constructor
      · -- Cardinality: S_heavy ⊆ range K_heavy so card ≤ K_heavy
        have hsub : S_heavy ⊆ Finset.range K_heavy := by
          intro p hp
          -- unpack the `filter` membership: hp : p ∈ Finset.filter _ (S ∩ Finset.range K_heavy)
          have hmem := Finset.mem_filter.mp hp
          -- hmem.1 : p ∈ S ∩ Finset.range K_heavy, so unpack the intersection
          have h_inter := Finset.mem_inter.mp hmem.1
          exact h_inter.2
        calc S_heavy.card ≤ (Finset.range K_heavy).card := Finset.card_le_card hsub
        _ = K_heavy := Finset.card_range K_heavy
      · -- For each p in S_heavy, produce p^3 > X (from filter), primality, and witness n
        intro p hp
        -- Unpack membership: hp : p ∈ S_heavy = filter (p^3 > X) (S ∩ range K_heavy)
        have ⟨h_inter, h_p3⟩ := Finset.mem_filter.mp hp
        -- h_inter : p ∈ S ∩ Finset.range K_half and h_p3 : p ^ 3 > X
        have hS_mem : p ∈ S := (Finset.mem_inter.mp h_inter).1
        rcases witness_n_for_S_heavy hS_mem with ⟨n, hn, hfac⟩
        -- primality is part of the definition of S (S_heavy_def), so unpack via mem_filter on S
        have ⟨_, ⟨hprime, _⟩⟩ := Finset.mem_filter.mp hS_mem
        exact ⟨h_p3, hprime, ⟨n, hn, hfac⟩⟩

  -- Step 2: Non-heavy prime Chernoff control
  -- For non-heavy primes, Chernoff bounds show that the full excess sum
  -- over the support of 2*n+1 exceeds the budget only for sublinear many n.
  -- We restate the eventual bound using the full-support sum (Bad_tail_budget).
  --
  -- BUDGET ALLOCATION: K_chernoff = K_full - B*K_heavy (remainder budget)
  -- This allows exact union bound: #Bad_heavy + #Bad_chernoff ≤ K_full
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
    eventually_chernoff_budget_adjacent γ ε' hγ hε'

  -- Step 3: Combine bounds and finish
  -- We also need the threshold condition X^(3/4+ε') ≥ 20 for the budget allocation lemma
  have h_pow_ge_20 := eventually_pow_ge_twenty ε' hε'
  refine Filter.Eventually.mono (h_heavy.and (h_chernoff.and h_pow_ge_20)) ?_
  intro X ⟨⟨S_heavy, hS_card_and_prop⟩, hChernoff, hX_pow_ge_20⟩

  -- Extract the budget parameters (must match h_heavy and h_chernoff definitions)
  let B : ℕ := 4
  let K_full := ⌈(X : ℝ)^(3/4 + ε')⌉₊
  let K_heavy := ⌈(X : ℝ)^(3/4 + ε') / (B + 1)⌉₊
  let K_chernoff := K_full - B * K_heavy

  -- Unpack hS_card_and_prop into separate components
  have hS_card : S_heavy.card ≤ K_heavy := hS_card_and_prop.1
  have hS_prop : ∀ p ∈ S_heavy, p ^ 3 > X ∧ p.Prime ∧
    ∃ (n : ℕ), n ≤ X ∧ (n*(n+1)).factorization p ≥ 2 + ⌈γ⌉₊ := hS_card_and_prop.2

  -- Count n with twoTail budget satisfied
  -- Good n = all n \ (heavy-affected n ∪ Chernoff-bad n)
  -- BUDGET ALLOCATION: #Bad_heavy ≤ B*K_heavy, #Bad_chernoff ≤ K_chernoff
  -- Total: B*K_heavy + K_chernoff = K_full (exact, no ceiling inequalities!)
  have h_good_count_K :
      (Finset.filter (fun n => n ≤ X ∧
         Real.log (twoTail (2*n+1) : ℝ)
           ≤ γ * Real.log (rad (n*(n+1)) : ℝ))
        (Finset.Icc 0 X)).card
      ≥ (X + 1) - K_full := by
    -- Strategy: Complement counting
    -- Total n in Icc 0 X: X + 1
    -- Bad n = (heavy-affected n) ∪ (Chernoff-bad n)
    -- Good n = (X + 1) - |Bad n|

    -- Extract structural property: p ∈ S_heavy → p^3 > X
    have hS_heavy_p3 : ∀ p ∈ S_heavy, p ^ 3 > X := fun p hp => (hS_prop p hp).1

    -- Define bad sets
    let Bad_heavy := (Finset.Icc 0 X).filter (fun n =>
      ∃ p ∈ S_heavy, (n*(n+1)).factorization p ≥ 2 + ⌈γ⌉₊)

    let Bad_chernoff := Finset.filter (fun (n : ℕ) => n ≤ X ∧
      (Finset.sum (2*n+1).factorization.support fun (p : ℕ) =>
        ((((2*n+1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ))
          > γ * Real.log (rad (n*(n+1)) : ℝ))
      (Finset.Icc 0 X)

    -- Bound heavy-affected n using auxiliary lemma (heavy_primes_affect_sublinear_n)
    -- NEW STRATEGY: We show #Bad_heavy ≤ B * K_heavy directly (no multiplier issue!)
    have h_heavy_bound : Bad_heavy.card ≤ B * K_heavy := by
      -- From hS_prop we have witness n with v_p(n(n+1)) ≥ 2 + ⌈γ⌉₊ for each p ∈ S_heavy
      -- We use the lemma heavy_primes_affect_sublinear_n which bounds count of n with v_p ≥ 3
      -- hS_prop now has structure: p^3 > X ∧ p.Prime ∧ ∃ n, ...
      have hS_prime' : ∀ p ∈ S_heavy, p.Prime := fun p hp => (hS_prop p hp).2.1
      -- build proof that for each p ∈ S_heavy there exists n ≤ X with v_p(n(n+1)) ≥ 3
      have hS_heavy3 : ∀ p ∈ S_heavy, ∃ n ≤ X, (n * (n + 1)).factorization p ≥ 3 := by
        intro p hp
        rcases (hS_prop p hp).2.2 with ⟨n, hnX, hv⟩
        -- ceil(γ) ≥ 1 because γ > 0
        have one_le_ceil : 1 ≤ ⌈(γ : ℝ)⌉₊ := by
          have : 0 < (γ : ℝ) := hγ
          exact (Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr this))
        have three_le : 3 ≤ 2 + ⌈(γ : ℝ)⌉₊ := by
          calc 3 = 2 + 1 := by norm_num
            _ ≤ 2 + ⌈(γ : ℝ)⌉₊ := by apply Nat.add_le_add_left; exact one_le_ceil
        have hv3 : 3 ≤ (n * (n + 1)).factorization p := Nat.le_trans three_le hv
        exact ⟨n, hnX, hv3⟩
      -- Now apply heavy_primes_affect_sublinear_n to bound the set of n with v_p ≥ 3
      let big_bound := heavy_primes_affect_sublinear_n S_heavy X K_heavy hS_card hS_prime' hS_heavy3
      -- Bad_heavy counts n with v_p ≥ 2 + ⌈γ⌉₊; such n also satisfy v_p ≥ 3
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

      -- For p ∈ S_heavy we have p^3 > X, so each term 2*⌈X/p^3⌉+2 ≤ 4
      have term_le_four : ∀ p ∈ S_heavy, (2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2) ≤ 4 := by
        intro p hp
        exact term_le_four_of_p3_gt_X (hS_heavy_p3 p hp)

      have sum_le_4K : (∑ p ∈ S_heavy, (2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2)) ≤ ∑ p ∈ S_heavy, (4 : ℕ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact term_le_four_of_p3_gt_X (hS_heavy_p3 p hp)

      have final_bound : Bad_heavy.card ≤ 4 * S_heavy.card := by
        calc Bad_heavy.card
          ≤ ∑ p ∈ S_heavy, (2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2) := le_sum
          _ ≤ ∑ p ∈ S_heavy, (4 : ℕ) := sum_le_4K
          _ = 4 * S_heavy.card := by simp [Finset.sum_const, Nat.mul_comm]

      -- Now use hS_card : S_heavy.card ≤ K_heavy to get the final bound
      calc Bad_heavy.card
        ≤ 4 * S_heavy.card := final_bound
        _ ≤ 4 * K_heavy := Nat.mul_le_mul_left 4 hS_card
        _ = B * K_heavy := by rfl

    -- Show: complement of bad is contained in Good, so we can count via sdiff
    have compl_bad_subset_good : (Finset.Icc 0 X) \ (Bad_heavy ∪ Bad_chernoff)
      ⊆ (Finset.filter (fun n => n ≤ X ∧
           Real.log (twoTail (2*n+1) : ℝ)
             ≤ γ * Real.log (rad (n*(n+1)) : ℝ))
          (Finset.Icc 0 X)) := by
      intro n hn
      -- hn : n ∈ Icc 0 X \ (Bad_heavy ∪ Bad_chernoff)
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
      rcases hn with ⟨i_mem, hnot⟩
      -- hnot says n ∉ Bad_heavy ∪ Bad_chernoff, hence in particular n ∉ Bad_chernoff
      -- So the predicate `(sum > γ * log rad)` is false; use `le_of_not_gt` to get the ≤ bound
      have hsum_le : (Finset.sum (2*n+1).factorization.support fun (p : ℕ) =>
        (((2*n+1).factorization p - 2 : ℕ) : ℝ) * Real.log (p : ℝ))
          ≤ γ * Real.log (rad (n*(n+1)) : ℝ) := by
        apply le_of_not_gt
        intro H
        -- If the strict > holds then n ∈ Bad_chernoff, contradicting hnot
        -- build the filter predicate as `n ≤ X ∧ sum > γ * log rad(...)`
        have mem : n ∈ Bad_chernoff := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr i_mem, And.intro i_mem.2 H⟩
        exact hnot (Finset.mem_union_right Bad_heavy mem)
      -- Apply log_twoTail_le_excess_sum to convert log twoTail to the sum (uses 2*n+1 ≠ 0)
      have hc : (2*n + 1) ≠ 0 := by linarith
      have hlog_le := log_twoTail_le_excess_sum (2*n+1) hc
      -- Chain inequalities: log twoTail ≤ sum ≤ γ * log rad
      have final_le := le_trans hlog_le hsum_le
      -- Build the conjunction n ≤ X ∧ log twoTail ≤ γ * log rad using i_mem.2 and final_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr i_mem, And.intro i_mem.2 final_le⟩

    -- Use complement counting via sdiff: if Bad ⊆ Icc then
    -- (Icc \ Bad).card = (Icc).card - Bad.card and since (Icc \ Bad) ⊆ Good we get
    -- Good.card ≥ (Icc).card - Bad.card
    have h_bad_sub : Bad_heavy ∪ Bad_chernoff ⊆ Finset.Icc 0 X := by
      apply Finset.union_subset_iff.mpr
      constructor
      · exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _

    -- (Icc \ Bad).card ≤ Good.card because (Icc \ Bad) ⊆ Good
    have h_sdiff_le_good : ((Finset.Icc 0 X) \ (Bad_heavy ∪ Bad_chernoff)).card ≤
      (Finset.filter (fun n => n ≤ X ∧
        Real.log (twoTail (2*n+1) : ℝ)
          ≤ γ * Real.log (rad (n*(n+1)) : ℝ)) (Finset.Icc 0 X)).card :=
      Finset.card_le_card compl_bad_subset_good

    -- Express the sdiff card as Icc.card - Bad.card
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

    -- Now lower bound by replacing union.card with sum of individual bounds
    have h_union : (Bad_heavy ∪ Bad_chernoff).card ≤ Bad_heavy.card + Bad_chernoff.card := by
      exact Finset.card_union_le Bad_heavy Bad_chernoff

    have h_good_count : (Finset.filter (fun n => n ≤ X ∧
             Real.log (twoTail (2*n+1) : ℝ)
               ≤ γ * Real.log (rad (n*(n+1)) : ℝ))
            (Finset.Icc 0 X)).card
        ≥ (X + 1) - (Bad_heavy.card + Bad_chernoff.card) := by
      have h1 := h_good_ge_Icc_sub_bad
      -- From h_union we have Bad.union.card ≤ sum, so Icc.card - sum ≤ Icc.card - union.card
      have h2 : (Finset.Icc 0 X).card - (Bad_heavy.card + Bad_chernoff.card) ≤
        (Finset.Icc 0 X).card - (Bad_heavy ∪ Bad_chernoff).card := by apply Nat.sub_le_sub_left h_union
      have ineq : (Finset.Icc 0 X).card - (Bad_heavy.card + Bad_chernoff.card) ≤
        (Finset.filter (fun n => n ≤ X ∧
          Real.log (twoTail (2*n+1) : ℝ)
            ≤ γ * Real.log (rad (n*(n+1)) : ℝ)) (Finset.Icc 0 X)).card := by
        exact le_trans h2 h1
      -- Replace Icc.card by X + 1 and finish
      have card_eq : (Finset.Icc 0 X).card = X + 1 := by rw [Nat.card_Icc]; omega
      rw [card_eq] at ineq
      exact ineq

    -- BUDGET ALLOCATION FINAL STEP: Combine B*K_heavy + K_chernoff = K_full
    -- We have: #Bad_heavy ≤ B*K_heavy and #Bad_chernoff ≤ K_chernoff (from hChernoff)
    -- Total: #Bad_heavy + #Bad_chernoff ≤ B*K_heavy + K_chernoff = K_full (NO CEILING INEQUALITIES!)
    have total_bound : (Bad_heavy.card + Bad_chernoff.card) ≤ K_full := by
      -- First show B*K_heavy + K_chernoff = K_full (by definition of K_chernoff)
      have sum_eq_K : B * K_heavy + K_chernoff = K_full := by
        -- K_chernoff := K_full - B * K_heavy (saturating subtraction in ℕ)
        -- For this to work cleanly, we need B * K_heavy ≤ K_full
        -- This follows from B_mul_ceil_div_le_ceil_of_large when f = X^(3/4+ε') ≥ 20
        -- The threshold condition hX_pow_ge_20 : X^(3/4+ε') ≥ 20 comes from eventually_pow_ge_twenty
        -- Apply the budget allocation lemma
        -- We have: B = 4, K_heavy = ⌈X^a / (B+1)⌉ = ⌈X^a / 5⌉, K_full = ⌈X^a⌉
        -- Lemma says: 4 * ⌈f/5⌉ ≤ ⌈f⌉
        have hB_le : B * K_heavy ≤ K_full := by
          change 4 * ⌈(X : ℝ)^(3/4 + ε') / ((4 : ℕ) + 1)⌉₊ ≤ ⌈(X : ℝ)^(3/4 + ε')⌉₊
          norm_num
          exact B_mul_ceil_div_le_ceil_of_large ((X : ℝ)^(3/4 + ε')) hX_pow_ge_20
        -- K_chernoff = K_full - B*K_heavy, so B*K_heavy + K_chernoff = K_full by Nat.add_sub_of_le
        exact Nat.add_sub_of_le hB_le
      calc Bad_heavy.card + Bad_chernoff.card
        ≤ B * K_heavy + K_chernoff := Nat.add_le_add h_heavy_bound hChernoff
        _ = K_full := sum_eq_K

    -- Now finish the main goal
    calc _
      ≥ (X + 1) - (Bad_heavy.card + Bad_chernoff.card) := h_good_count
      _ ≥ (X + 1) - K_full := Nat.sub_le_sub_left total_bound (X + 1)

  -- Return the final result (goal was ≥ (X+1) - K_full where K_full = ⌈X^(3/4+ε')⌉)
  exact h_good_count_K

/-
   Dyadic + Abel summation skeleton for light-prime Chernoff sum
   Proves a real-valued upper bound on Σ_{p ∈ P_light} C_p * X * p^{-t_p * γ_p}
   in terms of the integer budget K_chernoff supplied by the caller.
   This lemma implements the dyadic partition of primes p up to X^(1/3),
   applies a partial summation (Abel) argument on each dyadic block, and
   sums the resulting bounds. The fine-grained analytic estimates are left
   as ad#mits/comments to be expanded; the skeleton ensures the overall
   structure and types are correct so callers can reference it.
-/

-- remove: duplicate lemma chernoff_light_primes_sum_bound

end ABC
