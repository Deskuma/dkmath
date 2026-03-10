/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC027

#print "file: DkMath.ABC.ABC028"

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

/-  ### Phase 3: MGF (Moment Generating Function) and Chernoff Machinery

This section develops the probabilistic tools for controlling p-adic excess.

#### Core Idea
For a prime p and random n ≤ X, the p-adic valuation v_p(2n+1) behaves like
a geometric random variable. We use MGF to bound tail probabilities.

#### Key Definitions
- **MGF**: E[e^{t(v_p - 2)}] for parameter t > 0
- **Chernoff bound**: Pr[v_p - 2 > threshold] ≤ e^{-t*threshold} * MGF(t)
- **Optimal t**: Chosen to minimize the Chernoff bound

#### Implementation Status
Currently using `so#rry` placeholders. Full implementation requires:
1. Explicit MGF computation for geometric distribution
2. Optimal t parameter selection (balancing e^{-t*threshold} and MGF(t))
3. Union bound over primes with careful budget allocation
-/

-- MGF upper bound for v_p(2n+1) - 2
-- For a prime p, the excess v_p(2n+1) - 2 has geometric-like distribution
-- This lemma provides an explicit upper bound on E[e^{t(v_p - 2)}]
--
-- ★ CORE VERSION: p^t base (easier to work with for Chernoff)
lemma mgf_padic_excess_bound_pbase
  (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
  ∃ C > 0, ∀ X ≥ 1,
    (Finset.sum (Finset.Icc 0 X)
      (fun n => (p : ℝ) ^ (t * ((padicValNat p (2*n+1) : ℤ) - 2)))) / (X + 1) ≤ C := by
  classical
  -- Strategy: Use periodicity of p^k | (2n+1) + layer-cake representation
  --
  -- Step 1: p odd ⟹ 2 invertible in ℤ/p^kℤ ⟹ unique solution mod p^k
  --   count_powers_dividing_2n1 gives #{n≤X : p^k | 2n+1} ≤ ⌈(X+1)/p^k⌉
  --
  -- Step 2: Layer-cake decomposition (from ABCTailHelpers)
  --   ∑ p^{t(v-2)} = ∑ p^{-2t} * p^{tv}
  --                ≤ p^{-2t} * [(X+1) + (p^t - 1) * ∑_{k≥1} p^{t(k-1)} * #{v≥k}]
  --
  -- Step 3: Geometric series (ratio r = p^{t-1})
  --   ∑_{k≥1} p^{t(k-1)} * ⌈(X+1)/p^k⌉ ≤ (X+1) * ∑_{k≥1} p^{t(k-1)} / p^k
  --                                      = (X+1) * ∑_{k≥1} r^k
  --                                      = (X+1) * r/(1-r)  (for r < 1)
  --
  -- Step 4: Convergence condition
  --   r = p^{t-1} < 1 ⟺ t < 1
  --   For t ≤ 1/2 and p ≥ 3: r ≤ 3^{-1/2} ≈ 0.577 < 1 ✓
  --
  -- Step 5: Explicit constant
  --   C = p^{-2t} * [1 + (p^t - 1) * r/(1-r)]
  --     = p^{-2t} * [1 + (p^t - 1) * p^{t-1}/(1 - p^{t-1})]
  --   For t = 1/2, p = 3: C ≈ 3^{-1} * [1 + (√3 - 1) * (1/√3)/(1 - 1/√3)] ≈ 0.6
  --   Upper bound: C ≤ 4 * p^{-2t} for t ≤ 1/2, p ≥ 3
  --
  -- Implementation: Use count_powers_dividing_2n1 + layer-cake expansion
  classical
  -- Step A: Define parameters and establish basic bounds
  let r := (p : ℝ) ^ (t - 1)
  have hr_pos : 0 < r := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) _
  have hr_lt_one : r < 1 := by
    -- r = p^{t-1} where p ≥ 3 and t ≤ 1/2
    -- So t - 1 ≤ -1/2, hence p^{t-1} ≤ p^{-1/2} ≤ 3^{-1/2} < 1
    have ht_neg : t - 1 ≤ -1/2 := by linarith
    have hp_ge_3 : 3 ≤ p := by
      by_contra h
      push_neg at h
      -- h : p < 3, so p ∈ {0, 1, 2}
      -- p is prime, so p ≥ 2
      have hp2 : 2 ≤ p := hp.two_le
      -- Combining: 2 ≤ p < 3 means p = 2
      have : p = 2 := by omega
      exact hpodd this
    -- Use simplified bound: for p > 1 and t - 1 < 0, we have 0 < p^{t-1} < 1
    have : (p : ℝ) ^ (t - 1) < 1 := by
      have h_neg : t - 1 < 0 := by linarith
      have hp_gt_1 : (1 : ℝ) < (p : ℝ) := by norm_cast; exact hp.one_lt
      -- For x > 1 and exp < 0, we have 0 < x^exp < 1
      have : (0 : ℝ) < (p : ℝ) ^ (t - 1) := Real.rpow_pos_of_pos (by linarith : 0 < (p : ℝ)) _
      have : (p : ℝ) ^ (t - 1) = ((p : ℝ) ^ (1 - t))⁻¹ := by
        rw [← Real.rpow_neg (by linarith : 0 ≤ (p : ℝ))]
        congr 1
        ring
      rw [this]
      have : 1 < (p : ℝ) ^ (1 - t) := by
        apply Real.one_lt_rpow hp_gt_1
        linarith
      -- 1 < x なら 1/x < 1
      have h_inv_lt_one : 1 < (p : ℝ) ^ (1 - t) → ((p : ℝ) ^ (1 - t))⁻¹ < 1 := by
        intro h
        -- 1 < ↑p ^ (1 - t) なら 1 / ↑p ^ (1 - t) < 1 となる（逆数は単調減少）
        have hdiv : 1 / ((p : ℝ) ^ (1 - t)) < 1 := by
          rw [div_lt_one]
          · exact h
          · exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) (1 - t)
        -- 1 / x = x⁻¹ を使って型を合わせる
        rw [inv_eq_one_div]
        exact hdiv
      exact h_inv_lt_one this
    exact this

  -- Step B: Establish constant C
  -- C := p^{-2t} * (1 + (p^t - 1) * r / (1 - r) + 1)
  -- Using ABCTelescoping.sum_pow_padicValNat_le_geom: ∑ p^{tv(n)} ≤ 3(X+1)
  -- So we need C = 6 * p^{-2t} to get ∑ p^{t(v-2)} ≤ 6 * p^{-2t} * (X+1) / (X+1) = C
  let C := 6 * (p : ℝ) ^ (-2 * t)
  have hC_pos : 0 < C := by
    apply mul_pos
    · norm_num
    · exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) _

  use C, hC_pos
  intro X hX

  -- Step C: Layer-cake expansion
  -- Σ_n p^{t(v(n)-2)} = p^{-2t} * Σ_n p^{t·v(n)}
  --                   = p^{-2t} * Σ_{k≥0} p^{t(k-1)} * #{n : v(n) ≥ k}
  --                   ≤ p^{-2t} * [ Σ_{k=0} p^{-t} + Σ_{k≥1} p^{t(k-1)} * ⌈(X+1)/p^k⌉ ]

  -- Use count_powers_dividing_2n1 for each k ≥ 1
  have h_count : ∀ k ≥ 1, (Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X)).card
      ≤ ⌈(((X+1) : ℕ) : ℝ) / (p^k : ℝ)⌉₊ := by
    intro k hk
    convert count_powers_dividing_2n1 p hp hpodd k hk X using 2
    norm_cast

  -- Step D: Proper geometric series bound using count_powers_dividing_2n1
  -- Strategy: Use layer-cake formula
  -- Σ_n p^{tv} = Σ_{k=0}^∞ #{n : v(n) ≥ k} * (p^{tk} - p^{t(k+1)})
  --            = Σ_{k=0}^∞ #{n : p^k | 2n+1} * p^{tk} * (1 - p^t)
  -- where #{n : p^k | 2n+1} ≤ ⌈(X+1)/p^k⌉ by count_powers_dividing_2n1

  change (Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * ((padicValNat p (2*n+1) : ℤ) - 2))) / (X + 1) ≤ C

  -- Simpler approach: Just use monotonicity and direct calculation
  -- Note: For p ≥ 3, t ≤ 1/2, we have specific numerical bounds
  -- The key is that Σ_{k≥1} (X+1)/p^k * p^{t(k-1)} is bounded

  -- Actually, let's use an even simpler observation:
  -- Fix a large enough K (say K = 100). For k ≤ K, use count bound.
  -- For k > K, the contribution is negligible.

  -- Most direct: Bound using the fact that sum converges
  -- Σ_n p^{t(v-2)} = p^{-2t} * Σ_n p^{tv}
  -- Now Σ_n p^{tv} ≤ Σ_{k=0}^∞ (X+1+1) * p^{tk} / p^{k}  (crude: all n might have v=k)
  --                ≤ (X+2) * Σ_{k=0}^∞ (p^{t-1})^k
  --                = (X+2) / (1 - p^{t-1})
  --                ≤ (X+2) * 2  (since p^{t-1} ≤ 1/2)

  -- Therefore average ≤ 2 * p^{-2t} * (X+2)/(X+1) ≤ 4 * p^{-2t}

  -- Step D1: Apply ABCTelescoping theorem
  -- Use ABCTelescoping.sum_pow_padicValNat_le_geom: ∑ p^{tv(n)} ≤ 3(X+1)
  have hp_ge_3 : 3 ≤ p := by
    by_contra h
    push_neg at h
    -- h : p < 3, so p ∈ {0, 1, 2}
    have hp2 : 2 ≤ p := hp.two_le
    interval_cases p
    · omega -- p = 2, but hpodd says p ≠ 2

  have h_sum_bound : Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ)))
      ≤ 3 * (X + 1) := by
    -- Apply ABCTelescoping theorem directly (signature matches!)
    have hp_inst : Fact p.Prime := ⟨hp⟩
    exact @ABC.Telescoping.sum_pow_padicValNat_le_geom_half p hp_inst hp_ge_3 t ht0 ht X hX

  -- Step D2: Apply the bound
  have h_factor : (Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * ((padicValNat p (2*n+1) : ℤ) - 2)))
      = (p : ℝ) ^ (-2 * t) * (Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ))) := by
    rw [Finset.mul_sum]
    congr 1
    ext n
    have : t * ((padicValNat p (2*n+1) : ℤ) - 2)
         = -2 * t + t * (padicValNat p (2*n+1) : ℤ) := by ring
    rw [this, Real.rpow_add (by norm_cast; exact hp.pos)]

  rw [h_factor, mul_div_assoc]

  -- Now: goal is p^{-2t} * (∑ p^{tv} / (X+1)) ≤ C = 6 * p^{-2t}
  -- We have: ∑ p^{tv} ≤ 3(X+1) from h_sum_bound
  -- So: ∑ p^{tv} / (X+1) ≤ 3
  have h_ineq1 : (Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ))) / (X + 1)
      ≤ 3 := by
    -- divide both sides of h_sum_bound by X+1 > 0
    have hpos : 0 < (X + 1 : ℝ) := by norm_cast; omega
    exact (Real.div_le_iff hpos).mpr h_sum_bound

  -- Final application: p^{-2t} * 3 = 3 * p^{-2t} ≤ 6 * p^{-2t} = C
  change (p : ℝ) ^ (-2 * t) * ((Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ))) / (X + 1)) ≤ C
  calc (p : ℝ) ^ (-2 * t) * ((Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ))) / (X + 1))
      ≤ (p : ℝ) ^ (-2 * t) * 3 := by
        apply mul_le_mul_of_nonneg_left h_ineq1
        apply Real.rpow_nonneg
        norm_cast; omega
    _ = 3 * (p : ℝ) ^ (-2 * t) := by ring
    _ ≤ 6 * (p : ℝ) ^ (-2 * t) := by linarith
    _ = C := rfl



-- ========================================================================
-- Layer-cake representation for real power of integer-valued function
-- ∑ a^{t V(n)} ≤ (X+1) + (a^t - 1) * ∑_{k≥1} a^{t(k-1)} * #{n | V(n) ≥ k}
-- Bounded version: assumes V n ≤ X+1 for all n ≤ X
-- This is the rpow analogue of exp_layer_cake, useful for p-adic MGF bounds
-- ========================================================================
-- MathlibHello/ABCFinalWorking.lean で作業中



-- Special case: p = 2 (trivial, always v_2(2n+1) = 0)
lemma mgf_padic_excess_bound_two (t : ℝ) (_ht : 0 < t) :
  ∃ C > 0, ∀ X ≥ 1,
    (Finset.sum (Finset.Icc 0 X)
      (fun n => Real.exp (t * ((padicValNat 2 (2*n+1) : ℤ) - 2)))) / (X+1) ≤ C := by
  -- v_2(2n+1) = 0 for all n (padic_val_two_of_odd)
  -- So exp(t * (0 - 2)) = exp(-2t) = constant
  use Real.exp (-2 * t)
  constructor
  · exact Real.exp_pos _
  · intro X _
    -- Sum is (X+1) * exp(-2t), so average is exp(-2t)
    -- v_2(2n+1) = 0 always (odd number)
    have h_all_zero : ∀ n ∈ Finset.Icc 0 X, Real.exp (t * ((padicValNat 2 (2*n+1) : ℤ) - 2)) = Real.exp (-2 * t) := by
      intro n _
      simp [padic_val_two_of_odd]
      ring_nf
    rw [show (Finset.sum (Finset.Icc 0 X) fun n => Real.exp (t * ((padicValNat 2 (2*n+1) : ℤ) - 2)))
          = Finset.sum (Finset.Icc 0 X) (fun _ => Real.exp (-2 * t)) by
        apply Finset.sum_congr rfl h_all_zero]
    rw [Finset.sum_const]
    -- Goal: card(Icc 0 X) • exp(-2t) / (X+1) ≤ exp(-2t)
    -- card(Icc 0 X) = X + 1, so LHS simplifies to exp(-2t)
    have h_card : (Finset.Icc 0 X).card = X + 1 := by
      rw [Nat.card_Icc]
      omega
    rw [h_card]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [show ((X + 1 : ℝ) * Real.exp (-2 * t) / (X + 1)) = Real.exp (-2 * t) by field_simp]

-- Original exp-base version (follows from p-base version)
lemma mgf_padic_excess_bound_le_C (p : ℕ) (hp : p.Prime) (t : ℝ) (ht : 0 < t) (ht_small : t < Real.log 2 / 2) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (X : ℕ) (_hX : X ≥ 100),
      ( Finset.sum (Finset.Icc 0 X) fun n
        => Real.exp (t * (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ)) ) / (X + 1)
      ≤ C := by
  -- Strategy (SIMPLIFIED with p-base version):
  -- 1. Split into p=2 (trivial) and p≥3 (use mgf_padic_excess_bound_pbase)
  -- 2. For p=2: use mgf_padic_excess_bound_two
  -- 3. For p≥3: Convert exp(t * v) = p^{t'/v} with t' = t/log p
  --    Requires t' ≤ 1/2, i.e., t ≤ (log p)/2
  --    With t < (log 2)/2 and p≥3: t < (log 2)/2 < (log 3)/2 ≤ (log p)/2 ✓
  --
  -- Corollary proof is ~5 lines using mgf_padic_excess_bound_pbase
  by_cases h2 : p = 2
  · -- p = 2 case
    subst h2
    obtain ⟨C, hC_pos, hC_bound⟩ := mgf_padic_excess_bound_two t ht
    use C, hC_pos
    intro X hX
    -- Type conversion: goal vs hC_bound differ in cast placement
    -- Goal: (((n : ℤ) - 2) : ℝ)  vs  hC_bound: ((n : ℤ) - 2 : ℝ)
    -- These should be definitionally equal, but convert is safer
    convert hC_bound X (by omega : X ≥ 1) using 2
    -- Now need to show sum equality
    apply Finset.sum_congr rfl
    intro n _
    -- Show: exp(t * (((n:ℤ) - 2):ℝ)) = exp(t * ((n:ℤ) - 2))
    -- The issue is ↑2 vs 2
    norm_num
  · -- p ≥ 3 case: use p-base version with t' = t / log p
    -- Convert exp(t*v) to p^{t'*v} where t' = t/log(p)
    let t' := t / Real.log p

    -- Verify conditions for mgf_padic_excess_bound_pbase
    have ht'_pos : 0 < t' := by
      apply div_pos ht
      apply Real.log_pos
      have hp3 : 3 ≤ p := by
        by_contra h_not; push_neg at h_not
        have hp2 : 2 ≤ p := hp.two_le
        have : p = 2 := by omega
        exact h2 this
      have : 1 < (p : ℝ) := by
        have : 2 < p := by omega
        have : (1 : ℝ) < 2 := by norm_num
        calc (1 : ℝ) < 2 := this
          _ < p := Nat.cast_lt.mpr ‹2 < p›
      exact this

    have ht'_half : t' ≤ 1 / 2 := by
      -- Need: t / log(p) ≤ 1/2, i.e., 2*t ≤ log(p)
      -- We have: t < (log 2)/2, so 2*t < log 2
      -- For p≥3: log 2 < log 3 ≤ log p
      -- Therefore: 2*t < log 2 < log p, so t' = t/log(p) < (log 2)/(2·log p) < 1/2
      have hp3 : 3 ≤ p := by
        by_contra h_not; push_neg at h_not
        have hp2 : 2 ≤ p := hp.two_le
        have : p = 2 := by omega
        exact h2 this
      have hlog_pos : 0 < Real.log p := by
        have : (1 : ℝ) < p := by
          have : 1 < p := hp.one_lt
          exact Nat.one_lt_cast.mpr this
        exact Real.log_pos this
      -- multiply both sides by positive log p: use Real.div_le_iff
      apply (Real.div_le_iff hlog_pos).mpr
      -- show t ≤ Real.log p / 2 by strict inequalities
      apply le_of_lt
      have h_log2_lt_logp : Real.log 2 < Real.log p := by
        have : (2 : ℝ) < p := by
          have : 2 < p := hp3
          exact Nat.cast_lt.mpr this
        exact Real.log_lt_log (by norm_num) this
      calc t < Real.log 2 / 2 := ht_small
        _ < Real.log p / 2 := by
          apply div_lt_div_of_pos_right h_log2_lt_logp
          norm_num
        _ = 1 / 2 * Real.log p := by ring

    -- Apply p-base version
    obtain ⟨C, hC_pos, hC_bound⟩ := mgf_padic_excess_bound_pbase p hp h2 t' ht'_pos ht'_half
    use C, hC_pos
    intro X hX

    -- Get hlog_pos from ht'_half proof
    have hlog_pos : 0 < Real.log p := by
      have : (1 : ℝ) < p := by
        have : 1 < p := hp.one_lt
        exact Nat.one_lt_cast.mpr this
      exact Real.log_pos this

    -- Convert exp to p-base: exp(t*v) = p^{t'*v}
    convert hC_bound X (by omega : X ≥ 1) using 2
    apply Finset.sum_congr rfl
    intro n _
    -- Show: exp(t * ((v - 2):ℝ)) = p^{t' * ((v - 2):ℤ)}
    -- Key identity: p^x = exp(x * log p)
    have hp_pos : 0 < (p : ℝ) := by
      have : 0 < p := hp.pos
      exact Nat.cast_pos.mpr this
    rw [Real.rpow_def_of_pos hp_pos]
    congr 1
    -- Show: t * ((v-2):ℝ) = t' * ((v-2):ℤ) * log p
    -- where t' = t / log p
    -- First, unify 2*n+1 and 1+n*2
    have h_eq : (2 * n + 1 : ℕ) = 1 + n * 2 := by omega
    rw [h_eq]
    have : t' * (((padicValNat p (1 + n * 2)) - 2 : ℤ) : ℝ) * Real.log p
         = t * (((padicValNat p (1 + n * 2)) - 2 : ℤ) : ℝ) := by
      rw [show t' = t / Real.log p by rfl]
      have hlog_ne : Real.log p ≠ 0 := ne_of_gt hlog_pos
      field_simp [hlog_ne]
    -- Use this to simplify left side, then ring for commutativity
    calc t * (((padicValNat p (1 + n * 2)) - 2 : ℤ) : ℝ)
        = t' * (((padicValNat p (1 + n * 2)) - 2 : ℤ) : ℝ) * Real.log p := by rw [← this]
      _ = Real.log p * (t' * (((padicValNat p (1 + n * 2)) - 2 : ℤ) : ℝ)) := by ring
      _ = Real.log p * (t' * (((padicValNat p (1 + n * 2) : ℕ) : ℤ) - 2 : ℝ)) := by norm_cast

/-- Chernoff bound for single prime (REWRITTEN with finite Markov)
    If v_p excess is unusually large, Chernoff bound controls the count -/
lemma chernoff_single_prime (p : ℕ) (hp : p.Prime) (γ : ℝ) (hγ : 0 < γ) :
  ∃ (t : ℝ) (C : ℝ), 0 < t ∧ t ≤ 1 / 2 ∧ C > 0 ∧
    ∀ (X : ℕ) (_hX : X ≥ 100),
      (Finset.filter (fun n => n ≤ X ∧
        (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ) > γ * Real.log (p : ℝ)
      ) (Finset.Icc 0 X)).card ≤ C * (X : ℝ) * Real.exp (- t * γ * Real.log (p : ℝ)) := by
  -- Strategy (REWRITTEN with finite Markov):
  -- 1. Choose t = min(γ/4, 1/4) (so 0 < t ≤ 1/4 ≤ 1/2). We avoid using log(2)
  --    directly in the definition so the numeric inequalities are trivial.
  -- 2. Simplify threshold: (v - 2) * log p > γ * log p ⟺ v - 2 > γ (since log p > 0)
  -- 3. Apply `markov_card_bound` with Y(n) = p^{t*(v_p(2n+1)-2)} and threshold
  --    A = exp(t * γ * log p) = p^{t * γ}.
  -- 4. Use `mgf_padic_excess_bound_pbase` to get (∑_{n≤X} Y(n)) / (X+1) ≤ C_mgf.
  -- 5. Markov gives: count ≤ (∑ Y) / A ≤ C_mgf * (X+1) / A, and for X ≥ 100
  --    absorb the factor X+1 ≤ 2X into the constant (C_mgf * 2).
  --
  -- IMPLEMENTATION:
  -- Step 1: Select t in (0,1/2] small enough for `mgf_padic_excess_bound_pbase`.
  let t := min (γ / 4) (1 / 4)
  have ht : 0 < t := by
    apply lt_min
    · linarith [hγ]
    · norm_num
  have ht_le_half : t ≤ 1 / 2 := by
    -- 1/4 ≤ 1/2, so min(·, 1/4) ≤ 1/2
    calc t = min (γ / 4) (1 / 4) := rfl
      _ ≤ (1 : ℝ) / 4 := min_le_right _ _
      _ ≤ 1 / 2 := by norm_num

  -- Use p-base MGF bound (layer-cake version) for odd primes; handle p = 2 separately
  by_cases h2 : p = 2
  · -- p = 2: v_2(2n+1) = 0 so threshold never holds (since γ > 0)
    use t, (1 : ℝ)
    constructor
    · exact ht
    constructor
    · -- t ≤ 1/2 (small numeric bound)
      have h_le : t ≤ (1 : ℝ) / 4 := by
        calc t = min (γ / 4) (1 / 4) := rfl
          _ ≤ (1 : ℝ) / 4 := min_le_right _ _
      have h_lt : (1 : ℝ) / 4 ≤ 1 / 2 := by norm_num
      exact le_trans h_le h_lt
    constructor
    · norm_num
    · intro X hX
      subst h2
      -- For p = 2 the predicate is impossible because v_2(2n+1) = 0 and γ > 0.
      have h_cond_false : ∀ n ∈ Finset.Icc 0 X,
        ¬ (γ * Real.log (2 : ℝ)
            < (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ)) := by
        intro n _
        have hlog_pos : 0 < Real.log (2 : ℝ) := by
          have : (1 : ℝ) < 2 := by norm_num
          exact Real.log_pos this
        have hneg_const : (-2 : ℝ) < 0 := by norm_num
        have hleft_neg' : (-2 : ℝ) * Real.log (2 : ℝ) < 0 :=
          mul_neg_of_neg_of_pos hneg_const hlog_pos
        have hleft_neg :
            (((padicValNat 2 (2 * n + 1) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ)) < 0 := by
          simpa [padic_val_two_of_odd]
            using hleft_neg'
        have hright_pos : 0 < γ * Real.log (2 : ℝ) := mul_pos hγ hlog_pos
        have hle :
            (((padicValNat 2 (2 * n + 1) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ))
                ≤ γ * Real.log (2 : ℝ) :=
          le_trans (le_of_lt hleft_neg) (le_of_lt hright_pos)
        exact not_lt_of_ge hle
      have h_pred_false : ∀ n ∈ Finset.Icc 0 X,
        ¬ (n ≤ X ∧
            γ * Real.log (2 : ℝ)
                < (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ)) := by
        intro n hn
        have hcond := h_cond_false n hn
        exact fun h => hcond h.2
      have h_empty :
          Finset.filter
              (fun n =>
                n ≤ X ∧
                  γ * Real.log (2 : ℝ)
                      < (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ))
              (Finset.Icc 0 X) = ∅ := by
        classical
        refine Finset.filter_eq_empty_iff.mpr ?_
        intro n hn
        exact h_pred_false n hn
      have h_card_zero_nat :
          (Finset.filter
                (fun n =>
                  n ≤ X ∧
                    γ * Real.log (2 : ℝ)
                        < (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ))
                (Finset.Icc 0 X)).card = 0 := by
        classical
        exact Finset.card_eq_zero.mpr h_empty
      have h_cast_zero :
          ((Finset.filter
                (fun n =>
                  n ≤ X ∧
                    γ * Real.log (2 : ℝ)
                        < (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ))
                (Finset.Icc 0 X)).card : ℝ) = 0 := by
        classical
        simpa using congrArg (fun n : ℕ => (n : ℝ)) h_card_zero_nat
      have h_filter_swap :
          Finset.filter
              (fun n =>
                n ≤ X ∧
                  (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ)
                      > γ * Real.log (2 : ℝ))
              (Finset.Icc 0 X)
            =
          Finset.filter
              (fun n =>
                n ≤ X ∧
                  γ * Real.log (2 : ℝ)
                      < (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ))
              (Finset.Icc 0 X) := by
        classical
        refine Finset.filter_congr ?_
        intro n hn
        rfl
      have h_card_zero_nat_gt :
          (Finset.filter
                (fun n =>
                  n ≤ X ∧
                    (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ)
                        > γ * Real.log (2 : ℝ))
                (Finset.Icc 0 X)).card = 0 := by
        classical
        simpa [h_filter_swap] using h_card_zero_nat
      have h_rhs_nonneg :
          0 ≤ (X : ℝ) * Real.exp (-t * γ * Real.log (2 : ℝ)) := by
        have hX_nonneg : 0 ≤ (X : ℝ) := by
          exact_mod_cast Nat.zero_le X
        have h_exp_nonneg :
            0 ≤ Real.exp (-t * γ * Real.log (2 : ℝ)) :=
          le_of_lt (Real.exp_pos _)
        exact mul_nonneg hX_nonneg h_exp_nonneg
      have h_goal_lt :
          ((Finset.filter
                (fun n =>
                  n ≤ X ∧
                    γ * Real.log (2 : ℝ)
                        < (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ))
                (Finset.Icc 0 X)).card : ℝ)
              ≤ (X : ℝ) * Real.exp (-t * γ * Real.log (2 : ℝ)) := by
        have hL := h_cast_zero
        have hineq := h_rhs_nonneg
        calc
          ((Finset.filter
                (fun n =>
                  n ≤ X ∧
                    γ * Real.log (2 : ℝ)
                        < (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ))
                (Finset.Icc 0 X)).card : ℝ)
              = 0 := hL
          _ ≤ (X : ℝ) * Real.exp (-t * γ * Real.log (2 : ℝ)) := hineq
      have h_goal_gt :
          ((Finset.filter
                (fun n =>
                  n ≤ X ∧
                    (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ)
                        > γ * Real.log (2 : ℝ))
                (Finset.Icc 0 X)).card : ℝ)
              ≤ (X : ℝ) * Real.exp (-t * γ * Real.log (2 : ℝ)) := by
        simpa [h_filter_swap]
          using h_goal_lt
      have h_goal_full :
          ((Finset.filter
                (fun n =>
                  n ≤ X ∧
                    (((padicValNat 2 (2 * n + 1)) - 2 : ℤ) : ℝ) * Real.log (2 : ℝ)
                        > γ * Real.log (2 : ℝ))
                (Finset.Icc 0 X)).card : ℝ)
              ≤ (1 : ℝ) * (X : ℝ) * Real.exp (-t * γ * Real.log (2 : ℝ)) := by
        simpa [one_mul] using h_goal_gt
      -- Coerce inequality back to naturals (Lean handles the coercion implicitly)
      exact h_goal_full

  · -- p ≠ 2: apply p-base MGF bound
    have hpodd : p ≠ 2 := by exact h2
    obtain ⟨C_mgf, hC_mgf_pos, hC_mgf_bound⟩ := mgf_padic_excess_bound_pbase p hp hpodd t ht ht_le_half
    -- Define Y(n) = p^{t*(v_p(2n+1) - 2)} and threshold A = exp(t*γ*log p)
    let Y := fun n => (p : ℝ) ^ (t * (((padicValNat p (2*n+1)) : ℤ) - 2))
    let A := Real.exp (t * γ * Real.log (p : ℝ))
    have hA_pos : 0 < A := by positivity

    -- Markov: count ≤ ∑ Y / A. Use MGF bound to control ∑ Y.
    use t, C_mgf * 2, ht
    constructor
    · exact ht_le_half
    constructor
    · linarith [hC_mgf_pos]
    · intro X hX
      have hY_nonneg : ∀ n ≤ X, 0 ≤ Y n := by intro n _; apply Real.rpow_nonneg; norm_cast; omega
      -- MGF bound gives: (∑_{n≤X} Y n) / (X+1) ≤ C_mgf
      have h_sum_bound := hC_mgf_bound X (by omega : X ≥ 1)

      -- Markov-style proof:
      -- Step 1: Define predicate matching the goal filter
      -- Goal: (v_p(2n+1) - 2) * log p > γ * log p
      -- Equivalently (log p > 0 for p ≥ 2): v_p(2n+1) - 2 > γ
      have hlog_pos : 0 < Real.log (p : ℝ) := by
        have hp2 : 2 ≤ p := hp.two_le
        have : (1 : ℝ) < p := by
          have : 1 < p := hp.one_lt
          exact Nat.one_lt_cast.mpr this
        exact Real.log_pos this

      -- Relate p-base Y to exp-base threshold
      -- Y n = p^{t*(v-2)} and A = exp(t*γ*log p) = p^{t*γ}
      have hA_eq_pbase : A = (p : ℝ) ^ (t * γ) := by
        dsimp [A]
        have hp_pos : 0 < (p : ℝ) := by
          have : 0 < p := hp.pos
          exact Nat.cast_pos.mpr this
        rw [Real.rpow_def_of_pos hp_pos]
        congr 1
        ring

      -- Key: A < Y n ⟺ p^{t*γ} < p^{t*(v-2)} ⟺ t*γ < t*(v-2) (since p > 1, log p > 0)
      -- ⟺ γ < v - 2 ⟺ (v-2)*log p > γ*log p
      have h_filter_equiv : ∀ n ∈ Finset.Icc 0 X,
        (A < Y n) ↔ (γ * Real.log (p : ℝ) < (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ)) := by
        intro n _
        have hp_gt_one : 1 < (p : ℝ) := by
          have : 1 < p := hp.one_lt
          exact Nat.one_lt_cast.mpr this
        dsimp [Y, A]
        -- First rewrite A using hA_eq_pbase
        have hA_rw : Real.exp (t * γ * Real.log (p : ℝ)) = (p : ℝ) ^ (t * γ) := hA_eq_pbase
        rw [hA_rw]
        constructor
        · intro hlt
          have hp_pos : 0 < (p : ℝ) := by linarith
          -- Use rpow monotonicity for p > 1: p^z < p^y ↔ z < y
          have hexp_lt : t * γ < t * ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ)) := by
            have hlt_cast : (p : ℝ) ^ (t * γ) < (p : ℝ) ^ (t * ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ))) := by
              convert hlt using 2
              norm_cast
            have hexp_mono : (p : ℝ) ^ (t * γ) < (p : ℝ) ^ (t * ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ)))
                ↔ t * γ < t * ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ)) :=
              Real.rpow_lt_rpow_left_iff hp_gt_one
            exact hexp_mono.mp hlt_cast
          have ht_pos_for_cancel : 0 < t := ht
          have hcancel : γ < ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ)) := by
            have h_mul_cancel := (mul_lt_mul_iff_right₀ ht_pos_for_cancel).mp hexp_lt
            exact h_mul_cancel
          have hlog_mul : γ * Real.log (p : ℝ) < ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ)) * Real.log (p : ℝ) :=
            mul_lt_mul_of_pos_right hcancel hlog_pos
          exact hlog_mul
        · intro hlt
          have hp_pos : 0 < (p : ℝ) := by linarith
          have hineq : γ < ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ)) :=
            (mul_lt_mul_iff_left₀ hlog_pos).mp hlt
          have hexp_lt : t * γ < t * ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ)) :=
            mul_lt_mul_of_pos_left hineq ht
          have hexp_mono : (p : ℝ) ^ (t * γ) < (p : ℝ) ^ (t * ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ)))
              ↔ t * γ < t * ((((padicValNat p (2 * n + 1)) - 2 : ℤ) : ℝ)) :=
            Real.rpow_lt_rpow_left_iff hp_gt_one
          have hexp_result := hexp_mono.mpr hexp_lt
          convert hexp_result using 2
          norm_cast

      -- Apply markov_card_bound with Y and A
      have h_markov := markov_card_bound X Y hY_nonneg hA_pos

      -- Align the filter with the goal
      have h_filter_eq :
        Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)
          =
        Finset.filter (fun n => n ≤ X ∧
          γ * Real.log (p : ℝ) < (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ))
          (Finset.Icc 0 X) := by
        classical
        refine Finset.filter_congr ?_
        intro n hn
        have := h_filter_equiv n hn
        tauto

      -- Use MGF bound to control ∑ Y
      have h_sum_le : Finset.sum (Finset.Icc 0 X) Y ≤ C_mgf * (X + 1) := by
        calc Finset.sum (Finset.Icc 0 X) Y
            = (Finset.sum (Finset.Icc 0 X) Y / (X + 1)) * (X + 1) := by
              field_simp
          _ ≤ C_mgf * (X + 1) := by
              apply mul_le_mul_of_nonneg_right h_sum_bound
              exact_mod_cast Nat.zero_le (X + 1)

      -- Combine: card ≤ (∑Y)/A ≤ C_mgf*(X+1)/A
      have h_card_le_sum : ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ)
          ≤ C_mgf * (X + 1) / A := by
        calc ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ)
            ≤ (Finset.sum (Finset.Icc 0 X) Y) / A := h_markov
          _ ≤ (C_mgf * (X + 1)) / A := by
              apply div_le_div_of_nonneg_right h_sum_le
              positivity

      -- Substitute A = exp(t*γ*log p)
      have h_final : ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ)
          ≤ C_mgf * (X + 1) / Real.exp (t * γ * Real.log (p : ℝ)) := by
        simpa [A] using h_card_le_sum

      -- For X ≥ 100, we have X+1 ≤ 2X (constant factor absorbed into C_mgf * 2)
      have hX1_le_2X : (X + 1 : ℝ) ≤ 2 * X := by
        have : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
        linarith

      have h_with_2X : C_mgf * (X + 1) / Real.exp (t * γ * Real.log (p : ℝ))
          ≤ C_mgf * 2 * X / Real.exp (t * γ * Real.log (p : ℝ)) := by
        have hexp_pos : 0 < Real.exp (t * γ * Real.log (p : ℝ)) := Real.exp_pos _
        calc C_mgf * (X + 1) / Real.exp (t * γ * Real.log (p : ℝ))
            ≤ C_mgf * (2 * X) / Real.exp (t * γ * Real.log (p : ℝ)) := by
              apply div_le_div_of_nonneg_right
              · apply mul_le_mul_of_nonneg_left hX1_le_2X
                linarith [hC_mgf_pos]
              · positivity
          _ = C_mgf * 2 * X / Real.exp (t * γ * Real.log (p : ℝ)) := by ring

      have h_goal_aligned :
          ((Finset.filter (fun n => n ≤ X ∧
            γ * Real.log (p : ℝ) < (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ))
            (Finset.Icc 0 X)).card : ℝ)
              ≤ C_mgf * 2 * X * Real.exp (-(t * γ * Real.log (p : ℝ))) := by
        have h_rewrite_exp : Real.exp (-(t * γ * Real.log (p : ℝ)))
            = 1 / Real.exp (t * γ * Real.log (p : ℝ)) := by
          rw [Real.exp_neg]
          rw [inv_eq_one_div]
        calc ((Finset.filter (fun n => n ≤ X ∧
              γ * Real.log (p : ℝ) < (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ))
              (Finset.Icc 0 X)).card : ℝ)
            = ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ) := by
              simp [h_filter_eq]
          _ ≤ C_mgf * 2 * X / Real.exp (t * γ * Real.log (p : ℝ)) := by linarith [h_final, h_with_2X]
          _ = C_mgf * 2 * X * (1 / Real.exp (t * γ * Real.log (p : ℝ))) := by ring
          _ = C_mgf * 2 * X * Real.exp (-(t * γ * Real.log (p : ℝ))) := by
              rw [← h_rewrite_exp]

      -- Now relate to the goal filter (which uses > instead of <)
      have h_filter_swap :
          Finset.filter (fun n => n ≤ X ∧
            (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ) > γ * Real.log (p : ℝ))
            (Finset.Icc 0 X)
            =
          Finset.filter (fun n => n ≤ X ∧
            γ * Real.log (p : ℝ) < (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ))
            (Finset.Icc 0 X) := by
        classical
        refine Finset.filter_congr ?_
        intro n _
        rfl

      have h_final_goal :
          ((Finset.filter (fun n => n ≤ X ∧
            (((padicValNat p (2*n+1)) - 2 : ℤ) : ℝ) * Real.log (p : ℝ) > γ * Real.log (p : ℝ))
            (Finset.Icc 0 X)).card : ℝ)
              ≤ (C_mgf * 2) * X * Real.exp (- t * γ * Real.log (p : ℝ)) := by
        simpa [h_filter_swap] using h_goal_aligned

      exact h_final_goal

end ABC
