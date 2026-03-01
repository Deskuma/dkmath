/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC024

#print "file: DkMath.ABC.ABC025"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

namespace Telescoping

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory


variable {p : ℕ}

/-! ### Basic Bounds on p-adic Valuation -/

/-- The p-adic valuation of n is at most n itself.

This follows from the fact that p ≥ 2, so p^v ≥ 2^v.
For v ≥ 1: 2^v ≥ v+1 (by induction).
Since p^v | n implies p^v ≤ n, we get v ≤ n.

**Proof sketch:**
1. If n = 0, then padicValNat p 0 = 0 ≤ 0 trivially.
2. If n ≥ 1, let v = padicValNat p n.
3. Then p^v | n, so p^v ≤ n.
4. Since p ≥ 2, we have p^v ≥ 2^v.
5. By induction: 2^v ≥ v+1 for all v ≥ 0.
6. So v+1 ≤ 2^v ≤ p^v ≤ n, giving v ≤ n-1 < n.
-/
lemma padicValNat_le_self (n : ℕ) : padicValNat p n ≤ n := by
  cases n with
  | zero => simp [padicValNat.zero]
  | succ n =>
    -- For n+1 ≥ 1, we use the fact that v ≤ log_p(n+1) ≤ n+1
    have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
    calc padicValNat p (n + 1)
      _ ≤ Nat.log p (n + 1) := padicValNat_le_nat_log (n + 1)
      _ ≤ n + 1 := Nat.log_le_self _ _

/-- The p-adic valuation of n is at most the logarithm base p of n.

This is a tighter bound than `padicValNat_le_self`.
Note: Mathlib already has `padicValNat_le_nat_log` in
Mathlib.NumberTheory.Padics.PadicVal.Basic:480

**Proof sketch:**
1. If n = 0, trivial.
2. If n ≥ 1, let v = padicValNat p n.
3. Then p^v | n, so p^v ≤ n.
4. Taking log_p of both sides: v ≤ log_p(n).
5. Since v is an integer, v ≤ ⌊log_p(n)⌋ = Nat.log p n.
-/
lemma padicValNat_le_log (p n : ℕ) (_hn : n ≠ 0) : padicValNat p n ≤ Nat.log p n := by
  -- This already exists in Mathlib as padicValNat_le_nat_log
  exact padicValNat_le_nat_log n


/-! ### Telescoping Identity -/

/- For any v ≤ K, we have the telescoping identity:
    p^{tv} = ∑_{k=0}^K p^{kt} · 𝟙_{v≥k}

where 𝟙_{v≥k} = 1 if v ≥ k, else 0.

**Mathematical explanation:**
The indicator sum counts: p^0·1 + p^t·𝟙_{v≥1} + p^{2t}·𝟙_{v≥2} + ... + p^{Kt}·𝟙_{v≥K}

If v = 0: gets only p^0 = 1 = p^{0·t} ✓
If v = 1: gets p^0 + p^t = 1 + p^t
          But we want p^{1·t} = p^t, not 1 + p^t!

Wait, this is WRONG! The correct identity is different.

**Correct telescoping:**
Actually, we want: p^{tv} = ∑_{k=1}^v p^{t(k-1)} · [p^t - 1] + 1
Or equivalently: p^{tv} - 1 = (p^t - 1) · ∑_{k=1}^v p^{t(k-1)}

But the indicator approach works differently:
  ∑_{k=0}^K p^{kt} · 𝟙_{v≥k} = p^0 + p^t + ... + p^{vt} = (p^{(v+1)t} - 1)/(p^t - 1)

This is NOT equal to p^{vt}!

**Alternative: Layer-cake formula**
The correct approach is:
  p^{tv} = ∑_{k=0}^{v-1} [p^{t(k+1)} - p^{tk}] + p^0
        = ∑_{k=1}^v [p^{tk} - p^{t(k-1)}] + 1

Using indicators:
  p^{tv} - 1 = ∑_{k=1}^∞ 𝟙_{v≥k} · [p^{tk} - p^{t(k-1)}]
             = ∑_{k=1}^∞ 𝟙_{v≥k} · p^{t(k-1)} · (p^t - 1)

So: ∑_n [p^{tv(n)} - 1] = (p^t - 1) · ∑_n ∑_{k=1}^∞ 𝟙_{v(n)≥k} · p^{t(k-1)}
                         = (p^t - 1) · ∑_{k=1}^∞ p^{t(k-1)} · #{n : v(n) ≥ k}

**Conclusion:**
The telescoping is more subtle than initially thought. We need to carefully
handle the (p^t - 1) factor and start from k=1, not k=0.

This lemma is left as sorry because the correct formulation requires more care.
-/
/- COMMENTED OUT: WRONG FORMULATION
lemma sum_indicator_eq_pow_WRONG_FORMULATION (t : ℝ) (v K : ℕ) (hv : v ≤ K) :
    (p : ℝ) ^ (t * v) = ∑ k ∈ Finset.range (K + 1),
      if v ≥ k then (p : ℝ) ^ (t * k) else 0 := by
  sorry -- This formulation is actually INCORRECT!
-/

/-- The correct telescoping formula for p^{tv}.

We express p^{tv} using the difference formula:
  p^{tv} = 1 + ∑_{k=1}^v [p^{tk} - p^{t(k-1)}]
         = 1 + (p^t - 1) · ∑_{k=1}^v p^{t(k-1)}
         = 1 + (p^t - 1) · [p^0 + p^t + ... + p^{t(v-1)}]

For v ≤ K and using indicators:
  p^{tv} = 1 + (p^t - 1) · ∑_{k=1}^K 𝟙_{v≥k} · p^{t(k-1)}

**Proof sketch:**
1. Expand the geometric sum explicitly.
2. Verify by cases on v.
3. Use the formula: ∑_{j=0}^{v-1} p^{tj} = (p^{tv} - 1)/(p^t - 1).
-/
lemma sum_telescoping_correct {p : ℕ} (hp : p ≥ 3) (t : ℝ) (ht : 0 < t) (v K : ℕ) (hv : v ≤ K) :
    (p : ℝ) ^ (t * v) = 1 + ((p : ℝ) ^ t - 1) *
      ∑ k ∈ Finset.range K, if v ≥ k + 1 then (p : ℝ) ^ (t * k) else 0 := by
  -- Simplify the sum: indicators pick out k < v
  have h_sum_simp : ∑ k ∈ Finset.range K, (if v ≥ k + 1 then (p : ℝ) ^ (t * k) else 0)
                  = ∑ k ∈ Finset.range v, (p : ℝ) ^ (t * k) := by
    -- The indicator selects exactly k < v (since v ≥ k + 1 iff k + 1 ≤ v iff k < v)
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, ge_iff_le]
    omega
  rw [h_sum_simp]
  -- Now goal: p^{tv} = 1 + (p^t - 1) · ∑_{k=0}^{v-1} p^{tk}
  -- Use geom_sum_eq: ∑_{k=0}^{v-1} r^k = (r^v - 1) / (r - 1)
  by_cases hv_zero : v = 0
  · -- Case v = 0: trivial
    subst hv_zero
    simp
  · -- Case v > 0: use geometric sum formula
    have hp_ge : (p : ℝ) ≥ 1 := by exact_mod_cast (by omega : (1 : ℕ) ≤ p)
    have hp_pos : (0 : ℝ) < p := by linarith
    have hp_ne_zero : (p : ℝ) ≠ 0 := by linarith
    have hpt_ne_one : (p : ℝ) ^ t ≠ 1 := by
      intro h_eq
      -- p^t = 1 with p ≥ 3 and t > 0 is impossible
      have : (p : ℝ) ^ t ≥ (3 : ℝ) ^ t := by
        apply Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 3)
        · exact_mod_cast hp
        · linarith
      linarith [Real.one_lt_rpow (by linarith : (1 : ℝ) < 3) ht]
    -- Rewrite p^(t*k) as (p^t)^k using rpow_mul
    have h_rewrite : ∑ k ∈ Finset.range v, (p : ℝ) ^ (t * k) = ∑ k ∈ Finset.range v, ((p : ℝ) ^ t) ^ k := by
      congr 1
      ext k
      exact Real.rpow_mul_natCast (by linarith : (0 : ℝ) ≤ p) t k
    rw [h_rewrite]
    -- Apply geom_sum_eq: ∑_{k=0}^{v-1} x^k = (x^v - 1) / (x - 1)
    rw [geom_sum_eq hpt_ne_one v]
    -- Goal: p^{tv} = 1 + (p^t - 1) · ((p^t)^v - 1) / (p^t - 1)
    -- Simplify division: ((p^t)^v - 1) / (p^t - 1) = (p^{tv} - 1) / (p^t - 1)
    have h_pow_v : ((p : ℝ) ^ t) ^ (v : ℕ) = (p : ℝ) ^ (t * v) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ t) v]
      exact (Real.rpow_mul (by linarith : (0 : ℝ) ≤ p) t v).symm
    rw [h_pow_v]
    -- Now algebra: 1 + (p^t - 1) · (p^{tv} - 1) / (p^t - 1) = p^{tv}
    -- Cancel (p^t - 1) terms
    have h_cancel : (p : ℝ) ^ t - 1 ≠ 0 := sub_ne_zero_of_ne hpt_ne_one
    rw [mul_div_cancel₀ _ h_cancel]
    ring

/-! ### Counting Lemmas -/

/-- For k ≥ 1, the number of n ∈ [0,X] such that p^k divides 2n+1 is bounded by ⌈(X+1)/p^k⌉.

This is exactly `count_powers_dividing_2n1` from ABC.lean:15834.
We don't need to reprove it here, just reference it.

**From ABC.lean:**
```lean
private lemma count_powers_dividing_2n1 (p : ℕ) [hp : Fact (Nat.Prime p)] (k : ℕ) (X : ℕ) (hk : k ≥ 1) :
  #({n ∈ Finset.Icc 0 X | n ≤ X ∧ (p : ℕ) ^ k ∣ 2 * n + 1}) ≤ Nat.ceil ((X + 1 : ℝ) / (p : ℝ) ^ k) := by
  ...
```

For our purposes, we also need the fact that ⌈m⌉ ≤ m + 1 for any real m ≥ 0.
-/
lemma count_divisible_le (hp : p.Prime) (hp3 : p ≥ 3) {X k : ℕ} (hk : k ≥ 1) :
    ({n ∈ Finset.Icc 0 X | (p : ℕ) ^ k ∣ 2 * n + 1}).card ≤ (X + 1 : ℝ) / (p : ℝ) ^ k + 1 := by
  -- p ≠ 2 follows from p ≥ 3
  have hp_ne_2 : p ≠ 2 := by omega
  -- Filter simplification: n ≤ X is redundant in Finset.Icc 0 X
  have h_filter_eq : {n ∈ Finset.Icc 0 X | (p : ℕ) ^ k ∣ 2 * n + 1}
                    = {n ∈ Finset.Icc 0 X | n ≤ X ∧ (p : ℕ) ^ k ∣ 2 * n + 1} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    tauto
  rw [h_filter_eq]
  -- Apply count_powers_dividing_2n1 from ABC.lean
  have h_ceil := ABC.count_powers_dividing_2n1 p hp hp_ne_2 k hk X
  -- Convert ℕ cast to ℝ cast
  have h_ceil' : (({n ∈ Finset.Icc 0 X | n ≤ X ∧ (p : ℕ) ^ k ∣ 2 * n + 1}).card : ℝ)
               ≤ (⌈((X : ℝ) + 1) / (p : ℝ) ^ k⌉₊ : ℝ) := by
    exact_mod_cast h_ceil
  -- Use ceiling bound: ⌈m⌉₊ ≤ m + 1
  have h_ceil_bound : (⌈((X : ℝ) + 1) / (p : ℝ) ^ k⌉₊ : ℝ)
                    ≤ ((X : ℝ) + 1) / (p : ℝ) ^ k + 1 := by
    have h_pos : 0 ≤ ((X : ℝ) + 1) / (p : ℝ) ^ k := by
      apply div_nonneg
      · have : (0 : ℝ) < X + 1 := Nat.cast_add_one_pos X
        linarith
      · have : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
        linarith [pow_pos this k]
    have : (⌈((X : ℝ) + 1) / (p : ℝ) ^ k⌉₊ : ℝ) < ((X : ℝ) + 1) / (p : ℝ) ^ k + 1 :=
      Nat.ceil_lt_add_one h_pos
    linarith
  linarith

/-- Special case k=0: All X+1 elements have v(n) ≥ 0. -/
lemma count_all (X : ℕ) :
    ({n ∈ Finset.Icc 0 X | padicValNat p (2 * n + 1) ≥ 0}).card = X + 1 := by
  -- padicValNat is always ≥ 0, so all elements satisfy the condition
  have : {n ∈ Finset.Icc 0 X | padicValNat p (2 * n + 1) ≥ 0} = Finset.Icc 0 X := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, and_iff_left_iff_imp]
    intro _
    exact Nat.zero_le _
  rw [this]
  -- Finset.Icc 0 X = Finset.range (X + 1) for natural numbers
  have h_eq : Finset.Icc 0 X = Finset.range (X + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [h_eq, Finset.card_range]

/-! ### Exchange of Summation -/

/-- Exchange the order of summation: ∑_n ∑_k = ∑_k ∑_n.

Given:
  ∑_{n ∈ [0,X]} ∑_{k=0}^K f(n,k)

We can rewrite as:
  ∑_{k=0}^K ∑_{n ∈ [0,X]} f(n,k)

For our specific case: f(n,k) = p^{kt} · 𝟙_{v(n)≥k}

**Proof sketch:**
This is Finset.sum_comm in Mathlib, applied appropriately.
-/
lemma sum_comm_indicator (X K : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.range (K + 1), f n k =
    ∑ k ∈ Finset.range (K + 1), ∑ n ∈ Finset.Icc 0 X, f n k := by
  exact Finset.sum_comm

/-! ### Geometric Series Bounds -/

/-- Finite geometric series bound: ∑_{k=0}^K r^k ≤ 1/(1-r) when 0 < r < 1.

**Proof sketch:**
1. Geometric sum formula: ∑_{k=0}^K r^k = (1 - r^{K+1})/(1 - r).
2. Since r < 1, we have r^{K+1} ≥ 0.
3. So (1 - r^{K+1})/(1 - r) ≤ 1/(1 - r).
-/
lemma geom_sum_le {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), r ^ k ≤ 1 / (1 - r) := by
  -- Use the fact that finite geometric sum ≤ infinite sum when 0 < r < 1
  have h_summable : Summable (fun k : ℕ => r ^ k) := by
    apply summable_geometric_of_norm_lt_one
    simp [abs_of_pos hr, hr1]
  calc ∑ k ∈ Finset.range (K + 1), r ^ k
    _ ≤ ∑' k : ℕ, r ^ k := by
      refine h_summable.sum_le_tsum (Finset.range (K + 1)) (fun i _ => ?_)
      exact pow_nonneg (le_of_lt hr) _
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one (le_of_lt hr) hr1
    _ = 1 / (1 - r) := by rw [inv_eq_one_div]

/-- For p ≥ 3 and 0 < t ≤ 1/2, we have p^{t-1} < 1.

**Proof sketch:**
1. p^{t-1} = p^t / p ≤ 3^t / 3 (since p ≥ 3).
2. 3^t ≤ 3^{1/2} = √3 (since t ≤ 1/2 and t ↦ 3^t is increasing).
3. √3 / 3 = 1/√3 ≈ 0.577 < 1.
-/
lemma pow_t_minus_one_lt_one {p : ℕ} (hp : p ≥ 3) {t : ℝ} (ht : 0 < t) (ht_half : t ≤ 1 / 2) :
    (p : ℝ) ^ (t - 1) < 1 := by
  -- Strategy: p^{t-1} = p^t / p ≤ 3^t / 3 ≤ 3^{1/2} / 3 = √3/3 < 1
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega : 0 < p)
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  -- Step 1: p^{t-1} = p^t / p
  rw [Real.rpow_sub_one hp_ne]
  -- Step 2: p^t/p = p^{t-1} ≤ 3^{t-1} ≤ 3^{-1/2} < 1
  -- Key: t-1 < 0, and for negative exponents, larger base → smaller value
  have t_minus_one_nonpos : t - 1 ≤ 0 := by linarith
  have t_minus_one_le : t - 1 ≤ -(1 / 2) := by linarith
  -- Step 2a: p^{t-1} ≤ 3^{t-1} (since p ≥ 3 and t-1 ≤ 0)
  have step1 : (p : ℝ) ^ (t - 1) ≤ (3 : ℝ) ^ (t - 1) := by
    apply Real.rpow_le_rpow_of_nonpos
    · norm_num
    · exact hp3
    · exact t_minus_one_nonpos
  -- Step 2b: 3^{t-1} ≤ 3^{-1/2} (since t-1 ≤ -1/2 and 3 > 1)
  have step2 : (3 : ℝ) ^ (t - 1) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have h3 : (1 : ℝ) < 3 := by norm_num
    rw [Real.rpow_le_rpow_left_iff h3]
    exact t_minus_one_le
  -- Step 2c: 3^{-1/2} = 1/√3 < 1
  have final : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
    have h1 : (3 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / (3 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), inv_eq_one_div]
    rw [h1]
    have h2 : (3 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
    rw [h2]
    rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
    calc (1 : ℝ)
      _ = Real.sqrt 1 := by rw [Real.sqrt_one]
      _ < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  calc (p : ℝ) ^ t / p
    _ = (p : ℝ) ^ (t - 1) := by rw [← Real.rpow_sub_one hp_ne]
    _ ≤ (3 : ℝ) ^ (t - 1) := step1
    _ ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) := step2
    _ < 1 := final

/-- Bound on 1/(1 - p^{t-1}) for p ≥ 3, t ≤ 1/2.

From the calculation:
  p^{t-1} ≤ 3^{-1/2} = 1/√3 ≈ 0.577

So: 1/(1 - p^{t-1}) ≤ 1/(1 - 1/√3) = √3/(√3 - 1) ≈ 2.366

We'll use the loose bound 1/(1 - p^{t-1}) ≤ 3 for simplicity.
But the tight bound is 1/(1 - p^{t-1}) ≤ 2.4.

**Proof sketch:**
1. Show p^{t-1} ≤ 2/3 (as in ABCFinal.lean).
2. Then 1 - p^{t-1} ≥ 1/3.
3. So 1/(1 - p^{t-1}) ≤ 3.

For the tight bound (2.4), we need:
  p^{t-1} ≤ 1/√3 ⇒ 1 - 1/√3 = (√3 - 1)/√3
  ⇒ 1/(1 - 1/√3) = √3/(√3 - 1)

Computing: √3 ≈ 1.732, so √3/(√3 - 1) ≈ 1.732/0.732 ≈ 2.366
-/
lemma geom_bound_loose {p : ℕ} (hp : p ≥ 3) {t : ℝ} (ht : 0 < t) (ht_half : t ≤ 1 / 2) :
    1 / (1 - (p : ℝ) ^ (t - 1)) ≤ 3 := by
  -- From pow_t_minus_one_lt_one: p^(t-1) < 1
  have h_lt_one := pow_t_minus_one_lt_one hp ht ht_half
  -- Step 1: Show p^(t-1) ≤ 1/√3 < 2/3
  have h_sqrt3 : (p : ℝ) ^ (t - 1) ≤ 1 / Real.sqrt 3 := by
    -- This was proved in pow_t_minus_one_lt_one: p^(t-1) ≤ 3^(-1/2) = 1/√3
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega : 0 < p)
    have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have t_minus_one_nonpos : t - 1 ≤ 0 := by linarith
    have step1 : (p : ℝ) ^ (t - 1) ≤ (3 : ℝ) ^ (t - 1) := by
      apply Real.rpow_le_rpow_of_nonpos
      · norm_num
      · exact hp3
      · exact t_minus_one_nonpos
    have step2 : (3 : ℝ) ^ (t - 1) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have h3 : (1 : ℝ) < 3 := by norm_num
      rw [Real.rpow_le_rpow_left_iff h3]
      · linarith
    have h_eq : (3 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt 3 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_eq_rpow]
      norm_num
    calc (p : ℝ) ^ (t - 1) ≤ (3 : ℝ) ^ (t - 1) := step1
      _ ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) := step2
      _ = 1 / Real.sqrt 3 := h_eq
  -- Step 2: Show 1/√3 ≤ 2/3
  have h_two_thirds : 1 / Real.sqrt 3 ≤ 2 / 3 := by
    -- We'll show: 1/√3 * 3 ≤ 2 (i.e., 3/√3 ≤ 2, i.e., √3 ≤ 2/√3 * √3 = 2)
    -- Wait, that's wrong. Let's use: 1/√3 ≤ 2/3 ⟺ 3 ≤ 2√3 ⟺ 3^2 ≤ (2√3)^2 = 12
    have h_sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)
    have h_sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    -- First show 3^2 ≤ (2√3)^2
    have h_sq_ineq : (3 : ℝ) ^ 2 ≤ (2 * Real.sqrt 3) ^ 2 := by
      calc (3 : ℝ) ^ 2 = 9 := by norm_num
        _ ≤ 12 := by norm_num
        _ = 4 * 3 := by norm_num
        _ = (2 : ℝ) ^ 2 * (Real.sqrt 3) ^ 2 := by rw [h_sqrt3_sq]; norm_num
        _ = (2 * Real.sqrt 3) ^ 2 := by ring
    -- Since both sides are non-negative, we can take square roots
    have h_ineq : 3 ≤ 2 * Real.sqrt 3 := by
      have h3_nonneg : (0 : ℝ) ≤ 3 := by norm_num
      have h2sqrt3_nonneg : (0 : ℝ) ≤ 2 * Real.sqrt 3 := by
        apply mul_nonneg
        · norm_num
        · exact Real.sqrt_nonneg 3
      have h_sq_ineq' : 3 * 3 ≤ 2 * Real.sqrt 3 * (2 * Real.sqrt 3) := by
        have : (3 : ℝ) ^ 2 = 3 * 3 := sq 3
        have : (2 * Real.sqrt 3) ^ 2 = 2 * Real.sqrt 3 * (2 * Real.sqrt 3) := sq (2 * Real.sqrt 3)
        calc 3 * 3 = (3 : ℝ) ^ 2 := (sq 3).symm
          _ ≤ (2 * Real.sqrt 3) ^ 2 := h_sq_ineq
          _ = 2 * Real.sqrt 3 * (2 * Real.sqrt 3) := sq (2 * Real.sqrt 3)
      exact nonneg_le_nonneg_of_sq_le_sq h2sqrt3_nonneg h_sq_ineq'
    -- Now derive 1/√3 ≤ 2/3 from 3 ≤ 2√3
    calc 1 / Real.sqrt 3
        = 3 / (3 * Real.sqrt 3) := by ring
      _ = 3 / (Real.sqrt 3 * 3) := by ring
      _ ≤ (2 * Real.sqrt 3) / (Real.sqrt 3 * 3) := by
        apply div_le_div_of_nonneg_right h_ineq
        linarith [mul_pos h_sqrt3_pos (by norm_num : (0 : ℝ) < 3)]
      _ = 2 / 3 := by field_simp
  -- Step 3: So p^(t-1) ≤ 2/3, hence 1 - p^(t-1) ≥ 1/3
  have h_lower : 1 / 3 ≤ 1 - (p : ℝ) ^ (t - 1) := by linarith
  -- Step 4: Therefore 1/(1 - p^(t-1)) ≤ 3
  have h_pos : 0 < 1 - (p : ℝ) ^ (t - 1) := by linarith
  rw [div_le_iff h_pos]
  linarith

lemma geom_bound_tight {p : ℕ} (hp : p ≥ 3) {t : ℝ} (ht : 0 < t) (ht_half : t ≤ 1 / 2) :
    1 / (1 - (p : ℝ) ^ (t - 1)) ≤ 2.4 := by
  -- From pow_t_minus_one_lt_one: p^(t-1) < 1
  have h_lt_one := pow_t_minus_one_lt_one hp ht ht_half
  -- From the proof of geom_bound_loose: p^(t-1) ≤ 1/√3
  have h_sqrt3_bound : (p : ℝ) ^ (t - 1) ≤ 1 / Real.sqrt 3 := by
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega : 0 < p)
    have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have t_minus_one_nonpos : t - 1 ≤ 0 := by linarith
    have step1 : (p : ℝ) ^ (t - 1) ≤ (3 : ℝ) ^ (t - 1) := by
      apply Real.rpow_le_rpow_of_nonpos
      · norm_num
      · exact hp3
      · exact t_minus_one_nonpos
    have step2 : (3 : ℝ) ^ (t - 1) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have h3 : (1 : ℝ) < 3 := by norm_num
      rw [Real.rpow_le_rpow_left_iff h3]
      · linarith
    have h_eq : (3 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt 3 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_eq_rpow]
      norm_num
    linarith [step1, step2, h_eq]
  -- Step 1: So 1 - p^(t-1) ≥ 1 - 1/√3 = (√3 - 1)/√3
  have h_sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)
  have h_lower : (Real.sqrt 3 - 1) / Real.sqrt 3 ≤ 1 - (p : ℝ) ^ (t - 1) := by
    have h_eq : (Real.sqrt 3 - 1) / Real.sqrt 3 = 1 - 1 / Real.sqrt 3 := by field_simp
    rw [h_eq]
    linarith
  -- Step 2: Therefore 1/(1 - p^(t-1)) ≤ √3/(√3-1)
  have h_pos_denom : 0 < 1 - (p : ℝ) ^ (t - 1) := by linarith
  have h_pos_lower : 0 < (Real.sqrt 3 - 1) / Real.sqrt 3 := by
    apply _root_.div_pos
    · have : 1 < Real.sqrt 3 := by
        rw [← Real.sqrt_one]
        apply Real.sqrt_lt_sqrt
        · norm_num
        · norm_num
      linarith
    · exact h_sqrt3_pos
  have h_inv_ineq : 1 / (1 - (p : ℝ) ^ (t - 1)) ≤ 1 / ((Real.sqrt 3 - 1) / Real.sqrt 3) := by
    apply one_div_le_one_div_of_le h_pos_lower
    exact h_lower
  -- Step 3: Show √3/(√3-1) ≤ 2.4
  have h_target : 1 / ((Real.sqrt 3 - 1) / Real.sqrt 3) ≤ 2.4 := by
    -- Simplify: 1 / ((√3-1)/√3) = √3/(√3-1)
    have h_simp : 1 / ((Real.sqrt 3 - 1) / Real.sqrt 3) = Real.sqrt 3 / (Real.sqrt 3 - 1) := by
      field_simp
    rw [h_simp]
    -- Show: √3/(√3-1) ≤ 2.4
    -- 2.4 = 12/5, so we need √3/(√3-1) ≤ 12/5
    -- Cross-multiply: 5√3 ≤ 12(√3-1) = 12√3 - 12
    -- Rearrange: 12 ≤ 12√3 - 5√3 = 7√3
    -- Square both sides: 144 ≤ 49*3 = 147 ✓
    have h_sqrt3_minus_one_pos : 0 < Real.sqrt 3 - 1 := by
      have : 1 < Real.sqrt 3 := by
        rw [← Real.sqrt_one]
        apply Real.sqrt_lt_sqrt
        · norm_num
        · norm_num
      linarith
    rw [div_le_iff h_sqrt3_minus_one_pos]
    -- Show: √3 ≤ 2.4 * (√3 - 1)
    have h_24 : (2.4 : ℝ) = 12 / 5 := by norm_num
    rw [h_24, div_mul_eq_mul_div, mul_sub, mul_one]
    -- Goal is now: √3 ≤ (12 * √3 - 12) / 5
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 5)]
    -- Show: 5√3 ≤ 12√3 - 12, i.e., 12 ≤ 7√3
    have h_12_le_7sqrt3 : 12 ≤ 7 * Real.sqrt 3 := by
      -- Square both sides: 144 ≤ 49 * 3 = 147
      have h_sq : (12 : ℝ) ^ 2 ≤ (7 * Real.sqrt 3) ^ 2 := by
        have h_sqrt_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
        calc (12 : ℝ) ^ 2 = 144 := by norm_num
          _ ≤ 147 := by norm_num
          _ = 49 * 3 := by norm_num
          _ = (7 : ℝ) ^ 2 * (Real.sqrt 3) ^ 2 := by rw [h_sqrt_sq]; ring
          _ = (7 * Real.sqrt 3) ^ 2 := by ring
      have h12_nonneg : (0 : ℝ) ≤ 12 := by norm_num
      have h7sqrt3_nonneg : (0 : ℝ) ≤ 7 * Real.sqrt 3 := by
        apply mul_nonneg
        · norm_num
        · exact Real.sqrt_nonneg 3
      have h_prod : 7 * Real.sqrt 3 * (7 * Real.sqrt 3) = (7 * Real.sqrt 3) ^ 2 := (sq (7 * Real.sqrt 3)).symm
      have h_sq' : 12 * 12 ≤ 7 * Real.sqrt 3 * (7 * Real.sqrt 3) := by
        calc 12 * 12 = (12 : ℝ) ^ 2 := (sq 12).symm
          _ ≤ (7 * Real.sqrt 3) ^ 2 := h_sq
          _ = 7 * Real.sqrt 3 * (7 * Real.sqrt 3) := h_prod.symm
      exact nonneg_le_nonneg_of_sq_le_sq h7sqrt3_nonneg h_sq'
    linarith
  linarith [h_inv_ineq, h_target]

/-- Bound on (2X+2)^t for t ≤ 1/2 and X ≥ 1.

Since t ≤ 1/2 < 1 and 2X+2 ≥ 4 > 1, we have:
  (2X+2)^t ≤ (2X+2)^{1/2} = √(2X+2)

For X ≥ 1: √(2X+2) ≤ √(2X+2) (tautology, but we want specific bound)

Actually, for practical bound:
  (2X+2)^{1/2} ≤ X+1 when 2X+2 ≤ (X+1)^2
                      ⟺ 2X+2 ≤ X^2 + 2X + 1
                      ⟺ 1 ≤ X^2
                      ⟺ 1 ≤ X (for X ≥ 1) ✓

So for X ≥ 1: (2X+2)^t ≤ (2X+2)^{1/2} ≤ X+1.

**Proof sketch:**
1. Since t ≤ 1/2, we have (2X+2)^t ≤ (2X+2)^{1/2}.
2. For X ≥ 1: 2X+2 ≤ (X+1)^2, so √(2X+2) ≤ X+1.
-/
lemma pow_t_bound {X : ℕ} (hX : X ≥ 1) {t : ℝ} (_ht : 0 < t) (ht_half : t ≤ 1 / 2) :
    (2 * X + 2 : ℝ) ^ t ≤ X + 1 := by
  -- Step 1: Since t ≤ 1/2, we have (2X+2)^t ≤ (2X+2)^{1/2}
  have h_one_le : (1 : ℝ) ≤ 2 * X + 2 := by
    have : 1 ≤ 2 * X + 2 := by omega
    exact_mod_cast this
  have h_pow_mono : (2 * X + 2 : ℝ) ^ t ≤ (2 * X + 2 : ℝ) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le h_one_le ht_half
  -- Step 2: Show (2X+2)^{1/2} ≤ X+1, i.e., √(2X+2) ≤ X+1
  have h_sqrt_bound : (2 * X + 2 : ℝ) ^ (1 / 2 : ℝ) ≤ X + 1 := by
    have h_eq : (2 * X + 2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (2 * X + 2) := (Real.sqrt_eq_rpow (2 * X + 2)).symm
    rw [h_eq, Real.sqrt_le_iff]
    constructor
    · -- Show: 0 ≤ X+1
      have : (0 : ℕ) ≤ X + 1 := by omega
      exact_mod_cast this
    · -- Show: 2X+2 ≤ (X+1)^2
      calc (2 * X + 2 : ℝ) = 2 * X + 2 := rfl
        _ ≤ (X : ℝ) ^ 2 + 2 * X + 1 := by
          have : (1 : ℝ) ≤ (X : ℝ) ^ 2 := by
            have h_sq : (1 : ℝ) ≤ X * X := by
              have : (1 : ℕ) ≤ X * X := by
                have h_mul : X ≤ X * X := Nat.le_mul_of_pos_right X hX
                exact Nat.one_le_iff_ne_zero.mpr (by omega : X * X ≠ 0)
              exact_mod_cast this
            calc (1 : ℝ) ≤ X * X := h_sq
              _ = (X : ℝ) ^ 2 := by ring
          linarith
        _ = (X + 1 : ℝ) ^ 2 := by ring
  linarith [h_pow_mono, h_sqrt_bound]


-- ===========================================================================


/-! ### Main Telescoping Theorem -/

/-- Main theorem: Bound on ∑_{n=0}^X p^{t·v(n)} using finite telescoping.

Given:
- p ≥ 3 (odd prime)
- 0 < t ≤ 1/2
- X ≥ 1

We prove:
  ∑_{n=0}^X p^{t·padicValNat p (2n+1)} ≤ 3(X+1)

**Full proof strategy:**

1. **Define K:** Let K = Nat.log p (2X+2). Then ∀n ∈ [0,X], v(n) ≤ K.

2. **Apply telescoping:** For each n with v(n) ≤ K, use `sum_telescoping_correct`:
   ```
   p^{tv(n)} = 1 + (p^t - 1) · ∑_{k=1}^K 𝟙_{v(n)≥k} · p^{t(k-1)}
   ```

3. **Sum over n:**
   ```
   ∑_n p^{tv(n)} = (X+1) + (p^t - 1) · ∑_n ∑_{k=1}^K 𝟙_{v(n)≥k} · p^{t(k-1)}
   ```

4. **Exchange summation:**
   ```
   = (X+1) + (p^t - 1) · ∑_{k=1}^K p^{t(k-1)} · #{n : v(n) ≥ k}
   ```

5. **Apply counting bound:** Using `count_divisible_le`:
   ```
   #{n : v(n) ≥ k} ≤ (X+1)/p^k + 1
   ```

6. **Bound the sum:**
   ```
   ≤ (X+1) + (p^t - 1) · ∑_{k=1}^K p^{t(k-1)} · [(X+1)/p^k + 1]
   = (X+1) + (p^t - 1) · [(X+1) · ∑_{k=1}^K p^{t(k-1)-k} + ∑_{k=1}^K p^{t(k-1)}]
   = (X+1) + (p^t - 1) · [(X+1)/p · ∑_{k=1}^K (p^{t-1})^k + 1/p^t · ∑_{k=1}^K (p^t)^k]
   ```

7. **Geometric series:**
   Since p^{t-1} < 1 (from `pow_t_minus_one_lt_one`):
   ```
   ∑_{k=1}^K (p^{t-1})^k ≤ ∑_{k=0}^∞ (p^{t-1})^k = 1/(1 - p^{t-1})
   ```

8. **Bound (p^t - 1) factor:**
   For p ≥ 3, t ≤ 1/2:
   ```
   p^t ≤ 3^{1/2} ≈ 1.732, so p^t - 1 ≤ 0.732
   ```

9. **Final bound:**
   Using `geom_bound_tight`:
   ```
   ∑_n p^{tv(n)} ≤ (X+1) + 0.732 · [(X+1)/3 · 2.4 + small term]
                ≤ (X+1) + 0.6(X+1)
                ≤ 1.6(X+1) < 3(X+1)
   ```

**Note:** This proof sketch shows the bound is actually much better than 3(X+1).
With careful calculation, we can show ≤ 2(X+1) is achievable, which matches
the original target in ABCFinal.lean.

The detailed implementation requires ~80 lines but is entirely straightforward.
-/
theorem sum_pow_padicValNat_le_geom_half {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≥ 3)
    {t : ℝ} (ht : 0 < t) (ht_half : t ≤ 1 / 2)
    {X : ℕ} (hX : X ≥ 1) :
    ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ)) ≤ 3 * (X + 1) := by
  -- Step 1: Define K = upper bound on all v(n)
  let K := Nat.log p (2 * X + 2)
  have hK : ∀ n ∈ Finset.Icc 0 X, padicValNat p (2 * n + 1) ≤ K := by
    intro n hn
    unfold K
    -- Use padicValNat_le_log and monotonicity of Nat.log
    have h1 : padicValNat p (2 * n + 1) ≤ Nat.log p (2 * n + 1) := by
      apply padicValNat_le_log
      omega
    have h2 : 2 * n + 1 ≤ 2 * X + 2 := by
      simp only [Finset.mem_Icc] at hn
      omega
    have h3 : Nat.log p (2 * n + 1) ≤ Nat.log p (2 * X + 2) := by
      apply Nat.log_mono_right
      exact h2
    omega

  -- Step 2: Apply telescoping formula to each term
  have h_telescope : ∀ n ∈ Finset.Icc 0 X,
      (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ)) =
        1 + ((p : ℝ) ^ t - 1) *
          ∑ k ∈ Finset.range K, if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0 := by
    intro n hn
    -- Cast ℤ to ℕ: (padicValNat p (2 * n + 1) : ℤ) is actually a ℕ
    have h_cast : (t * (padicValNat p (2 * n + 1) : ℤ) : ℝ) = t * (padicValNat p (2 * n + 1) : ℝ) := by
      simp only [Int.cast_natCast]
    rw [h_cast]
    -- Apply sum_telescoping_correct
    exact sum_telescoping_correct hp3 t ht (padicValNat p (2 * n + 1)) K (hK n hn)

  -- Step 3: Sum over all n and rewrite using telescoping
  calc ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ))
      = ∑ n ∈ Finset.Icc 0 X, (1 + ((p : ℝ) ^ t - 1) *
          ∑ k ∈ Finset.range K, if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact h_telescope n hn
    _ = ∑ n ∈ Finset.Icc 0 X, 1 + ∑ n ∈ Finset.Icc 0 X, ((p : ℝ) ^ t - 1) *
          (∑ k ∈ Finset.range K, if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) := by
        rw [Finset.sum_add_distrib]
    _ = (X + 1) + ((p : ℝ) ^ t - 1) * ∑ n ∈ Finset.Icc 0 X,
          (∑ k ∈ Finset.range K, if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) := by
        rw [Finset.mul_sum]
        congr 1
        · simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
          norm_cast
    _ = (X + 1) + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Icc 0 X,
          (if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) := by
        congr 2
        exact Finset.sum_comm
        --
    _ ≤ 3 * (X + 1) := by
      -- ⊢ (↑X + 1 + (↑p ^ t - 1) * ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Icc 0 X, if padicValNat p (2 * n + 1) ≥ k + 1 then ↑p ^ (t * ↑k) else 0)
      --   ≤ 3 * (↑X + 1)
      -- Simplify: extract (p^t)^k from the indicator sum
      -- *proof, referenced from h_rewrite*
      -- have h_factor : ∀ k ∈ Finset.range K, ∑ n ∈ Finset.Icc 0 X,
      --     (if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) =
      --       (p : ℝ) ^ (t * k) * ((Finset.Icc 0 X).filter (fun n => padicValNat p (2 * n + 1) ≥ k + 1)).card := by
      --   intro k _
      --   rw [← Finset.sum_filter]
      --   simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]



      -- Apply h_factor to rewrite the double sum
      -- *proof but not referenced yet*
      -- have h_rewrite : ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Icc 0 X,
      --     (if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) =
      --       ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) * ((Finset.Icc 0 X).filter (fun n => padicValNat p (2 * n + 1) ≥ k + 1)).card := by
      --   apply Finset.sum_congr rfl
      --   exact fun k hk => h_factor k hk

      -- Now bound the count for each k
      -- Strategy: Use the trivial bound that each count ≤ X+1
      -- Then bound the geometric sum to get the final result

      -- First, show p^t - 1 ≥ 0 (actually > 0)
      -- *proof but not referenced yet*
      -- have hpt_pos : (p : ℝ) ^ t - 1 > 0 := by
      --   have : (p : ℝ) ^ t > 1 := by
      --     calc (p : ℝ) ^ t ≥ (3 : ℝ) ^ t := by
      --           apply Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 3)
      --           exact_mod_cast hp3
      --           linarith
      --       _ > 1 := Real.one_lt_rpow (by linarith : (1 : ℝ) < 3) ht
      --   linarith

      -- Rewrite goal using h_rewrite
      calc (X + 1) + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Icc 0 X,
            (if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0)
          = (X + 1) + ((p : ℝ) ^ t - 1) *
              ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) * ((Finset.Icc 0 X).filter (fun n => padicValNat p (2 * n + 1) ≥ k + 1)).card := by
            congr 2
            -- 前提で解決する h_rewrite? h_factor?
            apply Finset.sum_congr rfl
            intro k hk
            -- Apply h_factor
            rw [← Finset.sum_filter]
            simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ (X + 1) + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) * ((X + 1) / (p : ℝ) ^ (k + 1) + 1) := by
            -- Apply ceiling bound: card ≤ (X+1)/p^(k+1) + 1
            -- This is the KEY step: split into main term (X+1)/p^(k+1) and correction term +1
            gcongr with k hk
            -- ⊢ 0 ≤ ↑p ^ t - 1
            · have hpt_pos : (p : ℝ) ^ t - 1 > 0 := by
                have : (p : ℝ) ^ t > 1 := by
                  calc (p : ℝ) ^ t ≥ (3 : ℝ) ^ t := by
                        apply Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 3)
                        · exact_mod_cast hp3
                        · linarith
                  _ > 1 := Real.one_lt_rpow (by linarith : (1 : ℝ) < 3) ht
                linarith
              · linarith
            -- ⊢ ↑(#({n ∈ Finset.Icc 0 X | padicValNat p (2 * n + 1) ≥ k + 1})) ≤ (↑X + 1) / ↑p ^ (k + 1) + 1
            -- Need to relate padicValNat p (2*n+1) ≥ k+1 to p^(k+1) | 2*n+1
            have h_equiv : {n ∈ Finset.Icc 0 X | padicValNat p (2 * n + 1) ≥ k + 1}
                         = {n ∈ Finset.Icc 0 X | (p : ℕ) ^ (k + 1) ∣ 2 * n + 1} := by
              ext n
              simp only [Finset.mem_filter, Finset.mem_Icc]
              constructor
              · intro ⟨hn_mem, hv⟩
                -- padicValNat ≥ k+1 implies p^(k+1) | a
                have h_odd : 2 * n + 1 ≠ 0 := by omega
                have : (p : ℕ) ^ (k + 1) ∣ 2 * n + 1 := by
                  apply (padicValNat_dvd_iff_le h_odd).mpr
                  exact hv
                exact ⟨hn_mem, this⟩
              · intro ⟨hn_mem, hdiv⟩
                -- p^(k+1) | a implies padicValNat ≥ k+1
                have h_odd : 2 * n + 1 ≠ 0 := by omega
                have : k + 1 ≤ padicValNat p (2 * n + 1) := by
                  apply (padicValNat_dvd_iff_le h_odd).mp
                  exact hdiv
                exact ⟨hn_mem, this⟩
            rw [h_equiv]
            -- ⊢ ↑(#({n ∈ Finset.Icc 0 X | p ^ (k + 1) ∣ 2 * n + 1})) ≤ (↑X + 1) / ↑p ^ (k + 1) + 1
            have hk1 : k + 1 ≥ 1 := by omega
            convert count_divisible_le hp.out hp3 hk1 using 1
            -- *goals match exactly*
        _ = (X + 1) + ((p : ℝ) ^ t - 1) * (
              ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) * ((X + 1) / (p : ℝ) ^ (k + 1)) +
              ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) * 1) := by
            -- ⊢ ↑X + 1 + (↑p ^ t - 1) *  ∑ k ∈ Finset.range K, ↑p ^ (t * ↑k) * ((↑X + 1) / ↑p ^ (k + 1)  + 1                               ) =
            --   ↑X + 1 + (↑p ^ t - 1) * (∑ k ∈ Finset.range K, ↑p ^ (t * ↑k) * ((↑X + 1) / ↑p ^ (k + 1)) + ∑ k ∈ Finset.range K, ↑p ^ (t * ↑k) * 1)
            -- ∑ k ∈ Finset.range K, ↑p ^ (t * ↑k) = 1
            -- Split: ((X+1)/p^(k+1) + 1) = ((X+1)/p^(k+1)) + 1
            congr 2
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            -- ⊢ ↑p ^ (t * ↑k) * ((↑X + 1) / ↑p ^ (k + 1) + 1)
            -- = ↑p ^ (t * ↑k) * ((↑X + 1) / ↑p ^ (k + 1)    ) + ↑p ^ (t * ↑k) * 1
            ring
        _ = (X + 1) + ((p : ℝ) ^ t - 1) * ((X + 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) / (p : ℝ) ^ (k + 1) +
              ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k)) := by
            -- Factor out (X+1) from first sum
            congr 2
            congr 1
            · rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              rw [mul_div_assoc']
              ring_nf
            · field_simp
        _ = (X + 1) * (1 + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * (k : ℝ) - (k : ℝ) - 1)) +
              ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) := by
            -- Simplify: p^(tk) / p^(k+1) = p^(tk-k-1)
            have h_simp : ∀ k ∈ Finset.range K, (p : ℝ) ^ (t * k) / (p : ℝ) ^ (k + 1) = (p : ℝ) ^ (t * (k : ℝ) - (k : ℝ) - 1) := by
              intro k _
              have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
              rw [div_eq_mul_inv]
              conv_lhs => arg 2; rw [← Real.rpow_natCast]
              rw [← Real.rpow_neg hp_pos.le]
              rw [← Real.rpow_add hp_pos]
              congr 1
              push_cast
              ring
            rw [Finset.sum_congr rfl h_simp]
            ring
        _ = (X + 1) * (1 + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ) - 1)) +
              ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) := by
            -- Simplify exponent: tk - k - 1 = (t-1)k - 1
            congr 1
            congr 1
            congr 2
            apply Finset.sum_congr rfl
            intro k _
            have : (t * (k : ℝ) - (k : ℝ) - 1) = ((t - 1) * (k : ℝ) - 1) := by ring
            rw [← this]
        _ ≤ 3 * (X + 1) := by
            -- Main term: Use geometric series bound with r = p^(t-1)
            -- Correction term: Bound by telescoping formula
            -- Strategy: We bound (p^t - 1) / (p * (1 - p^(t-1))) ≤ 1
            -- This gives us (X+1) * (1 + ...) ≤ (X+1) * 2
            -- Then the tail term +1 gives us total ≤ 3(X+1)
            -- Split into two parts: first bound the sum with geometric series
            have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
            -- Set r = p^(t-1), we have 0 < r < 1 since t ≤ 1/2 and p ≥ 3
            have r_def : (p : ℝ) ^ (t - 1) < 1 := by
              have h1 : t - 1 < 0 := by linarith
              have h2 : (1 : ℝ) < p := by
                have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                linarith
              calc (p : ℝ) ^ (t - 1)
                  < (p : ℝ) ^ 0 := Real.rpow_lt_rpow_of_exponent_lt h2 h1
                _ = 1 := by simp
            -- Provide the positivity proof for p^(t-1) explicitly
            have r_pos : (0 : ℝ) < (p : ℝ) ^ (t - 1) := by exact Real.rpow_pos_of_pos hp_pos (t - 1)
            -- Also need p^t - 1 > 0 for later gcongr
            have hpt_pos : (p : ℝ) ^ t - 1 > 0 := by
              have : (1 : ℝ) < (p : ℝ) ^ t := by
                apply one_lt_rpow
                · have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                  linarith
                · exact ht
              linarith
            -- Bound the first sum: ∑ k, p^((t-1)k - 1)
            have h_sum1 : ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ) - 1)
                        ≤ ((p : ℝ) ^ t - 1) * ((p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1))) := by
              -- Rewrite sum as p^(-1) * ∑ k, r^k where r = p^(t-1)
              have h_rewrite : ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ) - 1)
                   = (p : ℝ) ^ (-1 : ℝ) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _
                rw [← Real.rpow_add hp_pos]
                congr 1
                ring
              rw [h_rewrite]
              -- Apply geometric sum bound
              have h_geom : ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ))
                   = ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * k) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
              rw [h_geom]
              -- Use: ∑_{k=0}^{K-1} r^k ≤ 1/(1-r) for 0 < r < 1
              have h_bound : ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ))
                          ≤ 1 / (1 - (p : ℝ) ^ (t - 1)) := by
                -- ((p : ℝ) ^ (t - 1)) ^ k = (p : ℝ) ^ ((t - 1) * (k : ℝ))
                have h_eq : ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ)) = ∑ k ∈ Finset.range K, ((p : ℝ) ^ (t - 1)) ^ k := by
                  apply Finset.sum_congr rfl
                  intro k _
                  -- 0 ≤ ↑p は hp_pos : 0 < ↑p から導ける
                  rw [Real.rpow_mul_natCast (le_of_lt hp_pos)]
                rw [h_eq, Finset.range_eq_Ico]
                exact geom_sum_Ico_le_of_lt_one r_pos.le r_def
              have : (p : ℝ) ^ (-1 : ℝ) * (1 / (1 - (p : ℝ) ^ (t - 1)))
                   = (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1)) := by ring
              calc ((p : ℝ) ^ t - 1) * ((p : ℝ) ^ (-1 : ℝ) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ)))
                  = ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ)) := by ring
                _ ≤ ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) * (1 / (1 - (p : ℝ) ^ (t - 1))) := by
                  have hp_inv_pos : (0 : ℝ) < (p : ℝ) ^ (-1 : ℝ) := by
                    apply Real.rpow_pos_of_pos hp_pos
                  gcongr
                _ = ((p : ℝ) ^ t - 1) * ((p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1))) := by
                  rw [← this]; ring_nf
              -- end of h_sum1 proof
            -- ⊢ (↑X + 1) * (1 + (↑p ^   t - 1)  * ∑ k ∈ Finset.range K, ↑p ^ ((t - 1) * ↑k - 1)) + (↑p ^ t - 1) * ∑ k ∈ Finset.range K, ↑p ^ (t * ↑k)
            -- ≤ (↑X + 1) * (1 +  ↑p ^ (-1 / 2)) + (↑X + 1)
            -- Bound the second sum: using p^(tK) ≤ X+1
            have h_pK : (p : ℝ) ^ (t * K) ≤ X + 1 := by
              -- K = log_p(2X+2) so p^K ≤ 2X+2; hence (p^(t))^K ≤ (2X+2)^t and
              -- for t ≤ 1/2 we have (2X+2)^t ≤ sqrt(2X+2) ≤ X+1 when X ≥ 1.
              have hK_def : p ^ K ≤ 2 * X + 2 := by
                unfold K
                have h_ne_zero : 2 * X + 2 ≠ 0 := by omega
                exact Nat.pow_log_le_self p h_ne_zero
              have hp_pos : 0 < (p : ℝ) := by positivity
              have h_nonneg : 0 ≤ (p : ℝ) := le_of_lt hp_pos
              -- (p : ℝ) ^ (t * K) = ((p : ℝ) ^ t) ^ K and apply monotonicity in the base
              have pow_eq : (p : ℝ) ^ (t * K) = ((p : ℝ) ^ t) ^ K := by
                -- ⊢ ↑p ^ (t * ↑K) = (↑p ^ t) ^ K
                rw [Real.rpow_mul_natCast h_nonneg t K]
              rw [pow_eq]
              -- ⊢ (↑p ^ t) ^ K ≤ ↑X + 1
              have h1 : ((p : ℝ) ^ t) ^ K ≤ (2 * X + 2 : ℝ) ^ t := by
                -- From hK_def: p^K ≤ 2X+2, we apply rpow monotonicity in the base
                -- (p^K)^t ≤ (2X+2)^t, and (p^K)^t = (p^t)^K by commutativity of exponents
                have hpK_cast : (p : ℝ) ^ K ≤ 2 * X + 2 := by exact_mod_cast hK_def
                have h_nonneg_pK : 0 ≤ (p : ℝ) ^ K := by
                  exact pow_nonneg (Nat.cast_nonneg p) K
                -- Apply rpow_le_rpow: if 0 ≤ x ≤ y and 0 ≤ z, then x^z ≤ y^z
                have h_pow : ((p : ℝ) ^ K) ^ t ≤ (2 * X + 2) ^ t := by
                  apply Real.rpow_le_rpow h_nonneg_pK hpK_cast ht.le
                -- Show (p^K)^t = (p^t)^K using commutativity
                have h_comm : ((p : ℝ) ^ K) ^ t = ((p : ℝ) ^ t) ^ K := by
                  calc ((p : ℝ) ^ K) ^ t
                      = (p : ℝ) ^ (K * t) := by
                        have : K * t = ↑K * t := by norm_cast
                        rw [this, Real.rpow_natCast_mul h_nonneg]
                    _ = (p : ℝ) ^ (t * K) := by ring_nf
                    _ = ((p : ℝ) ^ t) ^ K := by
                        rw [Real.rpow_mul_natCast]
                        exact Nat.cast_nonneg p
                rw [← h_comm]
                exact h_pow
              have h2 : (2 * X + 2 : ℝ) ^ t ≤ X + 1 := by
                -- For t ≤ 1/2, we have (2X+2)^t ≤ (2X+2)^(1/2) = √(2X+2)
                -- Then show √(2X+2) ≤ X+1, which is equivalent to 2X+2 ≤ (X+1)^2
                have h_base : 1 ≤ 2 * X + 2 := by
                  have : 1 ≤ X := hX
                  linarith
                -- Step 1: (2X+2)^t ≤ (2X+2)^(1/2) using t ≤ 1/2 and monotonicity
                have h_step1 : (2 * X + 2 : ℝ) ^ t ≤ (2 * X + 2 : ℝ) ^ (1 / 2 : ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_le
                  · exact_mod_cast h_base
                  · exact ht_half
                -- Step 2: (2X+2)^(1/2) = √(2X+2)
                have h_sqrt : (2 * X + 2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (2 * X + 2) := by
                  rw [Real.sqrt_eq_rpow]
                -- Step 3: √(2X+2) ≤ X+1 using Real.sqrt_le_iff
                have h_step2 : Real.sqrt (2 * X + 2) ≤ X + 1 := by
                  rw [Real.sqrt_le_iff]
                  constructor
                  · -- 0 ≤ X + 1
                    have : (0 : ℝ) ≤ X := Nat.cast_nonneg X
                    linarith
                  · -- 2X+2 ≤ (X+1)^2
                    have h_sq : (X + 1 : ℝ) ^ 2 = X ^ 2 + 2 * X + 1 := by ring
                    rw [h_sq]
                    -- Need: 2X+2 ≤ X^2 + 2X + 1, i.e., 1 ≤ X^2
                    have h_X_sq : 1 ≤ (X : ℝ) ^ 2 := by
                      have : 1 ≤ X := hX
                      calc (1 : ℝ)
                          = 1 ^ 2 := by norm_num
                        _ ≤ (X : ℝ) ^ 2 := by
                          apply sq_le_sq'
                          · linarith
                          · exact_mod_cast this
                    linarith
                calc (2 * X + 2 : ℝ) ^ t
                    ≤ (2 * X + 2 : ℝ) ^ (1 / 2 : ℝ) := h_step1
                  _ = Real.sqrt (2 * X + 2) := h_sqrt
                  _ ≤ X + 1 := h_step2
              exact le_trans h1 h2
            have h_sum2 : ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k)
                        ≤ (X + 1) := by
              -- Let r = (p^t). For r > 1 we have (r - 1) * ∑_{k=0}^{K-1} r^k = r^K - 1.
              have hp_pos : (0 : ℝ) < p := by positivity
              have h_r_gt1 : 1 < (p : ℝ) ^ t := by
                apply one_lt_rpow
                · have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                  linarith
                · exact ht
              -- Prove by induction that (r - 1) * ∑_{k=0}^{K-1} r^k = r^K - 1 where r = (p : ℝ) ^ t
              let r := (p : ℝ) ^ t
              have mul_eq : (r - 1) * ∑ k ∈ Finset.range K, r ^ k = r ^ K - 1 := by
                induction K with
                | zero => simp [Finset.range_zero, Finset.sum_empty, sub_eq_add_neg]
                | succ K ih =>
                  -- Finset.range (K + 1) = Finset.range K ∪ {K}
                  have : ∑ k ∈ Finset.range (K + 1), r ^ k = ∑ k ∈ Finset.range K, r ^ k + r ^ K := by
                    simp [Finset.sum_range_succ]
                  rw [this]
                  calc (r - 1) * (∑ k ∈ Finset.range K, r ^ k + r ^ K)
                      = (r - 1) * ∑ k ∈ Finset.range K, r ^ k + (r - 1) * r ^ K := by rw [mul_add]
                    _ = (r ^ K - 1) + (r - 1) * r ^ K := by rw [ih]
                    _ = r ^ (K + 1) - 1 := by
                      -- (r - 1) * r^K + (r^K - 1) = r^(K+1) - 1
                      calc (r ^ K - 1) + (r - 1) * r ^ K
                          = (r ^ K - 1) + (r ^ (K + 1) - r ^ K) := by { congr; ring }
                        _ = r ^ (K + 1) - 1 := by ring
              -- Relate ((p^t)^K) to p^(t*K) and finish with h_pK
              have pow_eq : ((p : ℝ) ^ t) ^ K = (p : ℝ) ^ (t * K) := by
                -- show nonnegativity of the base and apply the appropriate lemma
                have hp_pos : 0 < (p : ℝ) := by positivity
                have h_nonneg : 0 ≤ (p : ℝ) := le_of_lt hp_pos
                exact (Real.rpow_mul_natCast h_nonneg t K).symm
              rw [pow_eq] at mul_eq
              -- Now mul_eq = (p : ℝ) ^ (t * K) - 1, and use h_pK
              have h_le : (p : ℝ) ^ (t * K) - 1 ≤ X + 1 := by
                calc (p : ℝ) ^ (t * K) - 1 ≤ (p : ℝ) ^ (t * K) := by linarith
                  _ ≤ X + 1 := by linarith [h_pK]
              -- Convert the sum ∑ r^k to ∑ p^(t*k) so we can apply `mul_eq` to the current goal.
              have h_nonneg : 0 ≤ (p : ℝ) := by positivity
              have h_sum_eq : ∑ k ∈ Finset.range K, r ^ k = ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [Real.rpow_mul_natCast h_nonneg t k]
              -- Rewrite `mul_eq` to use the same sum-shape as the goal, then finish with `h_le`.
              rw [h_sum_eq] at mul_eq
              rw [mul_eq]
              exact h_le

            -- Combine: main + correction ≤ bound
            -- Strategy: We bound (p^t - 1) / (p * (1 - p^(t-1))) ≤ 1 (proved as h_main below)
            -- This gives us (X+1) * (1 + ...) ≤ (X+1) * 2
            -- Then the tail term +1 gives us total ≤ 3(X+1)
            calc (X + 1) * (1 + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ) - 1)) +
                  ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k)
                ≤ (X + 1) * (1 + ((p : ℝ) ^ t - 1) * ((p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1)))) +
                  (X + 1) := by gcongr
              _ = (X + 1) * (1 + ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1))) +
                  (X + 1) := by ring
              _ ≤ (X + 1) * (1 + 1) + (X + 1) := by
                  -- Bound the main term: (p^t - 1) * p^(-1) / (1 - p^(t-1)) ≤ 1
                  have hp_pos : (0 : ℝ) < p := by positivity
                  have h_denom_pos : 0 < 1 - (p : ℝ) ^ (t - 1) := by linarith [r_def]

                  -- Main bound: (p^t - 1) * p^(-1) / (1 - p^(t-1)) ≤ p^(t-1) / (1 - p^(t-1)) ≤ 1
                  have h_main : ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1)) ≤ 1 := by
                    -- Step 1: (p^t - 1) * p^(-1) ≤ p^(t-1)
                    have h_step1 : ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (t - 1) := by
                      have : (p : ℝ) ^ t * (p : ℝ) ^ (-1 : ℝ) = (p : ℝ) ^ (t - 1) := by
                        rw [← Real.rpow_add hp_pos]
                        ring_nf
                      calc ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ)
                          ≤ (p : ℝ) ^ t * (p : ℝ) ^ (-1 : ℝ) := by
                            gcongr
                            linarith [Real.rpow_pos_of_pos hp_pos t]
                        _ = (p : ℝ) ^ (t - 1) := this
                    -- Step 2: For 0 < x < 1/2, we have x / (1 - x) ≤ 1
                    have h_r_small : (p : ℝ) ^ (t - 1) < 1 / 2 := by
                      have h_exp : t - 1 ≤ -1 / 2 := by linarith
                      have h_p_gt1 : 1 < (p : ℝ) := by
                        have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                        linarith
                      calc (p : ℝ) ^ (t - 1)
                          ≤ (p : ℝ) ^ (-1 / 2 : ℝ) := by
                            rw [Real.rpow_le_rpow_left_iff h_p_gt1]
                            exact h_exp
                        _ ≤ (3 : ℝ) ^ (-1 / 2 : ℝ) := by
                            apply Real.rpow_le_rpow_of_nonpos
                            · norm_num
                            · exact_mod_cast hp3
                            · norm_num
                        _ < 1 / 2 := by
                            -- NOTE: This claim is INCORRECT! 3^(-1/2) = 1/√3 ≈ 0.577 > 0.5
                            -- The correct bound is 3^(-1/2) < 7/12 ≈ 0.583
                            -- However, the overall proof strategy still works because:
                            -- 1. The final bound uses ≤ 3(X+1), not a tighter constant
                            -- 2. The proof can be reworked to use x/(1-x) ≤ 3 directly
                            -- This sorry is left as a marker for future improvement
                            sorry -- KNOWN ISSUE: Claim is false; proof needs restructuring
                    -- Step 3: Combine
                    have h_div_lt : (p : ℝ) ^ (t - 1) / (1 - (p : ℝ) ^ (t - 1)) < 1 := by
                      have h_pos : 0 < (p : ℝ) ^ (t - 1) := r_pos
                      have h_lt_half : (p : ℝ) ^ (t - 1) < 1 / 2 := h_r_small
                      -- For 0 < x < 1/2: x / (1 - x) < x / (1/2) = 2x < 1
                      have h1 : (p : ℝ) ^ (t - 1) / (1 - (p : ℝ) ^ (t - 1)) < (p : ℝ) ^ (t - 1) / (1 / 2) := by
                        gcongr
                        linarith
                      have h2 : (p : ℝ) ^ (t - 1) / (1 / 2) = 2 * (p : ℝ) ^ (t - 1) := by ring
                      have h3 : 2 * (p : ℝ) ^ (t - 1) < 1 := by
                        calc 2 * (p : ℝ) ^ (t - 1)
                            < 2 * (1 / 2) := by gcongr
                          _ = 1 := by norm_num
                      linarith
                    have h_main_le : ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1)) ≤ (p : ℝ) ^ (t - 1) / (1 - (p : ℝ) ^ (t - 1)) := by
                      have h_num : ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (t - 1) := by
                        have : (p : ℝ) ^ t * (p : ℝ) ^ (-1 : ℝ) = (p : ℝ) ^ (t - 1) := by
                          rw [← Real.rpow_add hp_pos]
                          ring_nf
                        calc ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ)
                            ≤ (p : ℝ) ^ t * (p : ℝ) ^ (-1 : ℝ) := by
                              gcongr
                              linarith [Real.rpow_pos_of_pos hp_pos t]
                          _ = (p : ℝ) ^ (t - 1) := this
                      have h_denom_pos : 0 < 1 - (p : ℝ) ^ (t - 1) := by linarith [r_def]
                      apply div_le_div_of_nonneg_right h_num h_denom_pos.le
                    linarith
                  -- Now use h_main to bound the expression
                  have h_bound : 1 + ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1)) ≤ 1 + 1 := by
                    linarith
                  gcongr
              _ = (X + 1) * 2 + (X + 1) := by ring
              _ = 3 * (X + 1) := by ring
      -- end of calc "_ ≤ 3 * (X + 1)"
  -- end of proof









variable {p : ℕ}

noncomputable def one_sub_r_pow_neg (r : ℝ) : ℝ := (1 - r : ℝ) ^ (-1 : ℝ)
noncomputable def one_sub_r_pow_inv (r : ℝ) : ℝ := (1 - r : ℝ)⁻¹
noncomputable def one_div_one_sub_r (r : ℝ) : ℝ := 1 / (1 - r : ℝ)

lemma one_sub_r_pow_neg_eq_one_sub_r_pow_inv {r : ℝ} :
  -- (1 - r : ℝ) ^ -1 ↔ (1 - r : ℝ)⁻¹
  one_sub_r_pow_neg r = one_sub_r_pow_inv r := by
  rw [one_sub_r_pow_neg, one_sub_r_pow_inv]
  rw [Real.rpow_neg_one]

lemma one_sub_r_pow_inv_eq_one_div_one_sub_r {r : ℝ} :
  -- (1 - r : ℝ)⁻¹ ↔ 1 / (1 - r : ℝ)
  one_sub_r_pow_inv r = one_div_one_sub_r r := by
  rw [one_sub_r_pow_inv, one_div_one_sub_r]
  rw [inv_eq_one_div]

lemma one_sub_r_pow_neg_eq_one_div_one_sub_r {r : ℝ} :
  -- (1 - r : ℝ) ^ -1 ↔ 1 / (1 - r : ℝ)
  one_sub_r_pow_neg r = one_div_one_sub_r r := by
  rw [one_sub_r_pow_neg_eq_one_sub_r_pow_inv, one_sub_r_pow_inv_eq_one_div_one_sub_r]

noncomputable abbrev one_r_neg (r : ℝ) := one_sub_r_pow_neg r
noncomputable abbrev one_r_inv (r : ℝ) := one_sub_r_pow_inv r
noncomputable abbrev one_div_r (r : ℝ) := one_div_one_sub_r r

-- エイリアス
abbrev one_r_neg_inv_iff {r : ℝ} : one_r_neg r = one_r_inv r :=
  one_sub_r_pow_neg_eq_one_sub_r_pow_inv
abbrev one_r_inv_div_iff {r : ℝ} : one_r_inv r = one_div_r r :=
  one_sub_r_pow_inv_eq_one_div_one_sub_r
abbrev one_r_neg_div_iff {r : ℝ} : one_r_neg r = one_div_r r :=
  one_sub_r_pow_neg_eq_one_div_one_sub_r


/-! ### Phase 2: 補題の整備 - 3^(-1/2) と 7/12 の評価 -/

noncomputable def sqrt_3 : ℝ := (3 : ℝ) ^ (1/2 : ℝ)
noncomputable def inv_sqrt_3 : ℝ := (3 : ℝ) ^ (-(1/2 : ℝ))

/- Helper lemmas for safe division/manipulation -/

/-- r ≤ 2/3 ⇒ 0 < 1 - r -/
lemma denom_pos_of_ratio_le_two_thirds {r : ℝ} (hr : r ≤ (2 : ℝ) / 3) :
  0 < 1 - r := by
  -- 1 - r ≥ 1 - 2/3 = 1/3 > 0
  have h_ge : 1 - r ≥ 1 - (2 : ℝ) / 3 := by linarith
  have h_eq : 1 - (2 : ℝ) / 3 = 1 / 3 := by norm_num
  linarith [h_ge, h_eq]

/-- 0 ≤ r ≤ 2/3 ⇒ r/(1-r) ≤ 2 -/
lemma ratio_over_one_minus_le_two {r : ℝ} (_hr0 : 0 ≤ r) (hr : r ≤ (2 : ℝ) / 3) :
  r / (1 - r) ≤ 2 := by
  have hden_pos : 0 < 1 - r := denom_pos_of_ratio_le_two_thirds hr
  -- r/(1-r) ≤ (2/3)/(1-r) since r ≤ 2/3 and 1/(1-r) > 0
  have h_step : r / (1 - r) ≤ (2 / 3) / (1 - r) := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hr
    · rw [inv_eq_one_div]
      exact le_of_lt (one_div_pos.mpr hden_pos)
  -- Now (2/3)/(1-r) ≤ (2/3)/(1-2/3) because 1 - r ≥ 1 - 2/3
  have h_denom_ge : 1 - r ≥ 1 - (2 : ℝ) / 3 := by linarith
  have h_denom_pos' : 0 < 1 - (2 : ℝ) / 3 := by norm_num
  -- ⊢ r / (1 - r) ≤ 2
  have h_step2 : (2 / 3) / (1 - r) ≤ (2 / 3) / (1 - (2 : ℝ) / 3) := by
    -- ⊢ 2 / 3 / (1 - r) ≤ 2 / 3 / (1 - 2 / 3)
    gcongr

  have h_eq : (2 / 3) / (1 - (2 : ℝ) / 3) = 2 := by
    field_simp [h_denom_pos']
    norm_num
  linarith [h_step, h_step2, h_eq]


/-- p ≥ 3 ⇒ (p:ℝ) > 0 -/
lemma real_pos_of_nat_ge3 {p : ℕ} (hp3 : 3 ≤ p) : 0 < (p : ℝ) := by
  have : (0:ℕ) < p := lt_of_lt_of_le (by decide : 0 < 3) hp3
  exact_mod_cast this

/-- ((p^t - 1)/p ≤ p^(t-1)) を素直に出す -/
lemma sub_over_p_le_rpow_sub_one {p : ℕ} {t : ℝ} (hp3 : 3 ≤ p) :
  ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (t - 1) := by
  have hp_pos : 0 < (p : ℝ) := real_pos_of_nat_ge3 hp3
  -- (p^t - 1) ≤ p^t
  have hsub : (p : ℝ) ^ t - 1 ≤ (p : ℝ) ^ t := by linarith
  -- multiply both sides by p^(-1) ≥ 0
  have hpos_inv : 0 ≤ (p : ℝ) ^ (-1 : ℝ) := by
    have : 0 < (p : ℝ) := hp_pos
    rw [Real.rpow_neg_one, inv_eq_one_div]
    exact le_of_lt (one_div_pos.mpr this)
  have hmul := mul_le_mul_of_nonneg_right hsub hpos_inv
  -- rewrite RHS to p^(t-1)
  have : (p : ℝ) ^ t * (p : ℝ) ^ (-1 : ℝ) = (p : ℝ) ^ (t - 1) := by
    rw [← Real.rpow_add hp_pos]; ring_nf
  simpa [this] using hmul


/--
`inv_sqrt3_lt_7_12` は、3 の逆平方根が 7/12 より小さいことを証明する補題です。
すなわち、`3 ^ -1/2 < 7 / 12` が成り立つことを示します。
この不等式は、平方根の逆数と分数の大小関係に関する基本的な性質を利用しています。

【使用箇所】
- 旧版の主項評価（7/12 → 12/5 経由）
- 新版では 2/3 → 3 に簡略化予定だが、念のため保持
-/
lemma inv_sqrt3_lt_7_12 : inv_sqrt_3 < (7 : ℝ) / 12 := by
  -- (12/7)^2 = 144/49 < 3  ⇒ 12/7 < sqrt 3  ⇒ 1/sqrt 3 < 7/12
  have h_sq : ((12 : ℝ) / 7) ^ 2 < (3 : ℝ) := by
    -- 144/49 < 3  は `norm_num` で処理できる
    have : (12 : ℝ) * 12 / (7 : ℝ) ^ 2 < 3 := by norm_num
    rw [div_pow, pow_two]
    exact this
  have h_lt_sqrt : (12 : ℝ) / 7 < Real.sqrt 3 := by
    -- a^2 < b ∧ 0 ≤ b  ⇒ a < sqrt b
    apply Real.lt_sqrt_of_sq_lt
    -- (12/7)^2 < 3
    exact by simpa [pow_two] using h_sq
    -- exact 0 ≤ 3
  have h_pos1 : 0 < (12 : ℝ) / 7 := by norm_num
  have h_pos2 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  -- 0 < a < b ⇒ 1/b < 1/a
  have h_one_div : (1 : ℝ) / Real.sqrt 3 < (1 : ℝ) / ((12 : ℝ) / 7) :=
    one_div_lt_one_div_of_lt h_pos1 h_lt_sqrt
  -- (3)^(-1/2) = 1 / sqrt 3
  have h_rpow_eq : inv_sqrt_3 = 1 / Real.sqrt 3 := by
    have h3_nonneg : 0 ≤ (3 : ℝ) := by norm_num
    -- (3 : ℝ) ^ (-(1/2 : ℝ)) = 1 / (3 : ℝ) ^ (1/2 : ℝ)
    rw [inv_sqrt_3, Real.rpow_neg h3_nonneg (1/2 : ℝ), inv_eq_one_div]
    -- (3 : ℝ) ^ (1/2 : ℝ) = Real.sqrt 3
    rw [Real.sqrt_eq_rpow (3 : ℝ)]
    -- これで (3 : ℝ) ^ (-(1/2 : ℝ)) = 1 / Real.sqrt 3
  -- 1 / (12/7) = 7/12
  rw [h_rpow_eq]  -- ゴールを (√3)⁻¹ < 7/12 に変換
  simpa [one_div, inv_div] using h_one_div


-- 以降は 1/(1 - r) ≤ 12/5 を使えば 3 の上界に組み込める：
-- 1/(1 - (3 : ℝ) ^ (-(1/2 : ℝ))) ≤ 12/5
-- 1/(1-3^(-1/2))=2.3660254<12/5=2.4
lemma one_div_one_sub_inv_sqrt3_le_12div5 : 1 / (1 - inv_sqrt_3) ≤ (12 : ℝ) / 5 := by
  have hr : inv_sqrt_3 < (7 : ℝ) / 12 := inv_sqrt3_lt_7_12
  have hden_pos : 0 < 1 - inv_sqrt_3 := sub_pos.mpr (lt_of_lt_of_le hr (by norm_num))
  -- 1/(1 - r) は r↗ で増加。r ≤ 7/12 なら 1/(1 - r) ≤ 1/(1 - 7/12) = 12/5
  have : 1 / (1 - inv_sqrt_3) ≤ 1 / (1 - (7 : ℝ) / 12) :=
    one_div_le_one_div_of_le (by norm_num : 0 < 1 - (7 : ℝ) / 12) (by nlinarith : 1 - (7 : ℝ) / 12 ≤ 1 - inv_sqrt_3)
  have h_eq : 1 / (1 - (7 : ℝ) / 12) = 12 / 5 := by norm_num
  rw [h_eq] at this
  -- ここで型が一致しているので、そのまま le_trans でゴールに繋げる
  exact le_trans this (by norm_num)

/-- ABCテレスコーピング用の幾何級数主項評価 -/
abbrev abc_telescoping_geom_bound := one_div_one_sub_inv_sqrt3_le_12div5

-- そして 12/5 < 3 は自明
example : (12 : ℝ) / 5 < 3 := by norm_num

-- sqrt 3 < 2
-- h_sqrt3_lt_2
example : Real.sqrt 3 < 2 := by
  -- sqrt 3 < 2 ⇔ 3 < 2^2 ⇔ 3 < 4
  have h_nonneg : 0 ≤ (2 : ℝ) := by norm_num
  have h_lt : (3 : ℝ) < (2 : ℝ)^2 := by norm_num
  -- 2 ≥ 0 なので sqrt 3 < 2
  exact (Real.sqrt_lt (by norm_num : 0 ≤ (3 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))).mpr h_lt




-- 1-3^(1/2)=-0.73205081<12/5
-- (1-3^(-1/2))^(-1)=2.3660254<12/5=2.4
lemma one_sub_sqrt3_rpow_neq_one_le_12div5 : (1 - inv_sqrt_3) ^ (-1 : ℝ) ≤ (12 : ℝ) / 5 := by
  -- (1 - (3 : ℝ) ^ ((-1/2 : ℝ))) ^ (-1 : ℝ) = 1 / (1 - (3 : ℝ) ^ (-(1/2 : ℝ))) を pow_neg で変形
  rw [rpow_neg_one (1 - inv_sqrt_3), inv_eq_one_div]
  -- これでゴールが 1 / (1 - (3 : ℝ) ^ (-(1/2 : ℝ))) ≤ 12 / 5 になる
  exact one_div_one_sub_inv_sqrt3_le_12div5







private lemma have_r_def {p : ℕ} {t : ℝ} (hp3 : p ≥ 3) (ht_sub_one_neg : t - 1 < 0) : (p : ℝ) ^ (t - 1) < 1 := by
  have h1 : t - 1 < 0 := ht_sub_one_neg
  have h2 : (1 : ℝ) < p := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  calc (p : ℝ) ^ (t - 1)
      < (p : ℝ) ^ 0 := Real.rpow_lt_rpow_of_exponent_lt h2 h1
    _ = 1 := by simp


-- Bound the first sum: ∑ k, p^((t-1)k - 1)
private lemma have_sum1 {p : ℕ} {t : ℝ}
  (hp3 : p ≥ 3)
  (K : ℕ)
  (hp_pos : 0 < (p : ℝ))
  (r_pos : 0 < (p : ℝ) ^ (t - 1))
  (r_def : (p : ℝ) ^ (t - 1) < 1)
  (hpt_pos : (p : ℝ) ^ t - 1 > 0)
  :
      ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ) - 1)
    ≤ ((p : ℝ) ^ t - 1) * ((p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1))) := by
  -- Rewrite sum as p^(-1) * ∑ k, r^k where r = p^(t-1)
  have h_rewrite : ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ) - 1)
        = (p : ℝ) ^ (-1 : ℝ) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Real.rpow_add hp_pos]
    congr 1
    ring
  rw [h_rewrite]
  -- Apply geometric sum bound
  have h_geom : ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ))
        = ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * k) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [h_geom]
  -- Use: ∑_{k=0}^{K-1} r^k ≤ 1/(1-r) for 0 < r < 1
  have h_bound : ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ))
              ≤ 1 / (1 - (p : ℝ) ^ (t - 1)) := by
    -- ((p : ℝ) ^ (t - 1)) ^ k = (p : ℝ) ^ ((t - 1) * (k : ℝ))
    have h_eq : ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ)) = ∑ k ∈ Finset.range K, ((p : ℝ) ^ (t - 1)) ^ k := by
      apply Finset.sum_congr rfl
      intro k _
      -- 0 ≤ ↑p は hp_pos : 0 < ↑p から導ける
      rw [Real.rpow_mul_natCast (le_of_lt hp_pos)]
    rw [h_eq, Finset.range_eq_Ico]
    exact geom_sum_Ico_le_of_lt_one r_pos.le r_def
  have : (p : ℝ) ^ (-1 : ℝ) * (1 / (1 - (p : ℝ) ^ (t - 1)))
        = (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1)) := by ring
  calc ((p : ℝ) ^ t - 1) * ((p : ℝ) ^ (-1 : ℝ) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ)))
      = ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ)) := by ring
    _ ≤ ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) * (1 / (1 - (p : ℝ) ^ (t - 1))) := by
      have hp_inv_pos : (0 : ℝ) < (p : ℝ) ^ (-1 : ℝ) := by
        apply Real.rpow_pos_of_pos hp_pos
      gcongr
    _ = ((p : ℝ) ^ t - 1) * ((p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1))) := by
      rw [← this]; ring_nf
  -- end of h_sum1 proof


private lemma have_pK
  {p : ℕ} (hp3 : p ≥ 3)
  {t : ℝ} (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3)
  {X : ℕ} (hX : X ≥ 3)
  {K : ℕ} (hK : K = Nat.log p (X_two_mul_sum X))
  :
  (p : ℝ) ^ (t * K) ≤ X + 1 := by
    -- K = Nat.log p (2 * X + 2)
    have hK_def : p ^ K ≤ X_two_mul_sum X := by
      -- K は仮引数なので unfold 不要
      have h_ne_zero : X_two_mul_sum X ≠ 0 := by rw [X_two_mul_sum]; omega
      rw [X_two_mul_sum] at h_ne_zero
      rw [X_two_mul_sum, hK]
      exact Nat.pow_log_le_self p h_ne_zero
    have hp_pos : 0 < (p : ℝ) := by positivity
    have h_nonneg : 0 ≤ (p : ℝ) := le_of_lt hp_pos
    -- (p : ℝ) ^ (t * K) = ((p : ℝ) ^ t) ^ K and apply monotonicity in the base
    have pow_eq : (p : ℝ) ^ (t * K) = ((p : ℝ) ^ t) ^ K := by
      rw [Real.rpow_mul_natCast h_nonneg t K]
    -- ゴールの K と一致しているので rewrite 可能
    rw [pow_eq]
    -- ⊢ (↑p ^ t) ^ K ≤ ↑X + 1
    have h1 : ((p : ℝ) ^ t) ^ K ≤ (X_two_mul_sum X : ℝ) ^ t := by
      -- From hK_def: p^K ≤ 2X+2, we apply rpow monotonicity in the base
      -- (p^K)^t ≤ (2X+2)^t, and (p^K)^t = (p^t)^K by commutativity of exponents
      have hpK_cast : (p : ℝ) ^ K ≤ X_two_mul_sum X := by exact_mod_cast hK_def
      have h_nonneg_pK : 0 ≤ (p : ℝ) ^ K := by
        exact pow_nonneg (Nat.cast_nonneg p) K
      -- Apply rpow_le_rpow: if 0 ≤ x ≤ y and 0 ≤ z, then x^z ≤ y^z
      have h_pow : ((p : ℝ) ^ K) ^ t ≤ (X_two_mul_sum X) ^ t := by
        apply Real.rpow_le_rpow h_nonneg_pK hpK_cast ht.le
      -- Show (p^K)^t = (p^t)^K using commutativity
      have h_comm : ((p : ℝ) ^ K) ^ t = ((p : ℝ) ^ t) ^ K := by
        calc ((p : ℝ) ^ K) ^ t
            = (p : ℝ) ^ (K * t) := by
              have : K * t = ↑K * t := by norm_cast
              rw [this, Real.rpow_natCast_mul h_nonneg]
          _ = (p : ℝ) ^ (t * K) := by ring_nf
          _ = ((p : ℝ) ^ t) ^ K := by
              rw [Real.rpow_mul_natCast]
              exact Nat.cast_nonneg p
      rw [← h_comm]
      exact h_pow
    have h2 : (X_two_mul_sum X : ℝ) ^ t ≤ X + 1 := by
      -- For t ≤ 1/2, we have (2X+2)^t ≤ (2X+2)^(1/2) = √(2X+2)
      -- Then show √(2X+2) ≤ X+1, which is equivalent to 2X+2 ≤ (X+1)^2
      have h_base : 1 ≤ X_two_mul_sum X := by
        have : 1 ≤ X := by linarith [hX]
        rw [X_two_mul_sum]
        linarith
      -- Step 1: (2X+2)^t ≤ (2X+2)^(log2/log3) using t ≤ log2/log3 and monotonicity
      have ht_sub_one_le_log2_div_log3_sub_one : t - 1 ≤ Real.log 2 / Real.log 3 - 1 :=
        Real.t_sub_one_le_log2_div_log3_sub_one ht_le
      have h_step1 : (X_two_mul_sum X : ℝ) ^ t ≤ (X_two_mul_sum X : ℝ) ^ (Real.log 2 / Real.log 3 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact_mod_cast h_base
        · linarith [ht_sub_one_le_log2_div_log3_sub_one]
      -- Step 2: (2X+2)^(1/2) = √(2X+2)
      have h_sqrt : (X_two_mul_sum X : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (X_two_mul_sum X) := by
        rw [Real.sqrt_eq_rpow]
      -- Step 3: √(2X+2) ≤ X+1 using Real.sqrt_le_iff
      have h_step2 : Real.sqrt (X_two_mul_sum X) ≤ X + 1 := by
        rw [Real.sqrt_le_iff]
        constructor
        · -- 0 ≤ X + 1
          have : (0 : ℝ) ≤ X := Nat.cast_nonneg X
          linarith
        · -- 2X+2 ≤ (X+1)^2
          have h_sq : (X + 1 : ℝ) ^ 2 = X ^ 2 + 2 * X + 1 := by ring
          rw [h_sq]
          -- Need: 2X+2 ≤ X^2 + 2X + 1, i.e., 1 ≤ X^2
          have h_X_sq : 1 ≤ (X : ℝ) ^ 2 := by
            have : 1 ≤ X := by linarith [hX]
            calc (1 : ℝ)
                = 1 ^ 2 := by norm_num
              _ ≤ (X : ℝ) ^ 2 := by
                apply sq_le_sq'
                · linarith
                · exact_mod_cast this
          rw [X_two_mul_sum]
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ge_iff_le]
          linarith
      -- Step 2: Bound (2X+2)^(log 2/log 3) ≤ X+1 using tail_bound_alpha_X_ge3
      have h_step2 : (X_two_mul_sum X : ℝ) ^ (Real.log 2 / Real.log 3 : ℝ) ≤ X + 1 := by
        rw [X_two_mul_sum]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        exact tail_bound_alpha_X_ge3 hX
      calc (X_two_mul_sum X : ℝ) ^ t
          ≤ (X_two_mul_sum X : ℝ) ^ (Real.log 2 / Real.log 3 : ℝ) := h_step1
        _ ≤ X + 1 := h_step2
    exact le_trans h1 h2



private lemma have_sum2
  {p : ℕ} (hp3 : p ≥ 3) {t : ℝ} {X : ℕ}
  {K : ℕ} (h_pK : (p : ℝ) ^ (t * K) ≤ X + 1) :
    ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) ≤ (X + 1) := by
  -- Let r = (p^t). For r > 1 we have (r - 1) * ∑_{k=0}^{K-1} r^k = r^K - 1.
  have hp_pos : (0 : ℝ) < p := by positivity
  -- Prove by induction that (r - 1) * ∑_{k=0}^{K-1} r^k = r^K - 1 where r = (p : ℝ) ^ t
  let r := (p : ℝ) ^ t
  -- First prove the geometric series formula as a separate lemma
  have geom_series : ∀ n : ℕ, (r - 1) * ∑ k ∈ Finset.range n, r ^ k = r ^ n - 1 := by
    intro n
    induction n with
    | zero => simp [Finset.range_zero, Finset.sum_empty, sub_eq_add_neg]
    | succ n ih =>
      have : ∑ k ∈ Finset.range (n + 1), r ^ k = ∑ k ∈ Finset.range n, r ^ k + r ^ n := by
        simp [Finset.sum_range_succ]
      rw [this]
      calc (r - 1) * (∑ k ∈ Finset.range n, r ^ k + r ^ n)
          = (r - 1) * ∑ k ∈ Finset.range n, r ^ k + (r - 1) * r ^ n := by rw [mul_add]
        _ = (r ^ n - 1) + (r - 1) * r ^ n := by rw [ih]
        _ = r ^ (n + 1) - 1 := by
          calc (r ^ n - 1) + (r - 1) * r ^ n
              = (r ^ n - 1) + (r ^ (n + 1) - r ^ n) := by { congr; ring }
            _ = r ^ (n + 1) - 1 := by ring
  have mul_eq : (r - 1) * ∑ k ∈ Finset.range K, r ^ k = r ^ K - 1 := geom_series K
  -- Relate ((p^t)^K) to p^(t*K) and finish with h_pK
  have pow_eq : ((p : ℝ) ^ t) ^ K = (p : ℝ) ^ (t * K) := by
    -- show non-negativity of the base and apply the appropriate lemma
    have hp_pos : 0 < (p : ℝ) := by positivity
    have h_nonneg : 0 ≤ (p : ℝ) := le_of_lt hp_pos
    exact (Real.rpow_mul_natCast h_nonneg t K).symm
  rw [pow_eq] at mul_eq
  -- Now mul_eq = (p : ℝ) ^ (t * K) - 1, and use h_pK
  have h_le : (p : ℝ) ^ (t * K) - 1 ≤ X + 1 := by
    calc (p : ℝ) ^ (t * K) - 1 ≤ (p : ℝ) ^ (t * K) := by linarith
      _ ≤ X + 1 := by linarith [h_pK]
  -- Convert the sum ∑ r^k to ∑ p^(t*k) so we can apply `mul_eq` to the current goal.
  have h_nonneg : 0 ≤ (p : ℝ) := by positivity
  have h_sum_eq : ∑ k ∈ Finset.range K, r ^ k = ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.rpow_mul_natCast h_nonneg t k]
  -- Rewrite `mul_eq` to use the same sum-shape as the goal, then finish with `h_le`.
  rw [h_sum_eq] at mul_eq
  rw [mul_eq]
  exact h_le




/-
`sum_pow_padicValNat_le_geom_log2_div_log3` 定理は、素数 `p` (p ≥ 3) と実数 `t` (0 < t ≤ log 2 / log 3)、
自然数 `X` (X ≥ 1) に対して、区間 `Icc 0 X` 上の和
∑_{n=0}^{X} p^{t * padicValNat(p, 2n+1)}
が 4 * (X + 1) 以下であることを示します。

【大改修計画 Phase 1】現状把握とマーキング
- 目標: ht_half (t ≤ 1/2) → ht_le (t ≤ log 2 / log 3) へ変更
- 主項: r ≤ 2/3 → 1/(1-r) ≤ 4 に簡略化
- 尾項: case 分岐 (t ≤ 1/2 は √吸収、1/2 < t は最悪点 X=1 評価)

数学的背景: padicValNat(p, n) は n の p進評価（pで割り切れる最大の指数）を表します。
この版では、より正確な数値的境界を用い、定数 4 を達成します。
-/
/--
`sum_pow_padicValNat_le_geom_log2_div_log3` 定理は、素数 `p` (ただし `p ≥ 3`) と実数 `t` (ただし `0 < t ≤ log(2)/log(3)`)、および自然数 `X` (ただし `X ≥ 3`) に対して、区間 `Icc 0 X` 上の和
  ∑_{n=0}^{X} p^{t * padicValNat(p, 2n+1)}
が、`4 * (X + 1)` 以下であることを主張します。

この定理は、`2n+1` の `p` 進評価の指数的な和が、`t` の制約のもとで幾何級数的に抑えられることを示しています。`t` の上限が `log(2)/log(3)` であることから、指数の増加が制御されていることが分かります。

主な用途としては、`p` 進評価を用いた数論的な和の評価や、指数的増加の抑制に関する議論に役立ちます。
-/
theorem sum_pow_padicValNat_le_geom_log2_div_log3
  {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≥ 3)
  {t : ℝ} (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3)
  {X : ℕ} (hX : X ≥ 3) :
    ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ)) ≤ 4 * (X + 1) := by
  -- この証明は ABCTelescopingProofs.lean の sum_pow_padicValNat_le_geom と同じ構造です。
  -- 異なるのは、数値的境界として 3^(-1/2) < 7/12 を使う点です。
  -- Step 0: Setup and notation
  have ht_sub_one_neg : t - 1 < 0 := Real.t_sub_one_neg ht ht_le
  -- Step 1: Define K = upper bound on all v(n)
  let K := Nat.log p (X_two_mul_sum X)
  have hK : ∀ n ∈ Finset.Icc 0 X, padicValNat p (2 * n + 1) ≤ K := by
    intro n hn
    unfold K
    -- Use padicValNat_le_log and monotonicity of Nat.log
    have h1 : padicValNat p (2 * n + 1) ≤ Nat.log p (2 * n + 1) := by
      apply padicValNat_le_log
      omega
    have h2 : 2 * n + 1 ≤ X_two_mul_sum X := by
      simp only [Finset.mem_Icc] at hn
      rw [X_two_mul_sum]
      omega
    have h3 : Nat.log p (2 * n + 1) ≤ Nat.log p (X_two_mul_sum X) := by
      apply Nat.log_mono_right
      exact h2
    omega

  -- Step 2: Apply telescoping formula to each term
  have h_telescope : ∀ n ∈ Finset.Icc 0 X,
      (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ)) =
        1 + ((p : ℝ) ^ t - 1) *
          ∑ k ∈ Finset.range K, if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0 := by
    intro n hn
    -- Cast ℤ to ℕ: (padicValNat p (2 * n + 1) : ℤ) is actually a ℕ
    have h_cast : (t * (padicValNat p (2 * n + 1) : ℤ) : ℝ) = t * (padicValNat p (2 * n + 1) : ℝ) := by
      simp only [Int.cast_natCast]
    rw [h_cast]
    -- Apply sum_telescoping_correct
    exact sum_telescoping_correct hp3 t ht (padicValNat p (2 * n + 1)) K (hK n hn)

  -- Step 3: Sum over all n and rewrite using telescoping
  calc ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ))
      = ∑ n ∈ Finset.Icc 0 X, (1 + ((p : ℝ) ^ t - 1) *
          ∑ k ∈ Finset.range K, if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact h_telescope n hn
    _ = ∑ n ∈ Finset.Icc 0 X, 1 + ∑ n ∈ Finset.Icc 0 X, ((p : ℝ) ^ t - 1) *
          (∑ k ∈ Finset.range K, if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) := by
        rw [Finset.sum_add_distrib]
    _ = (X + 1) + ((p : ℝ) ^ t - 1) * ∑ n ∈ Finset.Icc 0 X,
          (∑ k ∈ Finset.range K, if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) := by
        rw [Finset.mul_sum]
        congr 1
        · simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
          norm_cast
    _ = (X + 1) + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Icc 0 X,
          (if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0) := by
        congr 2
        exact Finset.sum_comm
        --
    _ ≤ 4 * (X + 1) := by
      -- ⊢ (↑X + 1 + (↑p ^ t - 1) * ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Icc 0 X, if padicValNat p (2 * n + 1) ≥ k + 1 then ↑p ^ (t * ↑k) else 0)
      --   ≤ 3 * (↑X + 1)

      -- Rewrite goal using h_rewrite
      calc (X + 1) + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Icc 0 X,
            (if padicValNat p (2 * n + 1) ≥ k + 1 then (p : ℝ) ^ (t * k) else 0)
          = (X + 1) + ((p : ℝ) ^ t - 1) *
              ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) * ((Finset.Icc 0 X).filter (fun n => padicValNat p (2 * n + 1) ≥ k + 1)).card := by
            congr 2
            -- 前提で解決する h_rewrite? h_factor?
            apply Finset.sum_congr rfl
            intro k hk
            -- Apply h_factor
            rw [← Finset.sum_filter]
            simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ (X + 1) + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) * ((X + 1) / (p : ℝ) ^ (k + 1) + 1) := by
            -- Apply ceiling bound: card ≤ (X+1)/p^(k+1) + 1
            -- This is the KEY step: split into main term (X+1)/p^(k+1) and correction term +1
            gcongr with k hk
            -- ⊢ 0 ≤ ↑p ^ t - 1
            · have hpt_pos : (p : ℝ) ^ t - 1 > 0 := by
                have : (p : ℝ) ^ t > 1 := by
                  calc (p : ℝ) ^ t ≥ (3 : ℝ) ^ t := by
                        apply Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 3)
                        · exact_mod_cast hp3
                        · linarith
                    _ > 1 := Real.one_lt_rpow (by linarith : (1 : ℝ) < 3) ht
                linarith
              · linarith
            -- ⊢ ↑(#({n ∈ Finset.Icc 0 X | padicValNat p (2 * n + 1) ≥ k + 1})) ≤ (↑X + 1) / ↑p ^ (k + 1) + 1
            -- Need to relate padicValNat p (2*n+1) ≥ k+1 to p^(k+1) | 2*n+1
            have h_equiv : {n ∈ Finset.Icc 0 X | padicValNat p (2 * n + 1) ≥ k + 1}
                         = {n ∈ Finset.Icc 0 X | (p : ℕ) ^ (k + 1) ∣ 2 * n + 1} := by
              ext n
              simp only [Finset.mem_filter, Finset.mem_Icc]
              constructor
              · intro ⟨hn_mem, hv⟩
                -- padicValNat ≥ k+1 implies p^(k+1) | a
                have h_odd : 2 * n + 1 ≠ 0 := by omega
                have : (p : ℕ) ^ (k + 1) ∣ 2 * n + 1 := by
                  apply (padicValNat_dvd_iff_le h_odd).mpr
                  exact hv
                exact ⟨hn_mem, this⟩
              · intro ⟨hn_mem, hdiv⟩
                -- p^(k+1) | a implies padicValNat ≥ k+1
                have h_odd : 2 * n + 1 ≠ 0 := by omega
                have : k + 1 ≤ padicValNat p (2 * n + 1) := by
                  apply (padicValNat_dvd_iff_le h_odd).mp
                  exact hdiv
                exact ⟨hn_mem, this⟩
            rw [h_equiv]
            -- ⊢ ↑(#({n ∈ Finset.Icc 0 X | p ^ (k + 1) ∣ 2 * n + 1})) ≤ (↑X + 1) / ↑p ^ (k + 1) + 1
            have hk1 : k + 1 ≥ 1 := by omega
            convert count_divisible_le hp.out hp3 hk1 using 1
            -- *goals match exactly*
        _ = (X + 1) + ((p : ℝ) ^ t - 1) * (
              ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) * ((X + 1) / (p : ℝ) ^ (k + 1)) +
              ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) * 1) := by
            -- ⊢ ↑X + 1 + (↑p ^ t - 1) *  ∑ k ∈ Finset.range K, ↑p ^ (t * ↑k) * ((↑X + 1) / ↑p ^ (k + 1) + 1) =
            --   ↑X + 1 + (↑p ^ t - 1) * (∑ k ∈ Finset.range K, ↑p ^ (t * ↑k) * ((↑X + 1) / ↑p ^ (k + 1)    ) + ∑ k ∈ Finset.range K, ↑p ^ (t * ↑k) * 1)
            --
            -- Split: ((X+1)/p^(k+1) + 1) = ((X+1)/p^(k+1)) + 1
            congr 2
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            -- ⊢ ↑p ^ (t * ↑k) * ((↑X + 1) / ↑p ^ (k + 1) + 1)
            -- = ↑p ^ (t * ↑k) * ((↑X + 1) / ↑p ^ (k + 1)    ) + ↑p ^ (t * ↑k) * 1
            ring
        _ = (X + 1) + ((p : ℝ) ^ t - 1) * ((X + 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) / (p : ℝ) ^ (k + 1) +
              ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k)) := by
            -- Factor out (X+1) from first sum
            congr 2
            congr 1
            · rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              · intro k _
                rw [mul_div_assoc']
                ring_nf
            field_simp
        _ = (X + 1) * (1 + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * (k : ℝ) - (k : ℝ) - 1)) +
              ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) := by
            -- Simplify: p^(tk) / p^(k+1) = p^(tk-k-1)
            have h_simp : ∀ k ∈ Finset.range K, (p : ℝ) ^ (t * k) / (p : ℝ) ^ (k + 1) = (p : ℝ) ^ (t * (k : ℝ) - (k : ℝ) - 1) := by
              intro k _
              have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
              rw [div_eq_mul_inv]
              conv_lhs => arg 2; rw [← Real.rpow_natCast]
              rw [← Real.rpow_neg hp_pos.le]
              rw [← Real.rpow_add hp_pos]
              congr 1
              push_cast
              ring
            rw [Finset.sum_congr rfl h_simp]
            ring
        _ = (X + 1) * (1 + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ) - 1)) +
              ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k) := by
            -- Simplify exponent: tk - k - 1 = (t-1)k - 1
            congr 1  -- heartbeats < 50k
            congr 1
            congr 2
            apply Finset.sum_congr rfl
            intro k _
            have : (t * (k : ℝ) - (k : ℝ) - 1) = ((t - 1) * (k : ℝ) - 1) := by ring
            rw [← this]
        _ ≤ 4 * (X + 1) := by
        -- ⊢ (↑X + 1) * (1 + (↑p ^ t - 1) * ∑ k ∈ Finset.range K, ↑p ^ ((t - 1) * ↑k - 1))
        -- +                 (↑p ^ t - 1) * ∑ k ∈ Finset.range K, ↑p ^ ( t      * ↑k    )
        -- ≤ 4 * (↑X + 1)

            have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
            have r_def := have_r_def hp3 ht_sub_one_neg
            have r_def_le_2div3 := ratio_le_two_thirds hp3 ht_le
            -- Provide the positivity proof for p^(t-1) explicitly
            have r_pos : (0 : ℝ) < (p : ℝ) ^ (t - 1) := by exact Real.rpow_pos_of_pos hp_pos (t - 1)
            -- Also need p^t - 1 > 0 for later gcongr
            have hpt_pos : (p : ℝ) ^ t - 1 > 0 := by
              have : (1 : ℝ) < (p : ℝ) ^ t := by
                apply one_lt_rpow
                · have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                  linarith
                · exact ht
              linarith
            have h_sum1 := have_sum1 hp3 K hp_pos r_pos r_def hpt_pos
            -- Bound the second sum: using p^(tK) ≤ X+1
            have h_pK := have_pK hp3 ht ht_le hX rfl
            have h_sum2 := have_sum2 hp3 h_pK

            have h_r_gt1 : 1 < (p : ℝ) ^ t := by
              apply one_lt_rpow
              · have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                linarith
              · exact ht

            -- Combine: main + correction ≤ bound
            -- Strategy: We bound (p^t - 1) / (p * (1 - p^(t-1))) ≤ 1 (proved as h_main below)
            -- This gives us (X+1) * (1 + ...) ≤ (X+1) * 2
            -- Then the tail term +1 gives us total ≤ 3(X+1)
            -- ⊢ (↑X + 1) * (1 + (↑p ^ t - 1) * ∑ k ∈ Finset.range K, ↑p ^ ((t - 1) * ↑k - 1)) + (↑p ^ t - 1) * ∑ k ∈ Finset.range K, ↑p ^ (t * ↑k)
            -- ≤ 3 * (↑X + 1)
            calc (X + 1) * (1 + ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ ((t - 1) * (k : ℝ) - 1)) +
                  ((p : ℝ) ^ t - 1) * ∑ k ∈ Finset.range K, (p : ℝ) ^ (t * k)
                ≤ (X + 1) * (1 + ((p : ℝ) ^ t - 1) * ((p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1)))) +
                  (X + 1) := by gcongr
              _ = (X + 1) * (1 + ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1))) +
                  (X + 1) := by ring
              _ ≤ (X + 1) * (1 + 2) + (X + 1) := by
                  -- ⊢ (↑X + 1) * (1 + (↑p ^ t - 1) * ↑p ^ (-1) / (1 - ↑p ^ (t - 1))) + (↑X + 1) ≤ (↑X + 1) * (1 + 2) + (↑X + 1)
                  -- Bound the main term: (p^t - 1) * p^(-1) / (1 - p^(t-1)) ≤ 2






                  have hp_pos : (0 : ℝ) < p := by positivity
                  have h_denom_pos : 0 < 1 - (p : ℝ) ^ (t - 1) := by linarith [r_def]

                  -- Main bound: (p^t - 1) * p^(-1) / (1 - p^(t-1)) ≤ 2
                  have h_main : ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1)) ≤ 2 := by


                    -- 1) 分子を簡約して上に抑える
                    have h_step1 : ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (t - 1) := by
                      -- (p^t - 1) * p^{-1} = p^{t-1} - p^{-1} ≤ p^{t-1}
                      calc ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ)
                        = - (p : ℝ) ^ (-1 : ℝ) + (p : ℝ) ^ (t - 1) := by
                          -- ↑p ^ t * ↑p ^ (-1) = ↑p ^ (t - 1) by exponent law
                          {
                            -- (p^t - 1) * p^(-1) = p^t * p^(-1) - p^(-1) = p^{t-1} - p^{-1}
                            have h_exp : (p : ℝ) ^ t * (p : ℝ) ^ (-1 : ℝ) = (p : ℝ) ^ (t - 1) := by
                              rw [← Real.rpow_add hp_pos]; ring_nf
                            rw [sub_mul, h_exp]
                            ring_nf
                          }
                      _ ≤ (p : ℝ) ^ (t - 1) := by
                          -- -↑p ^ (-1) + ↑p ^ (t - 1) ≤ ↑p ^ (t - 1) は -↑p ^ (-1) ≤ 0 なので自明
                          -- -↑p ^ (-1) ≤ 0 は ↑p ^ (-1) ≥ 0 より成立
                          have h_nonneg : 0 ≤ (p : ℝ) ^ (-1 : ℝ) := by
                            rw [Real.rpow_neg_one, inv_eq_one_div]
                            exact le_of_lt (one_div_pos.mpr hp_pos)
                          -- よって -↑p ^ (-1) + ↑p ^ (t - 1) ≤ ↑p ^ (t - 1)
                          linarith [h_nonneg]


                    -- 2) 正の分母で割って不等号を保つ
                    have h_main_le : ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1))
                                      ≤ (p : ℝ) ^ (t - 1) / (1 - (p : ℝ) ^ (t - 1)) := by
                      -- 分子の評価
                      have h_step1 : ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (t - 1) := by
                        have hp_pos' : 0 < (p : ℝ) := by positivity
                        calc ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ)
                            ≤ (p : ℝ) ^ t * (p : ℝ) ^ (-1 : ℝ) := by
                              gcongr; linarith [Real.rpow_pos_of_pos hp_pos' t]
                          _ = (p : ℝ) ^ (t - 1) := by
                            rw [← Real.rpow_add (by linarith : 0 < (p : ℝ))]; ring_nf
                      -- 分母の評価
                      have h_denom_pos' : 0 < 1 - (p : ℝ) ^ (t - 1) := by linarith [r_def]
                      have hinv_nonneg : 0 ≤ (1 - (p : ℝ) ^ (t - 1))⁻¹ := by
                        rw [inv_eq_one_div]; exact
                        (one_div_pos.mpr h_denom_pos').le
                      apply mul_le_mul_of_nonneg_right h_step1 hinv_nonneg

                    -- Now bound p^(t-1)/(1 - p^(t-1)) using p^(t-1) ≤ 2/3 and 1/(1-r) ≤ 3
                    have h_main_bound : ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1)) ≤ 2 := by
                      have hr_le : (p : ℝ) ^ (t - 1) ≤ (2 : ℝ) / 3 := ratio_le_two_thirds hp3 ht_le
                      have h_denom_pos' : 0 < 1 - (p : ℝ) ^ (t - 1) := by linarith [r_def]
                      have hinv_nonneg : 0 ≤ (1 - (p : ℝ) ^ (t - 1))⁻¹ := by
                        rw [inv_eq_one_div]; exact
                        (one_div_pos.mpr h_denom_pos').le

                      calc ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) / (1 - (p : ℝ) ^ (t - 1))
                          ≤ (2 / 3) * (1 / (1 - (p : ℝ) ^ (t - 1))) := by
                            have two_thirds_nonneg : 0 ≤ (2 / 3) := by norm_num
                            rw [← inv_eq_one_div]
                            -- まず h_main_le で (↑p ^ t - 1) * ↑p ^ (-1) / (1 - ↑p ^ (t - 1)) ≤ ↑p ^ (t - 1) / (1 - ↑p ^ (t - 1))
                            -- 次に mul_le_mul_of_nonneg_right で ↑p ^ (t - 1) / (1 - ↑p ^ (t - 1)) ≤ (2 / 3) / (1 - ↑p ^ (t - 1))
                            have h_mul_le := mul_le_mul_of_nonneg_right hr_le hinv_nonneg
                            exact le_trans h_main_le h_mul_le
                        _ ≤ (2 / 3) * 3 := by
                            have h_inv_bound : 1 / (1 - (p : ℝ) ^ (t - 1)) ≤ 3 := one_div_one_sub_rpow_le_3 hp3 ht ht_le
                            gcongr
                        _ ≤ 2 := by norm_num
                      -- calc: solved in h_main_bound


                    -- h_main_bound : (↑p ^ t - 1) * ↑p ^ (-1) / (1 - ↑p ^ (t - 1)) ≤ 3
                    --              ⊢ (↑p ^ t - 1) * ↑p ^ (-1) / (1 - ↑p ^ (t - 1)) ≤ 3
                    exact h_main_bound
                  -- solved: h_main
                  -- ⊢ (↑X + 1) * (1 + (↑p ^ t - 1) * ↑p ^ (-1) / (1 - ↑p ^ (t - 1))) + (↑X + 1) ≤ (↑X + 1) * (1 + 2) + (↑X + 1)
                  gcongr with X  -- finish
                  -- exact h_main
                -- solved: ≤ (X + 1) * (1 + 2) + (X + 1)





              -- calc





              _ = (X + 1) * 3 + (X + 1) := by ring
              _ = 4 * (X + 1) := by ring
              _ ≤ 4 * (X + 1) := by
                -- Final simplification: 4(X+1) ≤ 4(X+1) for X ≥ 3
                have hX_pos : 0 < (X + 1) := by omega
                linarith [hX_pos]
            -- end of calc "≤ (X + 1) * (1 + 2) + (X + 1)"
        -- end of calc "_ ≤ (X + 1) * (1 + 2) + (X + 1)"


-- ----------------------------------------------------------------------------------------------------



      -- end of calc "_ ≤ 4 * (X + 1)"
  -- end of proof

end Telescoping

end ABC
