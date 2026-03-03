/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC020

#print "file: DkMath.ABC.ABC021"

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

namespace Janson

-- cid: 68dcf648-3cd8-832f-afa0-a396f556b3f7

/-!
## Janson Inequality: Current Status and Future Work

### Infrastructure Status (ABC.lean lines 6722-8550)

**What exists in ABC.lean:**
- ✅ `JansonModel`, `JansonSetup` structures
- ✅ `mu`, `dbar` definitions
- ✅ `product_pmf`, `bernoulli_pmf` constructions
- ✅ `expect_indicator_prod`: E[∏ I_v] = ∏ p_v for independent events
- ⚠️ `bound_v2` (line 8528): **Full statement with `admit`**

**What's missing (critical gaps):**

1. **Markov-type baseline bounds** (easiest, ~5 lemmas)
2. **Chernoff bound for sums** (moderate, ~10 lemmas)
3. **Dependency graph handling** (hard, ~15 lemmas)
4. **Second moment method** (hard, ~10 lemmas)
5. **Final Janson assembly** (moderate, ~5 lemmas)

### Formalization Roadmap

Below we sketch the missing pieces as `admit`-marked lemmas.
This serves as a concrete TODO list for completing Janson's inequality.
-/

/-! ### Auxiliary lemmas for probability bounds -/

/-- Monotonicity of expectation: if f ≤ g pointwise, then E[f] ≤ E[g]. -/
lemma PMF.expect_mono {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ)
    (_hf : ∀ a, 0 ≤ f a) (_hg : ∀ a, 0 ≤ g a) (h : ∀ a, f a ≤ g a) :
    PMF.expect p f ≤ PMF.expect p g := by
  -- Expand definition of PMF.expect
  dsimp [PMF.expect, PMF.expect_ennreal]
  -- Use ENNReal.toReal_mono for the inequality
  apply ENNReal.toReal_mono
  · -- Show g's expectation is not infinite
    have : ∀ a ∈ (Finset.univ : Finset α), p a * ENNReal.ofReal (g a) ≠ ⊤ := by
      intro a _
      exact ENNReal.mul_ne_top (PMF.apply_ne_top p a) ENNReal.ofReal_ne_top
    exact Finset.sum_ne_top_of_ne_top this
  · -- Show sum inequality at ENNReal level
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_right
    exact ENNReal.ofReal_le_ofReal (h a)

section JansonRoadmap

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-! ### Step 1: Markov and Chebyshev Bounds -/

/-- Markov's inequality: P(X ≥ t) ≤ E[X] / t for non-negative random variables. -/
lemma markov_inequality (X : (Γ → Bool) → ℝ) (t : ℝ) (M : JansonModel Γ)
    (hX_nonneg : ∀ ω, 0 ≤ X ω) (ht : 0 < t) :
    PMF.expect (product_pmf M) (fun ω => if t ≤ X ω then (1 : ℝ) else 0)
      ≤ PMF.expect (product_pmf M) X / t := by
  -- Proof strategy: t · 𝟙{X≥t} ≤ X, so E[t · 𝟙{X≥t}] ≤ E[X], hence E[𝟙{X≥t}] ≤ E[X]/t
  have hineq : ∀ ω, t * (if t ≤ X ω then (1 : ℝ) else 0) ≤ X ω := by
    intro ω
    by_cases h : t ≤ X ω
    · simp [h]
    · simp only [h, ↓reduceIte, mul_zero]
      exact hX_nonneg ω
  -- Indicator function is nonnegative
  have hind_nonneg : ∀ ω, 0 ≤ (if t ≤ X ω then (1 : ℝ) else 0) := by
    intro ω
    by_cases h : t ≤ X ω <;> simp [h]
  -- Use monotonicity of expectation
  have h_mono : PMF.expect (product_pmf M) (fun ω => t * (if t ≤ X ω then (1 : ℝ) else 0))
                ≤ PMF.expect (product_pmf M) X := by
    apply PMF.expect_mono
    · intro ω
      apply mul_nonneg (le_of_lt ht) (hind_nonneg ω)
    · exact hX_nonneg
    · exact hineq
  -- Extract the factor t using linearity
  have h_factor : PMF.expect (product_pmf M) (fun ω => t * (if t ≤ X ω then (1 : ℝ) else 0))
                  = t * PMF.expect (product_pmf M) (fun ω => if t ≤ X ω then (1 : ℝ) else 0) := by
    exact PMF.expect_const_mul (product_pmf M) t (le_of_lt ht) _ hind_nonneg
  rw [h_factor] at h_mono
  -- Divide by t (since t > 0)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  calc PMF.expect (product_pmf M) (fun ω => if t ≤ X ω then (1 : ℝ) else 0)
      = (t * PMF.expect (product_pmf M) (fun ω => if t ≤ X ω then (1 : ℝ) else 0)) / t := by
        rw [mul_div_cancel_left₀]; exact ht_ne
    _ ≤ PMF.expect (product_pmf M) X / t := by
        apply div_le_div_of_nonneg_right h_mono (le_of_lt ht)

/-- Chebyshev's inequality: P(|X - μ| ≥ t) ≤ Var(X) / t². -/
lemma chebyshev_inequality (X : (Γ → Bool) → ℝ) (t : ℝ) (M : JansonModel Γ)
    (ht : 0 < t) :
    let mu := PMF.expect (product_pmf M) X
    let variance := PMF.expect (product_pmf M) (fun ω => (X ω - mu)^2)
    PMF.expect (product_pmf M) (fun ω => if t ≤ |X ω - mu| then (1 : ℝ) else 0)
      ≤ variance / t^2 := by
  intro mu variance
  -- Define Y = (X - μ)²
  let Y := fun ω => (X ω - mu)^2
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := fun ω => sq_nonneg _
  -- Apply Markov to Y with threshold t²
  have ht_sq_pos : 0 < t^2 := sq_pos_of_pos ht
  have h_markov := markov_inequality Y (t^2) M hY_nonneg ht_sq_pos
  -- Show that the indicators are the same
  suffices PMF.expect (product_pmf M) (fun ω => if t ≤ |X ω - mu| then (1 : ℝ) else 0) ≤
           PMF.expect (product_pmf M) (fun ω => if t^2 ≤ Y ω then (1 : ℝ) else 0) by
    calc PMF.expect (product_pmf M) (fun ω => if t ≤ |X ω - mu| then (1 : ℝ) else 0)
        ≤ PMF.expect (product_pmf M) (fun ω => if t^2 ≤ Y ω then (1 : ℝ) else 0) := this
      _ ≤ PMF.expect (product_pmf M) Y / t^2 := h_markov
      _ = variance / t^2 := rfl
  -- The indicators are actually equal because |x| ≥ t ⇔ x² ≥ t²
  apply le_of_eq
  congr
  funext ω
  by_cases h : t ≤ |X ω - mu|
  · simp only [h, Y, ite_true]
    have : t^2 ≤ (X ω - mu)^2 := by
      have h1 : t * t ≤ |X ω - mu| * |X ω - mu| := mul_self_le_mul_self (le_of_lt ht) h
      have h2 : |X ω - mu| * |X ω - mu| = (X ω - mu)^2 := by rw [← sq, sq_abs]
      calc t^2 = t * t := sq t
        _ ≤ |X ω - mu| * |X ω - mu| := h1
        _ = (X ω - mu)^2 := h2
    simp [this]
  · push_neg at h
    simp only [Y]
    have : ¬(t^2 ≤ (X ω - mu)^2) := by
      intro hcontra
      have h1 : (X ω - mu) * (X ω - mu) = |X ω - mu| * |X ω - mu| := by
        rw [← sq, ← sq, sq_abs]
      have h2 : t^2 ≤ |X ω - mu|^2 := by
        calc t^2 = t * t := sq t
          _ ≤ |X ω - mu| * |X ω - mu| := by
            rw [← h1, ← sq, ← sq]
            exact hcontra
          _ = |X ω - mu|^2 := (sq _).symm
      have h3 : t ≤ |X ω - mu| := by
        by_contra hneg
        push_neg at hneg
        have : |X ω - mu| * |X ω - mu| < t * t := mul_self_lt_mul_self (abs_nonneg _) hneg
        rw [← sq, ← sq] at this
        linarith
      linarith
    simp [this, h]

/-! ### Step 2: Chernoff Bound Infrastructure -/

/-- Moment generating function: M_X(lam) = E[exp(lam·X)]. -/
noncomputable def mgf (X : (Γ → Bool) → ℝ) (M : JansonModel Γ) (lam : ℝ) : ℝ :=
  PMF.expect (product_pmf M) (fun ω => Real.exp (lam * X ω))

/-- Chernoff bound: P(X ≥ t) ≤ inf_lam { exp(-lam·t) · E[exp(lam·X)] }. -/
lemma chernoff_upper_bound (X : (Γ → Bool) → ℝ) (t : ℝ) (M : JansonModel Γ)
    (hX_nonneg : ∀ ω, 0 ≤ X ω) :
    PMF.expect (product_pmf M) (fun ω => if t ≤ X ω then (1 : ℝ) else 0)
      ≤ ⨅ (lam : ℝ) (_ : 0 < lam), Real.exp (-lam * t) * mgf X M lam := by
  admit

/-- Exponential of sum equals product of exponentials. -/
lemma exp_sum_eq_prod_exp {Γ : Type*} [Fintype Γ] (f : Γ → ℝ) :
    Real.exp (∑ v : Γ, f v) = ∏ v : Γ, Real.exp (f v) := by
  admit

/-! ### Step 3: Independence and Product PMF Properties -/

/-- For independent Bernoulli variables, E[∏ f(X_v)] = ∏ E[f(X_v)]. -/
lemma expect_prod_eq_prod_expect (M : JansonModel Γ) (f : Γ → Bool → ℝ) :
    PMF.expect (product_pmf M) (fun ω => ∏ v : Γ, f v (ω v))
      = ∏ v : Γ, PMF.expect (bernoulli_pmf M v) (f v) := by
  -- This is the key independence property
  admit

/-- MGF factorizes for sums of independent variables. -/
lemma mgf_sum_indep (M : JansonModel Γ) (X : Γ → Bool → ℝ) (lam : ℝ) :
    mgf (fun ω => ∑ v : Γ, X v (ω v)) M lam
      = ∏ v : Γ, PMF.expect (bernoulli_pmf M v) (fun b => Real.exp (lam * X v b)) := by
  admit

/-! ### Step 4: Second Moment Method for P(X = 0) -/

/-- Second moment method: P(X = 0) ≤ Var(X) / E[X]² when E[X] > 0. -/
lemma second_moment_zero_prob (X : (Γ → Bool) → ℝ) (M : JansonModel Γ)
    (hX_nonneg : ∀ ω, 0 ≤ X ω) :
    let mu := PMF.expect (product_pmf M) X
    let mu_sq := PMF.expect (product_pmf M) (fun ω => (X ω)^2)
    0 < mu →
    PMF.expect (product_pmf M) (fun ω => if X ω = 0 then (1 : ℝ) else 0)
      ≤ (mu_sq - mu^2) / mu^2 := by
  admit

/-- Variance calculation for sum of indicators with dependencies. -/
lemma variance_indicator_sum (M : JansonModel Γ) (A : Finset Γ) :
    let X := fun ω : Γ → Bool => A.sum (fun v => if ¬ ω v then (1 : ℝ) else 0)
    let mu := mu (M:=M) (A:=A)
    let variance := PMF.expect (product_pmf M) (fun ω => (X ω - mu)^2)
    variance = mu + dbar (M:=M) (A:=A) - mu^2 := by
  admit

/-! ### Step 5: Janson Assembly -/

/-- Janson's inequality: main theorem connecting second moment to exponential bound. -/
lemma janson_core_inequality (M : JansonModel Γ) (A : Finset Γ) :
    let X := fun ω : Γ → Bool => A.sum (fun v => if ¬ ω v then (1 : ℝ) else 0)
    let mu := mu (M:=M) (A:=A)
    let dbar_val := dbar (M:=M) (A:=A) + mu
    PMF.expect (product_pmf M) (fun ω => if X ω = 0 then (1 : ℝ) else 0)
      ≤ Real.exp (- mu^2 / (2 * dbar_val)) := by
  intro X mu dbar_val

  -- Step 0: Handle trivial case when mu = 0
  by_cases hmu : mu = 0
  case pos =>
    -- If mu = 0, then P(X=0) ≤ 1 and exp(0) = 1
    -- P(X=0) is a probability, hence ≤ 1
    have h_prob : PMF.expect (product_pmf M) (fun ω => if X ω = 0 then (1 : ℝ) else 0) ≤ 1 := by
      sorry -- This is a general property of indicator expectations
    have h_exp_zero : Real.exp (-mu^2 / (2 * dbar_val)) = 1 := by
      simp [hmu, sq, Real.exp_zero]
    rw [h_exp_zero]
    exact h_prob
  case neg =>
    -- mu > 0 case (the interesting case)
    have hmu_pos : 0 < mu := by
      sorry -- Need to show mu ≠ 0 implies mu > 0 (from definition of mu)

    -- Step 1: Show that mu = E[X]
    have h_mu_eq : mu = PMF.expect (product_pmf M) X := by
      sorry -- This should follow from the definition of mu in ABC.lean

    -- Step 1b: Apply second_moment_zero_prob
    have hX_nonneg : ∀ ω, 0 ≤ X ω := by
      intro ω
      sorry -- Sum of indicators is nonnegative

    have hmu_pos' : 0 < PMF.expect (product_pmf M) X := by
      rw [← h_mu_eq]; exact hmu_pos

    have h_second_moment := second_moment_zero_prob X M hX_nonneg hmu_pos'
    simp only [X] at h_second_moment

    -- Step 2: Use variance_indicator_sum to express variance
    have h_variance := variance_indicator_sum M A

    -- Step 3: Combine to get P(X=0) ≤ (mu + dbar - mu²) / mu²
    have h_bound : PMF.expect (product_pmf M) (fun ω => if X ω = 0 then (1 : ℝ) else 0)
                  ≤ (mu + dbar (M:=M) (A:=A) - mu^2) / mu^2 := by
      sorry -- Combine second moment method with variance formula

    -- Step 4: Show (mu + dbar - mu²) / mu² ≤ exp(-mu²/(2*dbar_val))
    -- This requires showing: (mu + dbar - mu²) / mu² ≤ exp(-mu²/(2*(dbar + mu)))
    have h_exp_bound : (mu + dbar (M:=M) (A:=A) - mu^2) / mu^2
                      ≤ Real.exp (- mu^2 / (2 * dbar_val)) := by
      sorry -- This is the key analytic inequality (uses convexity/Taylor)

    -- Step 5: Chain the inequalities
    calc PMF.expect (product_pmf M) (fun ω => if X ω = 0 then (1 : ℝ) else 0)
        ≤ (mu + dbar (M:=M) (A:=A) - mu^2) / mu^2 := h_bound
      _ ≤ Real.exp (- mu^2 / (2 * dbar_val)) := h_exp_bound

/-- Final form: bound_v2 proof using janson_core_inequality. -/
lemma bound_v2_from_janson (M : JansonModel Γ) (A : Finset Γ) :
    PMF.expect (product_pmf M)
      (fun ω => A.prod (fun v => if ¬ ω v then (1 : ℝ) else 0))
      ≤ (if 0 < dbar (M:=M) (A:=A) then
           Real.exp (- (mu (M:=M) (A:=A))^2 / (2 * dbar (M:=M) (A:=A)))
         else
           Real.exp (- mu (M:=M) (A:=A))) := by
  -- Split into two cases based on dbar value
  by_cases h_dbar : 0 < dbar (M:=M) (A:=A)
  case pos =>
    simp [h_dbar]
    -- Step 1: Show product indicator ≤ indicator of X = 0
    -- Product is 1 iff all indicators are 1 iff sum is |A|
    -- But we want X = 0, i.e., all events happen
    have h_prod_to_sum : ∀ (ω : Γ → Bool),
                         A.prod (fun v => if ¬ ω v then (1 : ℝ) else 0) ≤
                         (if (A.sum (fun v => if ω v then (1 : ℝ) else 0)) = 0 then (1 : ℝ) else 0) := by
      sorry -- Product is 1 iff all ¬ω v are true iff X = 0

    -- Step 2: Apply monotonicity of expectation
    have h_mono : PMF.expect (product_pmf M) (fun ω => A.prod (fun v => if ¬ ω v then (1 : ℝ) else 0))
                 ≤ PMF.expect (product_pmf M) (fun ω => if (A.sum (fun v => if ω v then (1 : ℝ) else 0)) = 0 then (1 : ℝ) else 0) := by
      sorry -- Apply PMF.expect_mono with h_prod_to_sum

    -- Step 3: Relate this to janson_core_inequality
    -- Note: janson_core_inequality uses ¬ω v, we need to connect
    sorry -- Apply janson_core_inequality and algebraic manipulation

  case neg =>
    -- Δ̄ ≤ 0 case (pure independence or trivial)
    push_neg at h_dbar
    simp only [Bool.not_eq_true]
    sorry -- When Δ̄ = 0, events are independent; use simpler bound

end JansonRoadmap

/-!
### Summary

**ABC.lean status:**
- Infrastructure: ✅ 80% complete
- Core inequality: ⚠️ `admit`

**This roadmap:**
- Breaks down the gap into ~50 lemmas
- Estimates: 2-3 weeks for full formalization
- Priority: Do this AFTER completing hπ, htail in adjacent_quality_le_ae_alt

**Current decision:**
Keep `ABC.Janson.bound_v2` as axiom, document thoroughly (pragmatic approach).
Use this roadmap if/when pursuing full formalization.
-/

-- The bound_v2 theorem is already defined in ABC.Janson
-- We don't redeclare it here to avoid conflicts.
-- Users should import ABC to access ABC.Janson.bound_v2.

end Janson

end ABC
