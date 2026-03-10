/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC018

#print "file: DkMath.ABC.ABC019"

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

/- Helper module for tail/square-part redesign.

This file centralizes the `TailBound` predicate, `sqPart` definition and
the analytic bridge lemma signatures. Proof bodies are left as `so#rry` or
short ad#mits to be completed by the Phase 3 probabilistic work.
 -/


/-- TailBound γ for triple (a,b,c): twoTail c ≤ (rad (a * b)) ^ γ (in ℝ). -/
def TailBound (γ : ℝ) (a b c : ℕ) : Prop :=
  (twoTail c : ℝ) ≤ (rad (a * b) : ℝ) ^ γ


/-- Maximal square divisor (square part) of `n`. -/
def sqPart (n : ℕ) : ℕ :=
  n.factorization.support.prod fun p => p ^ (2 * (n.factorization p / 2))


-- sqTail ≤ sqPart: prove via odd/even decomposition: c = oddPart * evenPart^2 and
-- oddPart ≤ rad, hence sqTail = oddPart * evenPart^2 / rad ≤ evenPart^2 = sqPart.
lemma sqPart_eq_evenPart_pow2 (n : ℕ) : sqPart n = (evenPart n) ^ 2 := by
  dsimp [sqPart, evenPart]
  let S := n.factorization.support
  -- Mirror the proof style used elsewhere: rewrite exponents `2*k` as `k+k`,
  -- distribute the product and use `ring` to finish.
  conv_lhs => arg 2; ext p; rw [two_mul]
  simp only [pow_add]
  -- ∏ p p^(k+k) = ∏ p (p^k * p^k) and then split the product
  rw [Finset.prod_mul_distrib]
  -- Now `(∏ p p^k) * (∏ p p^k) = (∏ p p^k)^2`
  ring


-- oddPart ≤ rad (pointwise exponent inequality)
lemma oddPart_le_rad (n : ℕ) : (oddPart n : ℝ) ≤ (rad n : ℝ) := by
  dsimp [oddPart, rad]
  let S := n.factorization.support
  -- For each p in support, v%2 ∈ {0,1}, so p^(v%2) ≤ p
  have pointwise_nat : ∀ p ∈ S, p ^ (n.factorization p % 2) ≤ p := by
    intro p hp
    rcases mem_support_factorization_iff.mp hp with ⟨_, ⟨hprime, _⟩⟩
    let v := n.factorization p
    -- v % 2 ∈ {0,1}, do case analysis
    by_cases hv0 : v % 2 = 0
    · rw [hv0]
      simp only [pow_zero, ge_iff_le]
      exact Nat.one_le_of_lt (Nat.Prime.one_lt hprime)
    · -- v % 2 ≠ 0 and v % 2 < 2 implies v % 2 = 1
      have vlt2 := Nat.mod_lt v (by norm_num : (0 : ℕ) < 2)
      have vpos : 0 < v % 2 := Nat.pos_of_ne_zero hv0
      have one_le : 1 ≤ v % 2 := Nat.succ_le_of_lt vpos
      have le1 : v % 2 ≤ 1 := Nat.le_of_lt_succ vlt2
      have req : v % 2 = 1 := Nat.le_antisymm le1 one_le
      rw [req]; simp
  -- Lift to product inequality on ℕ then cast to ℝ
  have prod_le_nat : Finset.prod S (fun p => p ^ (n.factorization p % 2)) ≤ Finset.prod S fun p => p :=
    Finset.prod_le_prod' fun p hp => (pointwise_nat p hp)
  have : (oddPart n : ℝ) ≤ (rad n : ℝ) := by
    exact_mod_cast prod_le_nat
  exact this


lemma sqTail_le_sqPart (n : ℕ) : (sqTail n : ℝ) ≤ (sqPart n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn, sqTail, sqPart]
  -- n ≠ 0: use decompositions c = sqTail * rad and c = oddPart * evenPart^2
  -- From decompositions: sqTail * rad = oddPart * evenPart^2
  have h_mul : (sqTail n : ℝ) * (rad n : ℝ) = (oddPart n : ℝ) * (evenPart n : ℝ) ^ 2 := by
    calc (sqTail n : ℝ) * (rad n : ℝ) = (n : ℝ) := by rw [nat_eq_sqTail_mul_rad_real n hn]
    _ = (oddPart n : ℝ) * (evenPart n : ℝ) ^ 2 := by rw [decomp_oddPart_evenPart_real n hn]
  -- rad > 0 so we can divide both sides
  have hrad_pos : 0 < (rad n : ℝ) := rad_pos_real n
  -- oddPart ≤ rad on ℝ, multiply both sides by evenPart^2 ≥ 0
  have h_odd_le_rad := oddPart_le_rad n
  have h_even_sq_nonneg : 0 ≤ (evenPart n : ℝ) ^ 2 := by apply pow_two_nonneg
  have h_mul_bound : (oddPart n : ℝ) * (evenPart n : ℝ) ^ 2 ≤ (rad n : ℝ) * (evenPart n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h_odd_le_rad h_even_sq_nonneg
  -- Replace oddPart * even^2 by sqTail * rad and deduce sqTail * rad ≤ rad * even^2
  have h_le := by rwa [← h_mul] at h_mul_bound
  -- rewrite evenPart^2 to sqPart to match target, using sqPart_eq_evenPart_pow2 but at real level
  have heq_real : (evenPart n : ℝ) ^ 2 = (sqPart n : ℝ) := by
    have hnat := sqPart_eq_evenPart_pow2 n
    exact_mod_cast hnat.symm
  -- swap factors on RHS to get form A*B ≤ C*B, then replace evenPart^2 by sqPart
  rw [mul_comm (rad n : ℝ) ((evenPart n : ℝ) ^ 2)] at h_le
  rw [heq_real] at h_le
  -- rad > 0 so cancel on right to get sqTail ≤ sqPart
  exact le_of_mul_le_mul_right h_le (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (one_le_rad_real n))


/-- Unconditional decomposition bound using sqPart: c ≤ rad(c) * sqPart(c). -/
lemma c_le_sqPart_mul_rad (n : ℕ) : (n : ℝ) ≤ (rad n : ℝ) * (sqPart n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  -- Use factorization: n = (rad n) * ∏ p ^ (2*(v_p/2)) * piSqRad? but simpler: exponents decomp
  -- We have n = rad n * sqTail n and sqTail n ≤ sqPart n by previous lemma
  have h := nat_eq_sqTail_mul_rad_real n hn
  -- h : (n : ℝ) = (sqTail n : ℝ) * (rad n : ℝ)
  rw [h]
  -- rewrite goal RHS to (sqPart n) * (rad n) so we can apply mul_le_mul_of_nonneg_right
  rw [mul_comm (rad n : ℝ) (sqPart n : ℝ)]
  apply mul_le_mul_of_nonneg_right (sqTail_le_sqPart n) (by norm_cast; exact Nat.cast_nonneg (rad n))


/-- Generalized analytic bridge: assumes piSqRad and TailBound and concludes quality bound.
    This is the API the main proof should call. -/
lemma quality_le_of_pi_tail_general
  {a b c : ℕ} {ε δ γ : ℝ}
  (hε_pos : 0 < ε) (hsum : a + b = c) (hcop : Nat.Coprime a b)
  (hπ : (piSqRad c : ℝ) ≤ (rad (a * b) : ℝ) ^ δ)
  (htail : TailBound γ a b c)
  (hδγ_nonneg : 0 ≤ δ + γ) (hδγ : δ + γ ≤ ε) :
  quality (Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  -- Derive the `htail'` shape used by `quality_le_of_pi_tail`:
  -- from decomp: (c : ℝ) = (piSqRad c) * (rad c) * (twoTail c)
  by_cases hc : c = 0
  · -- pathological c = 0 case: quality = 0 ≤ 1+ε
    have hqual_zero : quality (Triple.mk a b c hsum hcop) = 0 := by
      simp [quality, hc]
    have : (0 : ℝ) ≤ 1 + ε := by linarith
    simpa [hqual_zero] using this
  -- c ≠ 0: use decomposition and TailBound
  have hc_ne : c ≠ 0 := hc
  have hdec := decomp_piRad_twoTail_real c hc_ne
  -- TailBound gives twoTail ≤ rad(a*b)^γ
  have h_two_le := htail
  -- Multiply both sides by (piSqRad c * rad c) ≥ 0 to get the desired shape
  have h_pos_left : 0 ≤ (piSqRad c : ℝ) * (rad c : ℝ) := by
    have h1 : (1 : ℝ) ≤ (piSqRad c : ℝ) := by exact_mod_cast (piSqRad_ge_one c)
    have h2 : 0 < (rad c : ℝ) := rad_pos_real c
    exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) h1) (le_of_lt h2)
  have hmul := mul_le_mul_of_nonneg_left h_two_le h_pos_left
  -- Replace (pi*rad)*twoTail by c using hdec
  have htail' : (c : ℝ) ≤ (piSqRad c : ℝ) * (rad (a*b) : ℝ) ^ γ * (rad c : ℝ) := by
    -- rewrite P * twoTail = c using hdec.symm, then reorder factors by `ring`
    rw [hdec.symm] at hmul
    have : (piSqRad c : ℝ) * (rad c : ℝ) * (rad (a * b) : ℝ) ^ γ
        = (piSqRad c : ℝ) * (rad (a * b) : ℝ) ^ γ * (rad c : ℝ) := by ring
    rw [this] at hmul
    exact hmul
  -- Now apply the existing analytic bridge
  exact quality_le_of_pi_tail δ γ ε hε_pos hcop hsum hπ htail' hδγ_nonneg hδγ


/-
Basic inequality relating twoTail (log) to the sum of excess exponents times log p.
This turns the multiplicative definition of `twoTail` into an additive log upper bound
using the factorization support. We state the real-log version which is convenient
in the analytic parts of the proof.
-/

lemma log_twoTail_le_excess_sum (c : ℕ) (hc : c ≠ 0) :
  Real.log (twoTail c : ℝ)
    ≤ ∑ p ∈ c.factorization.support, (((c.factorization p - 2) : ℕ) : ℝ) * Real.log (p : ℝ) := by
  -- Use the already-proved equality (see `ABCFinalProofs.log_twoTail_eq_sum_vplus`)
  have h_eq := ABC.log_twoTail_eq_sum_vplus c hc
  -- `primeFactors` equals `factorization.support` for `c`; rewrite and finish by reflexivity
  have h_support : c.primeFactors = c.factorization.support := by
    ext p
    simp [Nat.support_factorization, Nat.mem_primeFactors, ne_eq]
  exact ge_of_eq (id (Eq.symm h_eq))

/- ### Probability-free Chernoff Machinery

The following lemmas provide finite-averaging versions of Markov's inequality
and layer-cake representation, avoiding measure theory entirely. These are
the core tools for MGF/Chernoff bounds in Phase 3.
-/

-- Finite-set Markov inequality: for non-negative Y and threshold A > 0,
-- count of {n | Y n > A} is bounded by (∑ Y n) / A
lemma markov_card_bound
  (X : ℕ) (Y : ℕ → ℝ) (hY : ∀ n ≤ X, 0 ≤ Y n) {A : ℝ} (hA : 0 < A) :
  ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ)
    ≤ (Finset.sum (Finset.Icc 0 X) (fun n => Y n)) / A := by
  classical
  have h_calc : ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ) * A
      ≤ Finset.sum (Finset.Icc 0 X) (fun n => Y n) := by
    calc ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ) * A
        = Finset.sum (Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)) (fun _ => A) := by
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
  calc ((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ)
      = (((Finset.filter (fun n => n ≤ X ∧ A < Y n) (Finset.Icc 0 X)).card : ℝ) * A) / A := by
        field_simp
    _ ≤ (Finset.sum (Finset.Icc 0 X) (fun n => Y n)) / A := by
        apply div_le_div_of_nonneg_right h_calc; positivity

-- Basic telescoping lemma: ∑_{k=1}^m (f k - f(k-1)) = f m - f 0
lemma sum_Icc_telescope (m : ℕ) (f : ℕ → ℝ) :
  Finset.sum (Finset.Icc 1 m) (fun k => f k - f (k-1)) = f m - f 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · -- Direct induction on m
    induction m with
    | zero => simp at hm
    | succ m ihm =>
        by_cases hm0 : m = 0
        · simp [hm0]
        · rw [Finset.sum_Icc_succ_top]
          · rw [ihm hm0]
            simp
          · omega

-- Layer-cake representation for exponential of integer-valued function
-- ∑ e^{t V(n)} ≤ (X+1) + (e^t - 1) * ∑_{k≥1} e^{t(k-1)} * #{n | V(n) ≥ k}
-- Bounded version: assumes V n ≤ X+1 for all n ≤ X
lemma exp_layer_cake
  (X : ℕ) (t : ℝ) (ht : 0 < t) (V : ℕ → ℕ)
  (hVbd : ∀ n ≤ X, V n ≤ X + 1) :
  (Finset.sum (Finset.Icc 0 X) (fun n => Real.exp (t * (V n : ℝ))))
    ≤ (X + 1 : ℝ) + (Real.exp t - 1) *
        (Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
          Real.exp (t * ((k : ℝ) - 1)) *
          ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ))) := by
  classical
  -- Step 1: Decompose e^{tV(n)} = 1 + ∑_{k=1}^{V(n)} (e^{tk} - e^{t(k-1)})
  have h_decomp : ∀ n ≤ X, Real.exp (t * (V n : ℝ))
      = 1 + Finset.sum (Finset.Icc 1 (V n)) (fun k => Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ))) := by
    intro n _
    by_cases hV : V n = 0
    · simp [hV]
    · -- Telescoping sum
      have h_tele : Finset.sum (Finset.Icc 1 (V n)) (fun k => Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ)))
          = Real.exp (t * (V n : ℝ)) - 1 := by
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
  -- Step 2: Sum both sides over n
  calc Finset.sum (Finset.Icc 0 X) (fun n => Real.exp (t * (V n : ℝ)))
      = Finset.sum (Finset.Icc 0 X) (fun n =>
          1 + Finset.sum (Finset.Icc 1 (V n)) (fun k =>
            Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ)))) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_Icc] at hn
        exact h_decomp n hn.2
    _ = (X + 1) + Finset.sum (Finset.Icc 0 X) (fun n =>
          Finset.sum (Finset.Icc 1 (V n)) (fun k =>
            Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const]
        have h_card : (Finset.Icc 0 X).card = X + 1 := by rw [Nat.card_Icc]; omega
        rw [h_card]
        simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    _ ≤ (X + 1) + (Real.exp t - 1) *
          Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
            Real.exp (t * ((k : ℝ) - 1)) *
            ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ)) := by
        -- Factor out (e^t - 1) from differences (for k ≥ 1)
        have h_factor : ∀ k : ℕ, 1 ≤ k → Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ))
            = (Real.exp t - 1) * Real.exp (t * ((k-1) : ℝ)) := by
          intro k hk
          have h_eq : (k : ℝ) = ((k-1) : ℝ) + 1 := by simp
          rw [h_eq, mul_add, Real.exp_add]
          ring_nf
        -- Rewrite double sum using factorization
        have h_rewrite : ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n),
            (Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ)))
            = (Real.exp t - 1) * ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n),
                Real.exp (t * ((k-1) : ℝ)) := by
          trans (∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n),
            (Real.exp t - 1) * Real.exp (t * ((k-1) : ℝ)))
          · apply Finset.sum_congr rfl
            intro n _
            apply Finset.sum_congr rfl
            intro k hk
            exact h_factor k (Finset.mem_Icc.mp hk).1
          · simp [Finset.mul_sum]
        rw [h_rewrite]
        -- Key: show (e^t - 1) ≥ 0 for t > 0
        have ht_pos : 0 ≤ Real.exp t - 1 := by
          have : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr (le_of_lt ht)
          linarith
        gcongr
        -- Interchange: ∑_n ∑_{k ≤ V(n)} f(k) = ∑_{k ≤ X+1} f(k) * #{n : k ≤ V(n)}
        -- Using boundedness V n ≤ X+1, we can rewrite as equality with indicators
        calc ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n), Real.exp (t * ((k-1) : ℝ))
            = ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (X+1),
                if k ≤ V n then Real.exp (t * ((k-1) : ℝ)) else 0 := by
              apply Finset.sum_congr rfl
              intro n hn
              -- Use boundedness: V n ≤ X+1 for n ≤ X
              have hV : V n ≤ X+1 := hVbd n (Finset.mem_Icc.mp hn).2
              -- Rewrite Icc 1 (V n) as filter of Icc 1 (X+1)
              rw [← Finset.sum_filter]
              apply Finset.sum_congr
              · ext k
                simp only [Finset.mem_filter, Finset.mem_Icc]
                constructor
                · intro ⟨h1, h2⟩
                  exact ⟨⟨h1, Nat.le_trans h2 hV⟩, h2⟩
                · intro ⟨⟨h1, _⟩, h2⟩
                  exact ⟨h1, h2⟩
              · intro k _; rfl
          _ = ∑ k ∈ Finset.Icc 1 (X+1), ∑ n ∈ Finset.Icc 0 X,
                if k ≤ V n then Real.exp (t * ((k-1) : ℝ)) else 0 := Finset.sum_comm
          _ = ∑ k ∈ Finset.Icc 1 (X+1), Real.exp (t * ((k-1) : ℝ)) *
                (Finset.filter (fun n => k ≤ V n) (Finset.Icc 0 X)).card := by
              apply Finset.sum_congr rfl
              intro k _
              rw [← Finset.sum_filter, Finset.sum_const]
              simp [nsmul_eq_mul, mul_comm]
          _ ≤ ∑ k ∈ Finset.Icc 1 (X+1), Real.exp (t * ((k-1) : ℝ)) *
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

end ABC
