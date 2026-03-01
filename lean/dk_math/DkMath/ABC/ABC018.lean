/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC017

#print "file: DkMath.ABC.ABC018"

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

/- For a given prime p and threshold k, count n ≤ X where v_p(n(n+1)) ≥ k.
    Such n must satisfy either n ≡ 0 (mod p^k) or n+1 ≡ 0 (mod p^k).
    Therefore there are at most 2⌈X/p^k⌉ such n. -/

/- The proof needs small auxiliary facts about counting n with m | n or m | n+1; isolate them as private lemmas.-/
private lemma count_multiples_le_ceil (X m : ℕ) (_hm_pos : 0 < m) :
    ((Finset.Icc 0 X).filter fun n => m ∣ n).card ≤ ⌈(X : ℝ) / (m : ℝ)⌉₊ + 1 := by
  classical
  let S := Finset.range (X + 1)
  -- use the standard lemma: range (X+1) = Icc 0 X
  have h_range : Finset.Icc 0 X = S := (Nat.range_succ_eq_Icc_zero X).symm
  let Ppos := S.filter fun k => k ≠ 0 ∧ m ∣ k
  have hP_card : Ppos.card = X / m := by simpa using (Nat.card_multiples' X m)
  have h0_not_mem : (0 : ℕ) ∉ Ppos := by
    intro h
    let hmem := Finset.mem_filter.1 h
    rcases hmem with ⟨hrange, hprop⟩
    rcases hprop with ⟨hne, hdiv⟩
    exact hne rfl
  have h_eq : (S.filter fun k => m ∣ k) = insert (0 : ℕ) Ppos := by
    ext a
    constructor
    · intro h
      let ⟨ha_range, ha_div⟩ := Finset.mem_filter.1 h
      by_cases ha0 : a = 0
      · rw [ha0]
        exact Finset.mem_insert_self 0 Ppos
      · have haP : a ∈ Ppos := Finset.mem_filter.2 ⟨ha_range, ⟨ha0, ha_div⟩⟩
        exact Finset.mem_insert_of_mem haP
    · intro h
      let hmem := Finset.mem_insert.1 h
      rcases hmem with ha_eq | ha_in
      · -- a = 0
        -- ha_eq : a = 0
        rw [ha_eq]
        have hs0 : (0 : ℕ) ∈ S := Finset.mem_range.mpr (Nat.zero_lt_succ X)
        have hdiv0 : m ∣ 0 := dvd_zero m
        exact Finset.mem_filter.2 ⟨hs0, hdiv0⟩
      · -- a ∈ Ppos
        let ⟨ha_range, ha_prop⟩ := Finset.mem_filter.1 ha_in
        rcases ha_prop with ⟨_, ha_div⟩
        exact Finset.mem_filter.2 ⟨ha_range, ha_div⟩
  -- Use Icc = S to rewrite the filtered Icc as the filtered S, then compute the card
  have Icc_eq_range : (Finset.Icc 0 X).filter fun n => m ∣ n = (S.filter fun n => m ∣ n) := by
    rw [h_range]
  have rhs_card : (S.filter fun k => m ∣ k).card = X / m + 1 := by
    rw [h_eq]
    have : (insert (0 : ℕ) Ppos).card = Ppos.card + 1 := Finset.card_insert_of_notMem h0_not_mem
    rw [this, hP_card]
  have final_card_eq : ((Finset.Icc 0 X).filter fun n => m ∣ n).card = X / m + 1 := by
    rw [Icc_eq_range]
    exact rhs_card
  -- rewrite the card equality and reduce to a nat inequality involving the ceiling
  have final_card_eq' : ((Finset.Icc 0 X).filter fun n => m ∣ n).card = X / m + 1 := final_card_eq
  -- show X / m ≤ ⌈(X : ℝ) / (m : ℝ)⌉₊ by working at the real level then casting
  have h_cast_div : ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / (m : ℝ) := Nat.cast_div_le
  have h_le_ceil : (X : ℝ) / (m : ℝ) ≤ (⌈(X : ℝ) / (m : ℝ)⌉₊ : ℝ) := Nat.le_ceil ((X : ℝ) / (m : ℝ))
  have h_trans : ((X / m : ℕ) : ℝ) ≤ (⌈(X : ℝ) / (m : ℝ)⌉₊ : ℝ) := le_trans h_cast_div h_le_ceil
  have h_nat_le : X / m ≤ ⌈(X : ℝ) / (m : ℝ)⌉₊ := by exact_mod_cast h_trans
  rw [final_card_eq']
  exact Nat.add_le_add h_nat_le (le_refl 1)



-- ========================================================================
-- Auxiliary lemmas for heavy-affected n counting
-- ========================================================================



private lemma count_shifted_multiples_le_ceil (X m : ℕ) (hm_pos : 0 < m) :
    ((Finset.Icc 0 X).filter fun n => m ∣ n + 1).card
    ≤ ⌈(X : ℝ) / (m : ℝ)⌉₊ + 1 := by
  classical
  let S0 := (Finset.Icc 0 X).filter fun n => m ∣ n + 1
  let T := (Finset.range (X + 2)).filter fun k => k ≠ 0 ∧ m ∣ k
  let f := fun a => a + 1
  have img_subset : (S0.image f) ⊆ T := by
    intro b hb
    simp only [Finset.mem_image] at hb
    rcases hb with ⟨a, haS0, rfl⟩
    let ha' := Finset.mem_filter.1 haS0
    rcases ha' with ⟨ha_range, ha_div⟩
    let ⟨_, haX⟩ := Finset.mem_Icc.1 ha_range
    have h_le : a + 1 ≤ X + 1 := by linarith [haX]
    have h_lt : a + 1 < X + 2 := by simpa using (Nat.lt_succ_iff.mpr h_le)
    have ne0 : a + 1 ≠ 0 := Nat.succ_ne_zero a
    exact Finset.mem_filter.2 ⟨Finset.mem_range.mpr h_lt, ⟨ne0, ha_div⟩⟩
  have subset_img : T ⊆ (S0.image f) := by
    intro b hb
    rcases Finset.mem_filter.1 hb with ⟨hb_range, ⟨hb_ne0, hb_div⟩⟩
    have hb_lt : b < X + 2 := Finset.mem_range.1 hb_range
    have hb_le : b ≤ X + 1 := Nat.lt_succ_iff.mp hb_lt
    let a := b - 1
    have hb_pos : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb_ne0)
    have ha1 : a + 1 = b := by simp only [a]; exact Nat.sub_add_cancel hb_pos
    have ha_le : a ≤ X := by
      have : a + 1 ≤ X + 1 := by rw [ha1]; exact hb_le
      exact Nat.le_of_succ_le_succ this
    have ha_Icc : a ∈ Finset.Icc 0 X := Finset.mem_Icc.mpr ⟨Nat.zero_le a, ha_le⟩
    apply Finset.mem_image.mpr
    exact ⟨a, Finset.mem_filter.2 ⟨ha_Icc, by rw [ha1]; exact hb_div⟩, by dsimp [f]; rw [ha1]⟩
  have img_eq : S0.image f = T := by
    ext x
    constructor
    · intro h; exact img_subset h
    · intro h; exact subset_img h
  have finj : Function.Injective f := Nat.succ_injective
  have h_card_eq : S0.card = T.card := by
    have : (S0.image f).card = S0.card := Finset.card_image_of_injective S0 finj
    calc S0.card = (S0.image f).card := by rw [this.symm]
      _ = T.card := by rw [img_eq]
  have hT_card : T.card = (X + 1) / m := by
    simpa using (Nat.card_multiples' (X + 1) m)
  have hS0 : S0.card = (X + 1) / m := by rw [h_card_eq, hT_card]
  have h_div_le : (X + 1) / m ≤ X / m + 1 := by
    -- Let q = X / m and r = X % m. We have X = q*m + r, 0 ≤ r < m.
    have r_lt : X % m < m := Nat.mod_lt X hm_pos
    have r_le : X % m ≤ m - 1 := Nat.le_pred_of_lt r_lt
    have h1 : X + 1 = m * (X / m) + X % m + 1 := by rw [Nat.div_add_mod X m]
    -- Compute X + 1 = q*m + r + 1 ≤ q*m + m = (q + 1) * m
    have hsum : X + 1 ≤ m * (X / m + 1) := by
      rw [h1]
      -- X % m + 1 ≤ m since X % m ≤ m - 1
      have : X % m + 1 ≤ m := by linarith [r_le]
      calc
        m * (X / m) + X % m + 1 ≤ m * (X / m) + m := by
          apply add_le_add_right this (m * (X / m))
        _ = m * (X / m + 1) := by ring
    -- divide both sides by m and simplify the RHS using mul_div_cancel
    have hdiv := Nat.div_le_div_right (c := m) hsum
    have hm_neq : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos
    have rhs_simp : (m * (X / m + 1)) / m = X / m + 1 := by
      rw [mul_comm]
      exact Nat.mul_div_cancel (X / m + 1) hm_pos
    -- rewrite the RHS of hdiv using rhs_simp and finish
    rw [rhs_simp] at hdiv
    exact hdiv
  have h_nat_le_ceil : X / m ≤ ⌈(X : ℝ) / (m : ℝ)⌉₊ := by
    have h_cast_div : ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / (m : ℝ) := Nat.cast_div_le
    have h_trans' := le_trans h_cast_div (Nat.le_ceil ((X : ℝ) / (m : ℝ)))
    exact_mod_cast h_trans'
  calc
    S0.card = (X + 1) / m := hS0
    _ ≤ X / m + 1 := h_div_le
    _ ≤ ⌈(X : ℝ) / (m : ℝ)⌉₊ + 1 := by exact Nat.add_le_add h_nat_le_ceil (le_refl 1)


lemma count_n_with_high_vp_bound (p k X : ℕ) (hp : p.Prime) (_hk : k ≥ 1) :
    ((Finset.Icc 0 X).filter (fun n => (n * (n + 1)).factorization p ≥ k)).card
    ≤ 2 * ⌈(X : ℝ) / (p ^ k : ℝ)⌉₊ + 2 := by
  classical
  -- 素数冪が互いに素な積を割るなら一方を割る
  have prime_pow_dvd_of_dvd_mul_coprime :
      ∀ {a b m : ℕ}, Nat.Coprime a b → (p^m ∣ a*b) → (p^m ∣ a) ∨ (p^m ∣ b) := by
    intro a b m hcop hdiv
    -- p は素数なので、p^m | a*b かつ gcd(a,b)=1 なら
    -- v_p(a*b) = v_p(a) + v_p(b) ≥ m
    -- gcd(a,b)=1 より v_p(a)=0 または v_p(b)=0
    -- よって v_p(a) ≥ m または v_p(b) ≥ m
    by_cases ha : a = 0
    · -- a = 0 なら p^m | 0*b = 0 で自明に p^m | 0
      left
      simp [ha]
    by_cases hb : b = 0
    · -- b = 0 なら p^m | a*0 = 0 で自明に p^m | 0
      right
      simp [hb]
    -- a, b ≠ 0 の場合
    -- Coprime a b と p | a*b から、p∤a ならば p^m | b が従う
    -- factorization の加法性: v_p(a*b) = v_p(a) + v_p(b)
    -- gcd(a,b)=1 より、p が a を割るなら b を割らない（その逆も）
    -- したがって v_p(a) = 0 または v_p(b) = 0
    have hab : (a * b).factorization p = a.factorization p + b.factorization p := by
      have h := Nat.factorization_mul ha hb
      rw [h]
      rfl
    -- hdiv を factorization の言葉で書き換え
    have hdiv' : m ≤ (a * b).factorization p := by
      rw [← hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb)]
      exact hdiv
    rw [hab] at hdiv'
    -- hdiv': m ≤ a.factorization p + b.factorization p
    -- coprime より、どちらかが 0
    have hcop' : (a.factorization p = 0) ∨ (b.factorization p = 0) := by
      -- gcd(a,b) = 1 なので、p が両方を割ることはない
      by_contra h
      push_neg at h
      have hpa' : p ∣ a := by
        rw [hp.dvd_iff_one_le_factorization ha]
        omega
      have hpb' : p ∣ b := by
        rw [hp.dvd_iff_one_le_factorization hb]
        omega
      -- p | a かつ p | b なら p | gcd(a,b) = 1 で矛盾
      have : p ∣ a.gcd b := Nat.dvd_gcd hpa' hpb'
      rw [hcop] at this
      exact hp.not_dvd_one this
    cases hcop' with
    | inl h =>
      right
      simp only [h, zero_add] at hdiv'
      rw [hp.pow_dvd_iff_le_factorization hb]
      exact hdiv'
    | inr h =>
      left
      simp only [h, add_zero] at hdiv'
      rw [hp.pow_dvd_iff_le_factorization ha]
      exact hdiv'

  set m : ℕ := p ^ k with hm

  -- フィルタ集合 ⊆ {n | m∣n} ∪ {n | m∣n+1}
  have h_subset :
      ((Finset.Icc 0 X).filter (fun n => (n * (n + 1)).factorization p ≥ k))
      ⊆ ((Finset.Icc 0 X).filter (fun n => m ∣ n))
        ∪ ((Finset.Icc 0 X).filter (fun n => m ∣ n + 1)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union] at hn ⊢
    -- v_p(n(n+1)) ≥ k ⇒ p^k | n(n+1)
    have hpk : m ∣ n * (n+1) := by
      -- factorization p ≥ k means p^k divides the number
      rw [hm]
      by_cases h0 : n * (n+1) = 0
      · -- n(n+1) = 0 なら p^k | 0 は自明
        simp [h0]
      · -- n(n+1) ≠ 0 なら Prime.pow_dvd_iff_le_factorization を使う
        rw [hp.pow_dvd_iff_le_factorization h0]
        exact hn.2
    -- gcd(n, n+1) = 1
    have hcop : Nat.Coprime n (n+1) := Nat.coprime_self_succ n
    -- 素数冪割込み補題から二択
    have := prime_pow_dvd_of_dvd_mul_coprime hcop hpk
    cases this with
    | inl hdiv =>
      left
      exact ⟨hn.1, hdiv⟩
    | inr hdiv =>
      right
      exact ⟨hn.1, hdiv⟩

  -- 個数上界：各フィルタ集合の個数を数える
  -- 0 < m from p.Prime and k ≥ 1 (needed for the auxiliary lemmas)
  have hm_pos : 0 < m := by
    have hm_ne : m ≠ 0 := by
      -- m = p^k and p is prime, so p ≠ 0 and p^k ≠ 0
      rw [hm]
      exact pow_ne_zero k (Nat.Prime.ne_zero hp)
    exact Nat.pos_of_ne_zero hm_ne
  have h_card_A := count_multiples_le_ceil X m hm_pos
  have h_card_B := count_shifted_multiples_le_ceil X m hm_pos

  -- 合併の個数
  calc ((Finset.Icc 0 X).filter (fun n => (n * (n + 1)).factorization p ≥ k)).card
      ≤ (((Finset.Icc 0 X).filter (fun n => m ∣ n))
         ∪ ((Finset.Icc 0 X).filter (fun n => m ∣ n + 1))).card := by
          exact Finset.card_le_card h_subset
    _ ≤ ((Finset.Icc 0 X).filter (fun n => m ∣ n)).card
        + ((Finset.Icc 0 X).filter (fun n => m ∣ n + 1)).card := by
          exact Finset.card_union_le _ _
    _ ≤ (⌈(X : ℝ) / (m : ℝ)⌉₊ + 1) + (⌈(X : ℝ) / (m : ℝ)⌉₊ + 1) := by
          exact Nat.add_le_add h_card_A h_card_B
    _ = 2 * ⌈(X : ℝ) / (m : ℝ)⌉₊ + 2 := by ring
    _ = 2 * ⌈(X : ℝ) / (p ^ k : ℝ)⌉₊ + 2 := by
          -- m = p^k なので置換、キャストの正規化
          rw [hm]
          norm_cast


/-- Heavy primes (with large v_p for some n) affect at most sublinear n.
    Given a set S of "heavy" primes with #S ≤ K, the number of n ≤ X
    affected by at least one p ∈ S is bounded by f(K, X). -/
lemma heavy_primes_affect_sublinear_n
    (S : Finset ℕ) (X : ℕ) (K : ℕ) (_hS_card : S.card ≤ K)
    (hS_prime : ∀ p ∈ S, p.Prime)
    (_hS_heavy : ∀ p ∈ S, ∃ (n : ℕ), n ≤ X ∧ (n * (n + 1)).factorization p ≥ 3) :
   ((Finset.Icc 0 X).filter (fun n =>
     ∃ p ∈ S, (n*(n+1)).factorization p ≥ 3)).card
   ≤ ∑ p ∈ S, (2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2) := by
  -- Strategy: Union bound over all primes in S
  -- For each p ∈ S, at most 2⌈X/p³⌉ + 2 affected n (from count_n_with_high_vp_bound)
  -- Since p ≥ 2 for any prime, p³ ≥ 8, so ⌈X/p³⌉ ≤ ⌈X/8⌉
  -- Total: #S * (2⌈X/8⌉ + 2) ≤ K * (⌈X/4⌉ + 1) (rough bound)
  --
  -- More precise: Use inclusion-exclusion or just union bound
  -- |⋃_{p∈S} A_p| ≤ ∑_{p∈S} |A_p| where A_p = {n | v_p(n(n+1)) ≥ 3}
  /- Convert the existential-filter into a union over p ∈ S of the single-p filters -/
  classical
  let A (p : ℕ) := (Finset.Icc 0 X).filter fun n => (n * (n + 1)).factorization p ≥ 3
  -- The filter is included in the biUnion over p of A p
  have filter_subset_biUnion :
      ((Finset.Icc 0 X).filter (fun n => ∃ p ∈ S, (n * (n + 1)).factorization p ≥ 3))
    ⊆ S.biUnion A := by
    intro n hn
    rcases Finset.mem_filter.1 hn with ⟨hnX, hex⟩
    obtain ⟨p, hpS, hpv⟩ := hex
    -- build the proof using tactics: show n ∈ A p then finish with mem_biUnion
    apply Finset.mem_biUnion.2
    use p
    constructor
    · exact hpS
    · dsimp [A]
      apply Finset.mem_filter.mpr
      exact ⟨hnX, hpv⟩

  -- Now bound the cardinality of the union by the sum of cardinals
  -- card(filter) ≤ card(biUnion A) ≤ sum_p card (A p)
  have filter_card_le_biUnion : ((Finset.Icc 0 X).filter fun n => ∃ p ∈ S, (n * (n + 1)).factorization p ≥ 3).card
    ≤ (S.biUnion A).card := by
    apply Finset.card_le_card filter_subset_biUnion
  have union_le_sum : (S.biUnion A).card ≤ ∑ p ∈ S, (A p).card := by
    apply Finset.card_biUnion_le

  -- For each p ∈ S bound (A p).card by count_n_with_high_vp_bound
  have pointwise_bound : ∀ p ∈ S, (A p).card ≤ 2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2 := by
    intro p hpS
    -- apply lemma from ABCFinalProofs: count_n_with_high_vp_bound (with threshold k = 3)
    have hp_prime := hS_prime p hpS
    have hbound := count_n_with_high_vp_bound p 3 X hp_prime (by norm_num : 3 ≥ 1)
    -- A p = filter for v_p ≥ 3 by definition
    simpa [A] using hbound

  -- Sum the pointwise bounds over S
  have sum_bound : ∑ p ∈ S, (A p).card ≤ ∑ p ∈ S, (2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2) :=
    Finset.sum_le_sum fun p hp => pointwise_bound p hp

  -- Now compare each ceil ⌈X / p^3⌉ with ⌈X / 4⌉: since p ≥ 2 we have p^3 ≥ 8 ≥ 4, so X/p^3 ≤ X/4
  have ceil_mono_for_p : ∀ p ∈ S, ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ ≤ ⌈(X : ℝ) / 4⌉₊ := by
    intro p hpS
    have hp_prime := hS_prime p hpS
    have h2 : 2 ≤ p := by exact Nat.succ_le_of_lt (Nat.Prime.one_lt hp_prime)
    have h8le : 8 ≤ p ^ 3 := by
      have h2' : 2 ≤ p := h2
      have h4le : 4 ≤ p * p := by
        calc 4 = 2 * 2 := by norm_num
          _ ≤ p * p := by apply Nat.mul_le_mul h2' h2'
      calc 8 = 4 * 2 := by norm_num
        _ ≤ (p * p) * p := by apply Nat.mul_le_mul h4le h2'
        _ = p ^ 3 := by simp [pow_succ]
    have h4_le_p3_nat : (4 : ℕ) ≤ p ^ 3 := by
      exact Nat.le_trans (by norm_num : 4 ≤ 8) h8le
    -- cast to reals and use monotonicity of division
    have h4_le_p3_nat : (4 : ℕ) ≤ p ^ 3 := by
      have : 4 ≤ 8 := by norm_num
      exact Nat.le_trans this h8le
    have h4_le_p3 : (4 : ℝ) ≤ (p ^ 3 : ℝ) := by exact_mod_cast h4_le_p3_nat
    have hX_nonneg : 0 ≤ (X : ℝ) := by exact_mod_cast Nat.zero_le X
    have : (X : ℝ) / (p ^ 3 : ℝ) ≤ (X : ℝ) / 4 :=
      -- use div_le_div_of_nonneg_left: for 0 ≤ a, 0 < c, c ≤ b → a / b ≤ a / c
      div_le_div_of_nonneg_left hX_nonneg (by norm_num : (0 : ℝ) < 4) h4_le_p3
    -- apply monotonicity of ceil: a ≤ b → ceil a ≤ ceil b
    exact Nat.ceil_mono this

  -- Combine inequalities to get a sum-over-S form; the caller can further bound this sum
  calc ((Finset.Icc 0 X).filter (fun n => ∃ p ∈ S, (n*(n+1)).factorization p ≥ 3)).card
      ≤ (S.biUnion A).card := by apply filter_card_le_biUnion
    _ ≤ ∑ p ∈ S, (A p).card := by apply union_le_sum
    _ ≤ ∑ p ∈ S, (2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2) := by exact_mod_cast sum_bound

end ABC
