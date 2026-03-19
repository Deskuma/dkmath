/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC

set_option linter.style.emptyLine false
set_option linter.style.longLine false

/-!
Auxiliary lemmas used in the mgf_twoTail_log argument.
These are small, self-contained statements that will be proved in subsequent commits.
 - `finset_holder_equal_power` : equal-exponent Hölder bound for finite products over a finite set
 - `large_primes_tail_bound` : tail sum over large primes is bounded by a convergent series
 - `mgf_vp_base_apply` : wrapper to apply `mgf_vp_base` uniformly over primes
 -/

-- Generalized equal-exponent Hölder inequality for finite products over finite sets
-- Proof strategy:
-- 1. Induction on s using Finset.induction_on (revert F/hF to keep IH generic)
-- 2. Base case (empty): impossible by s.Nonempty assumption
-- 3. Singleton case s = {a}: both sides equal average of F a, trivial by simp
-- 4. Inductive case s = insert a s' with s' nonempty:
--    - Let m = s'.card + 1, q = m/(m-1), define G n = ∏_{b∈s'} F b n, H b n = (F b n)^q
--    - Apply 2-term Hölder (Real.inner_le_Lp_mul_Lq) to F a and G with exponents m, q
--    - Apply IH to H (tail) to bound (∑ G^q)^(1/q) in terms of powers of F_b
--    - Key algebra: q * s'.card = m (cancels denominators), (X+1) factors simplify
--    - Combine Hölder bound with IH bound via multiplication and Finset.prod_insert
-- Technical notes:
-- - Need Real.finset_prod_rpow to distribute rpow over products
-- - Need Real.rpow_mul for nested rpow simplification (a^b)^c = a^(bc)
-- - r := (s.card : ℝ) must be unfolded carefully in proofs (not definitional equality)
-- - Finset.prod_const converts ∏ c to c^(card), then use rpow laws




namespace ABC


section RX1_defs

/-- RX1 X := (↑X+1) -/
def RX1 (X : ℕ) : ℝ := (X + 1 : ℝ)  -- (↑X+1)

/-- RX1 is positive -/
lemma RX1_pos (X : ℕ) : 0 < RX1 X := by
  dsimp [RX1]
  norm_cast
  simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]

/-- RX1 is nonnegative -/
lemma RX1_nonneg (X : ℕ) : 0 ≤ RX1 X := by
  dsimp [RX1]
  norm_cast
  simp only [le_add_iff_nonneg_left, zero_le]

/-- RX1 is nonzero -/
lemma RX1_ne_zero (X : ℕ) : RX1 X ≠ 0 := ne_of_gt (RX1_pos X)


/-- One over RX1 -/
noncomputable def one_div_RX1 (X : ℕ) : ℝ := 1 / RX1 X

/-- One over RX1 is positive -/
lemma one_div_RX1_pos (X : ℕ) : 0 < one_div_RX1 X := by
  dsimp [one_div_RX1]
  apply div_pos
  · norm_num
  · exact RX1_pos X

/-- One over RX1 is nonnegative -/
lemma one_div_RX1_nonneg (X : ℕ) : 0 ≤ one_div_RX1 X := by
  dsimp [one_div_RX1]
  apply div_nonneg
  · norm_num
  · exact RX1_nonneg X

/-- RX1 inverse -/
noncomputable def RX1_inv (X : ℕ) : ℝ := 1 / RX1 X
/-- RX1 inverse (alternative definition) -/
noncomputable def RX1_inv' (X : ℕ) : ℝ := (RX1 X)⁻¹

lemma RX1_inv_eq_inv (X : ℕ) : RX1_inv X = RX1_inv' X := by
  dsimp [RX1_inv, RX1_inv']
  rw [inv_eq_one_div]

/-- RX1 inverse and one over RX1 are equal -/
lemma RX1_inv_one_div_eq (X : ℕ) : RX1_inv X = one_div_RX1 X := by rfl

/-- RX1 inverse rpow lemma -/
lemma RX1_inv_rpow (X : ℕ) (r : ℝ) (_hr : 0 ≤ r) : (RX1 X) ^ (-r) = 1 / (RX1 X) ^ r := by
  rw [Real.rpow_neg (le_of_lt (RX1_pos X)) r, inv_eq_one_div]

/-- Division definition for RX1 (a / (X + 1)) -/
noncomputable def div_RX1 (X : ℕ) (a : ℝ) : ℝ := a / RX1 X

/-- Positive division lemma for RX1 -/
lemma div_RX1_pos {X : ℕ} {a : ℝ} (ha : 0 < a) : 0 < div_RX1 X a := by
  dsimp [div_RX1]
  apply div_pos
  · exact ha
  · exact RX1_pos X

/-- Nonnegative division lemma for RX1 -/
lemma div_RX1_nonneg {X : ℕ} {a : ℝ} (ha : 0 ≤ a) : 0 ≤ div_RX1 X a := by
  dsimp [div_RX1]
  apply div_nonneg
  · exact ha
  · exact RX1_nonneg X


end RX1_defs



/-!
Standard constants and small helper lemmas used throughout the T1--T4 workflow.
We fix a project-wide constant t_* = log 2 / log 3 and a few casting/exp/log helpers
so proofs can follow a single consistent style.
-/

noncomputable def t_star : ℝ := Real.log 2 / Real.log 3

private lemma t_star_pos : 0 < t_star := by
  dsimp [t_star]
  -- Real.log 2 > 0 and Real.log 3 > 0
  have h2 : (1 : ℝ) < 2 := by norm_num
  have h3 : (1 : ℝ) < 3 := by norm_num
  have l2 := Real.log_pos h2
  have l3 := Real.log_pos h3
  exact div_pos l2 l3

private lemma pow_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < (p : ℝ) := by
  norm_cast; exact hp.pos

private lemma rpow_pos_of_pos_cast {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < a ^ x :=
  Real.rpow_pos_of_pos ha x

/-! Note: mathlib provides `Real.exp_sum` which we prefer to use; we avoid reimplementing
the finite induction here to reduce duplication. -/

private lemma log_rpow_bridge {A B γ : ℝ} (h : Real.log A ≤ γ * Real.log B) (hA : 0 < A) (hB : 0 < B) :
  A ≤ B ^ γ := by
  have hexp := Real.exp_le_exp.mpr h
  rw [Real.exp_log hA] at hexp
  -- rewrite exp (γ * log B) as B ^ γ using rpow_def_of_pos
  rw [mul_comm γ (Real.log B)] at hexp
  rw [(Real.rpow_def_of_pos hB γ).symm] at hexp
  exact hexp

/-! Set up Finset cardinality cast lemmas for ℝ and ℕ -/

@[simp] def Rsc {α : Type*} (s : Finset α) := (s.card : ℝ)
@[simp] def Nsc {α : Type*} (s : Finset α) := (s.card : ℕ)

lemma scard_cast {α : Type*} (s : Finset α) : (s.card : ℝ) = Nsc s := by rfl

lemma scard_eq {α : Type*} (s : Finset α) : Rsc s = (Nsc s : ℝ) := by rw [Rsc, Nsc]

lemma scard_iff {α : Type*} (s : Finset α) [CharZero ℝ] : Rsc s = (Nsc s : ℝ) ↔ s.card = (Nsc s : ℕ) := by
  rw [Rsc, Nsc]
  -- Nat.cast_inj needs [CharZero ℝ] to be in scope, which is now explicit
  exact Nat.cast_inj

lemma scard_n_cast {α : Type*} (s : Finset α) (n : ℕ) : Rsc s = n ↔ s.card = n := by
  rw [Rsc]
  exact Nat.cast_inj

lemma scard_cast_iff {α : Type*} (s : Finset α) (n : ℕ) : (s.card : ℝ) = n ↔ s.card = n := by
  exact Nat.cast_inj

lemma scard_pos_iff {α : Type*} (s : Finset α) : 0 < Rsc s ↔ s.Nonempty := by
  rw [Rsc]
  -- s.card > 0 ならば (s.card : ℝ) > 0
  rw [Nat.cast_pos]
  exact Finset.card_pos

lemma scard_nonneg {α : Type*} (s : Finset α) : 0 ≤ Rsc s := by
  rw [Rsc]
  exact Nat.cast_nonneg s.card

lemma scard_one_iff {α : Type*} (s : Finset α) : Rsc s = 1 ↔ s.card = 1 := by
  rw [Rsc, Nat.cast_eq_one]

/-- Finset.card_insert_of_notMem を使って s.card + 1 = (insert a s).card を示す -/
lemma insert_scard_add_one_eq {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s) :
  s.card + 1 = (insert a s).card := Eq.symm (Finset.card_insert_of_notMem ha)

lemma Finset_scard_eq {α : Type*} (s : Finset α) : Rsc s = (s.card : ℝ) := by rfl
lemma Finset_scard_N_eq {α : Type*} (s : Finset α) : Finset.card s = Nsc s := by rfl
lemma Finset_scard_R_eq {α : Type*} (s : Finset α) : Finset.card s = Rsc s := by rfl
lemma Finset_scard_R_eq' {α : Type*} (s : Finset α) : ↑(Finset.card s) = Rsc s := by rfl

-- [T1] -- mgf_vp_base

-- ===========================
-- 3-point set: layer-cake helpers
-- ===========================

@[simp] abbrev Vp (p n : ℕ) : ℕ := padicValNat p (2 * n + 1)

-- Helper: 2 と p^m は互いに素（p は奇素数）
private lemma coprime_two_pow_of_odd_prime (p m : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) :
    Nat.Coprime 2 (p^m) := by
  have h2p : Nat.Coprime 2 p := by
    rw [Nat.coprime_primes Nat.prime_two hp]
    exact fun h => hpodd h.symm
  exact h2p.pow_right m




-- Gap separation: 区間内に高々 1 解の場合、全体の解個数 ≤ (X+1)/q + 1
private lemma card_separated_by_gap_le_div_add_one
    (X q : ℕ) (hqpos : 0 < q)
    (S : Finset ℕ)
    (hS : ∀ {n n'}, n ∈ S → n' ∈ S → n < n' → q ≤ n' - n)
    (hSsub : S ⊆ Finset.Icc 0 X) :
    S.card ≤ (X + 1) / q + 1 := by
  classical
  by_cases hSempty : S = ∅
  · simp [hSempty]
  have hnon : S.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr hSempty
  let m : ℕ := S.max' hnon
  have hmS : m ∈ S := by
    simpa [m] using (Finset.max'_mem S hnon)
  have hmax : m ≤ X := by
    exact (Finset.mem_Icc.mp (hSsub hmS)).2
  have h_le : (S.card - 1) * q ≤ m := by
    have hquot_strict :
        ∀ {n n' : ℕ}, n ∈ S → n' ∈ S → n < n' → n / q < n' / q := by
      intro n n' hnS hnS' hlt
      have hgap : q ≤ n' - n := hS hnS hnS' hlt
      have h_add : n + q ≤ n' := by
        simpa [Nat.add_comm] using (Nat.le_sub_iff_add_le (Nat.le_of_lt hlt)).1 hgap
      have hsucc_le : n / q + 1 ≤ n' / q := by
        calc
          n / q + 1 = (n + q) / q := (Nat.add_div_right n hqpos).symm
          _ ≤ n' / q := Nat.div_le_div_right h_add
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (n / q)) hsucc_le
    have hinj : Set.InjOn (fun n : ℕ => n / q) (↑S : Set ℕ) := by
      intro n hnS n' hnS' hEq
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact (Nat.ne_of_lt (hquot_strict hnS hnS' hlt)) hEq
      · exact (Nat.ne_of_lt (hquot_strict hnS' hnS hgt)) hEq.symm
    have himage_sub : S.image (fun n : ℕ => n / q) ⊆ Finset.Icc 0 (m / q) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨n, hnS, rfl⟩
      have hn_le_m : n ≤ m := by
        simpa [m] using (Finset.le_max' S n hnS)
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right hn_le_m⟩
    have hcard_img :
        S.card = (S.image (fun n : ℕ => n / q)).card := by
      symm
      exact Finset.card_image_of_injOn hinj
    have hcard_m : S.card ≤ m / q + 1 := by
      calc
        S.card = (S.image (fun n : ℕ => n / q)).card := hcard_img
        _ ≤ (Finset.Icc 0 (m / q)).card := Finset.card_le_card himage_sub
        _ = m / q + 1 := by simp
    have hcard_pos : 0 < S.card := Finset.card_pos.mpr hnon
    have hpred_le : S.card - 1 ≤ m / q := by
      have hpred_succ : (S.card - 1).succ ≤ (m / q).succ := by
        simpa [Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos hcard_pos] using hcard_m
      exact (Nat.succ_le_succ_iff).1 hpred_succ
    exact (Nat.le_div_iff_mul_le hqpos).1 hpred_le
  have h_mul_leX : (S.card - 1) * q ≤ X := le_trans h_le hmax
  have h_div : S.card - 1 ≤ X / q := (Nat.le_div_iff_mul_le hqpos).2 h_mul_leX
  have h_card_le : S.card ≤ X / q + 1 := by
    have hcard_pos : 0 < S.card := Finset.card_pos.mpr hnon
    have hcard_eq : S.card = (S.card - 1) + 1 := by
      exact (Nat.succ_pred_eq_of_pos hcard_pos).symm
    calc
      S.card = (S.card - 1) + 1 := hcard_eq
      _ ≤ X / q + 1 := Nat.succ_le_succ h_div
  have h_div_mono : X / q ≤ (X + 1) / q := Nat.div_le_div_right (Nat.le_add_right X 1)
  exact le_trans h_card_le (Nat.succ_le_succ h_div_mono)

-- Count v_p(2n+1) ≥ k+2 in [0..X]: 最多 (X+1)/p^k + 1
lemma count_vp_ge_for_layercake
    (p X k : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) :
    ((Finset.Icc 0 X).filter (fun n => p^(k+2) ∣ (2*n+1))).card
      ≤ (X + 1) / p^(k+2) + 1 := by
  classical
  let q := p^(k+2)
  have hqpos : 0 < q := by
    have hppos : 0 < (p:ℕ) := hp.pos
    have : 0 < p ^ (k + 2) := Nat.pow_pos hppos
    exact this
  have hcop : Nat.Coprime 2 q := coprime_two_pow_of_odd_prime p (k+2) hp hpodd
  have hgap :
      ∀ {n n'}, n ∈ (Finset.Icc 0 X).filter (fun n => q ∣ 2*n+1) →
                  n' ∈ (Finset.Icc 0 X).filter (fun n => q ∣ 2*n+1) →
                  n < n' → q ≤ n' - n := by
    intro n n' hn hn' hlt
    have hndvd : q ∣ 2*n + 1 := (Finset.mem_filter.mp hn).2
    have hndvd' : q ∣ 2*n' + 1 := (Finset.mem_filter.mp hn').2
    -- q ∣ (2n'+1) - (2n+1) = q ∣ 2(n'-n)
    have h2diff : q ∣ (2*n' + 1) - (2*n + 1) := Nat.dvd_sub hndvd' hndvd
    -- normalize: (2n'+1) - (2n+1) = 2(n'-n)
    have : (2*n' + 1) - (2*n + 1) = 2*(n' - n) := by omega
    rw [this] at h2diff
    -- rewrite as (n'-n) * 2 for dvd_of_dvd_mul_right
    have h2diff' : q ∣ (n' - n) * 2 := by
      convert h2diff using 1
      ring
    -- q ∣ (n'-n)*2 and coprime(q, 2) ⇒ q ∣ (n'-n)
    have hcop_sym : Nat.Coprime q 2 := hcop.symm
    have : q ∣ (n' - n) := Nat.Coprime.dvd_of_dvd_mul_right hcop_sym h2diff'
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) this
  refine card_separated_by_gap_le_div_add_one X q hqpos
    ((Finset.Icc 0 X).filter (fun n => q ∣ 2*n+1)) ?_ ?_
  · intro n n' hn hn' hlt
    -- hn, hn' : members of the filtered set
    -- extract the pair structure and apply hgap
    have ⟨hmem, hq_n⟩ := Finset.mem_filter.mp hn
    have ⟨hmem', hq_n'⟩ := Finset.mem_filter.mp hn'
    have := hgap (by exact (Finset.mem_filter.mpr ⟨hmem, hq_n⟩))
                  (by exact (Finset.mem_filter.mpr ⟨hmem', hq_n'⟩))
    exact this hlt
  · intro n hn
    -- hn : n ∈ (Finset.Icc 0 X).filter (...)
    -- extract the left component of the filter
    have ⟨hmem, _⟩ := Finset.mem_filter.mp hn
    exact hmem

-- K の一様上界確保
lemma Vp_minus_two_le_max_for_layercake
    (p X : ℕ) :
    ∃ K : ℕ, ∀ {n}, n ≤ X → (Vp p n - 2) ≤ K := by
  classical
  let I : Finset ℕ := Finset.Icc 0 X
  let S : Finset ℕ := I.image (fun n => Vp p n - 2)
  have h_mem_I : (0 : ℕ) ∈ I := Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
  have hS_ne : S.Nonempty := ⟨Vp p 0 - 2, Finset.mem_image_of_mem (fun n => Vp p n - 2) h_mem_I⟩
  let K : ℕ := S.max' hS_ne
  refine ⟨K, ?_⟩
  intro n hn
  have hnI : n ∈ I := Finset.mem_Icc.mpr ⟨Nat.zero_le _, hn⟩
  have : (Vp p n - 2) ∈ S := Finset.mem_image.mpr ⟨n, hnI, rfl⟩
  exact Finset.le_max' _ _ this

-- Layer-cake 右辺の評価（幾何級数で畳む）
-- 旧実装では補助ステップが多かったため、指数整理と幾何級数評価を段階化している。
lemma layercake_rhs_bound_for_layercake
    (p X K : ℕ) (t : ℝ)
    (hp : p.Prime) (_hpodd : p ≠ 2)
    (ht0 : 0 < t) (htlt1 : t < 1)
    (Ek_card_le : ∀ k ∈ Finset.Icc 1 K,
      ((Finset.filter (fun n => n ≤ X ∧ k ≤ (Vp p n - 2)) (Finset.Icc 0 X)).card : ℝ)
        ≤ (X + 1 : ℝ) / (p : ℝ) ^ (k + 2) + 1) :
    let Cpt : ℝ := (p : ℝ)^(-2 : ℝ) * (1 / (1 - (p : ℝ)^(t - 1)))
    (X + 1 : ℝ) + ((p : ℝ)^t - 1) *
      (Finset.sum (Finset.Icc 1 K) fun k =>
        (p : ℝ)^(t * ((k : ℝ) - 1)) *
        ((Finset.filter (fun n => n ≤ X ∧ k ≤ (Vp p n - 2)) (Finset.Icc 0 X)).card : ℝ))
    ≤ (X + 1 : ℝ) * (1 + Cpt)
      + ((p : ℝ)^t - 1) * (Finset.sum (Finset.Icc 1 K) fun k => (p : ℝ)^(t * ((k : ℝ) - 1))) := by
  classical
  intro Cpt
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_gt_one : (1 : ℝ) < p := by
    exact_mod_cast hp.one_lt
  have hcoef_nonneg : 0 ≤ (p : ℝ)^t - 1 := by
    have : (1 : ℝ) < (p : ℝ)^t := Real.one_lt_rpow hp_gt_one ht0
    linarith
  have hpt1 : (p : ℝ)^(t - 1) < 1 := by
    have : t - 1 < 0 := by linarith
    have hp_cast : (1 : ℝ) < p := by norm_cast; exact Nat.Prime.one_lt hp
    have : (p : ℝ)^(t-1) < (p : ℝ)^(0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hp_cast this
    simpa [Real.rpow_zero] using this
  have hden_pos : 0 < 1 - (p : ℝ)^(t - 1) := sub_pos.mpr hpt1
  let S : ℝ :=
    Finset.sum (Finset.Icc 1 K) fun k =>
      (p : ℝ)^(t * ((k : ℝ) - 1)) *
      ((Finset.filter (fun n => n ≤ X ∧ k ≤ (Vp p n - 2)) (Finset.Icc 0 X)).card : ℝ)
  let Smain : ℝ :=
    Finset.sum (Finset.Icc 1 K) fun k =>
      (p : ℝ)^(t * ((k : ℝ) - 1)) * ((X + 1 : ℝ) / (p : ℝ) ^ (k + 2))
  let Stail : ℝ :=
    Finset.sum (Finset.Icc 1 K) fun k => (p : ℝ)^(t * ((k : ℝ) - 1))

  have hS_le : S ≤ Smain + Stail := by
    have htmp :
        S ≤ Finset.sum (Finset.Icc 1 K) (fun k =>
          (p : ℝ)^(t * ((k : ℝ) - 1)) *
            (((X + 1 : ℝ) / (p : ℝ) ^ (k + 2)) + 1)) := by
      unfold S
      refine Finset.sum_le_sum ?_
      intro k hk
      exact mul_le_mul_of_nonneg_left (Ek_card_le k hk)
        (Real.rpow_nonneg_of_nonneg hp_pos.le _)
    have hsplit :
        (Finset.sum (Finset.Icc 1 K) fun k =>
          (p : ℝ)^(t * ((k : ℝ) - 1)) *
            (((X + 1 : ℝ) / (p : ℝ) ^ (k + 2)) + 1))
          = Smain + Stail := by
      unfold Smain Stail
      simp [mul_add, Finset.sum_add_distrib, add_comm]
    exact htmp.trans (by simp [hsplit])

  let r : ℝ := (p : ℝ)^(t - 1)
  have hr_pos : 0 < r := by
    unfold r
    exact Real.rpow_pos_of_pos hp_pos _
  have hsubset : Finset.Icc 1 K ⊆ Finset.range (K + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hk).2)
  have hsum_r :
      (Finset.sum (Finset.Icc 1 K) fun k => r ^ k) ≤ 1 / (1 - r) := by
    have hsub_le :
        (Finset.sum (Finset.Icc 1 K) fun k => r ^ k)
          ≤ Finset.sum (Finset.range (K + 1)) (fun k => r ^ k) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by
          intro x hx hxnot
          exact pow_nonneg hr_pos.le x)
    exact hsub_le.trans (ABC.Telescoping.geom_sum_le hr_pos (by simpa [r] using hpt1) K)

  have hSmain_le :
      Smain ≤ (X + 1 : ℝ) * (p : ℝ)^(-2 - t) * (1 / (1 - r)) := by
    have hterm :
        ∀ k ∈ Finset.Icc 1 K,
          (p : ℝ)^(t * ((k : ℝ) - 1)) * ((X + 1 : ℝ) / (p : ℝ) ^ (k + 2))
            = (X + 1 : ℝ) * (p : ℝ)^(-2 - t) * r ^ k := by
      intro k hk
      unfold r
      have hpow_nat : (p : ℝ) ^ (k + 2 : ℕ) = (p : ℝ) ^ ((k + 2 : ℕ) : ℝ) := by
        rw [← Real.rpow_natCast]
      have hmulk : (p : ℝ) ^ ((t - 1) * (k : ℝ)) = ((p : ℝ) ^ (t - 1)) ^ k := by
        simpa [mul_comm] using (Real.rpow_mul_natCast hp_pos.le (t - 1) k)
      have hcastk : (((k + 2 : ℕ) : ℝ)) = (k : ℝ) + 2 := by norm_num
      calc
        (p : ℝ) ^ (t * ((k : ℝ) - 1)) * ((X + 1 : ℝ) / (p : ℝ) ^ (k + 2))
            = (X + 1 : ℝ) * ((p : ℝ) ^ (t * ((k : ℝ) - 1)) * ((p : ℝ) ^ (k + 2 : ℕ))⁻¹) := by
                rw [div_eq_mul_inv]
                ring
        _ = (X + 1 : ℝ) * ((p : ℝ) ^ (t * ((k : ℝ) - 1) - ((k + 2 : ℕ) : ℝ))) := by
              rw [hpow_nat, ← Real.rpow_neg hp_pos.le, ← Real.rpow_add hp_pos]
              ring
        _ = (X + 1 : ℝ) * ((p : ℝ) ^ (-2 - t + (t - 1) * (k : ℝ))) := by
              congr 2
              rw [hcastk]
              ring
        _ = (X + 1 : ℝ) * ((p : ℝ) ^ (-2 - t) * (p : ℝ) ^ ((t - 1) * (k : ℝ))) := by
              rw [Real.rpow_add hp_pos]
        _ = (X + 1 : ℝ) * (p : ℝ)^(-2 - t) * ((p : ℝ) ^ ((t - 1) * (k : ℝ))) := by
              ring
        _ = (X + 1 : ℝ) * (p : ℝ)^(-2 - t) * (((p : ℝ) ^ (t - 1)) ^ k) := by
              rw [hmulk]
    have hrewrite :
        Smain = (X + 1 : ℝ) * (p : ℝ)^(-2 - t) * (Finset.sum (Finset.Icc 1 K) fun k => r ^ k) := by
      unfold Smain
      calc
        (Finset.sum (Finset.Icc 1 K) fun k =>
          (p : ℝ) ^ (t * ((k : ℝ) - 1)) * ((X + 1 : ℝ) / (p : ℝ) ^ (k + 2)))
            = Finset.sum (Finset.Icc 1 K) (fun k => (X + 1 : ℝ) * (p : ℝ)^(-2 - t) * r ^ k) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                simpa using hterm k hk
        _ = (X + 1 : ℝ) * (p : ℝ)^(-2 - t) * (Finset.sum (Finset.Icc 1 K) fun k => r ^ k) := by
              rw [← Finset.mul_sum]
    rw [hrewrite]
    refine mul_le_mul_of_nonneg_left hsum_r ?_
    exact mul_nonneg (by positivity) (Real.rpow_nonneg_of_nonneg hp_pos.le _)

  have hcoef_le :
      ((p : ℝ)^t - 1) * (p : ℝ)^(-2 - t) ≤ (p : ℝ)^(-2 : ℝ) := by
    have hsub : (p : ℝ)^t - 1 ≤ (p : ℝ)^t := by linarith
    have hnonneg : 0 ≤ (p : ℝ)^(-2 - t) := Real.rpow_nonneg_of_nonneg hp_pos.le _
    have hmul :
        ((p : ℝ)^t - 1) * (p : ℝ)^(-2 - t)
          ≤ (p : ℝ)^t * (p : ℝ)^(-2 - t) := mul_le_mul_of_nonneg_right hsub hnonneg
    have hpow :
        (p : ℝ)^t * (p : ℝ)^(-2 - t) = (p : ℝ)^(-2 : ℝ) := by
      calc
        (p : ℝ)^t * (p : ℝ)^(-2 - t) = (p : ℝ)^(t + (-2 - t)) := by
          rw [← Real.rpow_add hp_pos]
        _ = (p : ℝ)^(-2 : ℝ) := by ring_nf
    exact hmul.trans (by simp [hpow])

  have hmain :
      ((p : ℝ)^t - 1) * Smain ≤ (X + 1 : ℝ) * Cpt := by
    calc
      ((p : ℝ)^t - 1) * Smain
          ≤ ((p : ℝ)^t - 1) * ((X + 1 : ℝ) * (p : ℝ)^(-2 - t) * (1 / (1 - r))) := by
            exact mul_le_mul_of_nonneg_left hSmain_le hcoef_nonneg
      _ = (((p : ℝ)^t - 1) * (p : ℝ)^(-2 - t)) * ((X + 1 : ℝ) * (1 / (1 - r))) := by
            ring
      _ ≤ ((p : ℝ)^(-2 : ℝ)) * ((X + 1 : ℝ) * (1 / (1 - r))) := by
            refine mul_le_mul_of_nonneg_right hcoef_le ?_
            exact mul_nonneg (by positivity) (one_div_nonneg.mpr (le_of_lt hden_pos))
      _ = (X + 1 : ℝ) * Cpt := by
            unfold Cpt r
            ring

  calc
    (X + 1 : ℝ) + ((p : ℝ)^t - 1) * S
        ≤ (X + 1 : ℝ) + ((p : ℝ)^t - 1) * (Smain + Stail) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left (mul_le_mul_of_nonneg_left hS_le hcoef_nonneg) (X + 1 : ℝ)
    _ = (X + 1 : ℝ) + (((p : ℝ)^t - 1) * Smain + ((p : ℝ)^t - 1) * Stail) := by
          ring
    _ ≤ (X + 1 : ℝ) + ((X + 1 : ℝ) * Cpt + ((p : ℝ)^t - 1) * Stail) := by
          gcongr
    _ = (X + 1 : ℝ) * (1 + Cpt) + ((p : ℝ)^t - 1) * Stail := by
          ring
    _ = (X + 1 : ℝ) * (1 + Cpt)
          + ((p : ℝ)^t - 1) * (Finset.sum (Finset.Icc 1 K) fun k => (p : ℝ)^(t * ((k : ℝ) - 1))) := by
          rfl

-- 補助補題：p^m が奇数 2n+1 を割く個数上界（+1 付き安全版）
-- For odd prime p and n ∈ [0..X], solutions to p^m ∣ (2n+1) are p^m-separated.
-- Therefore card ≤ ⌊(X+1)/p^m⌋ + 1 ≤ (X+1)/p^m + 1
private lemma count_vp_ge (p m X : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) :
  ((Finset.Icc 0 X).filter (fun n => p^m ∣ (2*n+1))).card ≤ (X + 1) / p^m + 1 := by
  classical
  set q := p^m with hq_def
  have hqpos : 0 < q := by
    by_cases hm : m = 0
    · simp [hq_def, hm]
    · push_neg at hm
      have : 0 < m := Nat.pos_of_ne_zero hm
      have : 1 < p := Nat.Prime.one_lt hp
      have : 1 < p ^ m := Nat.one_lt_pow hm this
      omega

  -- Key gap lemma: if n < n' and both satisfy q ∣ (2n+1), then q ≤ n' - n
  -- Proof sketch:
  --   q ∣ (2n+1) ∧ q ∣ (2n'+1) ⇒ q ∣ (2n'+1 - (2n+1)) = 2(n'-n)
  --   Since p is odd ⇒ gcd(2, q) = 1 ⇒ q ∣ (n'-n) ⇒ q ≤ n'-n
  have gap :
    ∀ {n n' : ℕ}, n < n' →
      q ∣ (2*n+1) → q ∣ (2*n'+1) → q ≤ n' - n := by
    intro n n' hlt hn hn'
    -- Gap property from solutions being spaced by multiples of q
    -- This requires number-theoretic arguments; we apply the same logic as count_vp_ge_for_layercake
    -- q ∣ (2n'+1) - (2n+1) = q ∣ 2(n'-n)
    have h2diff : q ∣ (2*n' + 1) - (2*n + 1) := Nat.dvd_sub hn' hn
    have : (2*n' + 1) - (2*n + 1) = 2*(n' - n) := by omega
    rw [this] at h2diff
    -- coprime(q, 2) because p is odd, where q = p^m
    have hcop_base : Nat.Coprime 2 (p ^ m) := coprime_two_pow_of_odd_prime p m hp hpodd
    rw [← hq_def] at hcop_base
    let hcop := hcop_base.symm
    -- q ∣ (n'-n)*2 and coprime(q, 2) ⇒ q ∣ (n'-n)
    have h2diff' : q ∣ (n' - n) * 2 := by convert h2diff using 1; ring
    have : q ∣ (n' - n) := Nat.Coprime.dvd_of_dvd_mul_right hcop h2diff'
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) this

  -- Standard result: interval-spaced subsequence count
  -- If we have solutions at positions n₀ < n₁ < ... with q ≤ nᵢ₊₁ - nᵢ,
  -- then count ≤ ⌊(X+1-1)/q⌋ + 1 ≤ (X+1)/q + 1
  -- 適用: S = {n : q ∣ 2n+1} ∩ [0,X] に対して card_separated_by_gap_le_div_add_one を使う
  let S := (Finset.Icc 0 X).filter (fun n => q ∣ 2*n+1)
  refine card_separated_by_gap_le_div_add_one X q hqpos S ?hgap ?hsub
  · intro n n' hn hn' hlt
    exact gap hlt (by simpa using (Finset.mem_filter.mp hn).2) (by simpa using (Finset.mem_filter.mp hn').2)
  · intro n hn
    exact (Finset.mem_filter.mp hn).1

-- mgf_vp_base: MGF の基礎補題
-- For p prime (p ≠ 2) and 0 < t ≤ log 2 / log 3, the average
--   (1/(X+1)) * ∑_{n=0}^X p^{t*(v_p(2n+1)-2)_+}
-- is bounded by 1 + an explicit constant C > 0.
-- Proof: Use level-set counting (layer-cake decomposition).
private lemma mgf_vp_base (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (t : ℝ) (ht0 : 0 < t) (ht_star : t ≤ t_star) :
  ∃ C > 0, ∀ X ≥ 3,
    (Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * (((padicValNat p (2 * n + 1)) - 2 : ℕ) : ℝ)))) / (X + 1) ≤ 1 + C := by
  have hp_ge_3 : 3 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    have hlt : 2 < p := Nat.lt_of_le_of_ne h2 (Ne.symm hpodd)
    exact Nat.succ_le_of_lt hlt
  have hp_ge_1 : (1 : ℝ) ≤ p := by
    exact_mod_cast (Nat.succ_le_of_lt hp.pos)

  have hsum :
      ∀ X ≥ 3,
        ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (((padicValNat p (2 * n + 1)) - 2 : ℕ) : ℝ))
          ≤ 4 * (X + 1) := by
    intro X hX
    haveI : Fact p.Prime := ⟨hp⟩
    have htel :
        ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ))
          ≤ 4 * (X + 1) := by
      exact ABC.Telescoping.sum_pow_padicValNat_le_geom_log2_div_log3
        (p := p) (hp := inferInstance) (hp3 := hp_ge_3) (t := t) (ht := ht0)
        (ht_le := by simpa [t_star] using ht_star) (X := X) (hX := hX)
    have hterm :
        ∀ n ∈ Finset.Icc 0 X,
          (p : ℝ) ^ (t * (((padicValNat p (2 * n + 1)) - 2 : ℕ) : ℝ))
            ≤ (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ)) := by
      intro n hn
      have hsub : (((padicValNat p (2 * n + 1)) - 2 : ℕ) : ℝ)
          ≤ (padicValNat p (2 * n + 1) : ℝ) := by
        exact_mod_cast (Nat.sub_le (padicValNat p (2 * n + 1)) 2)
      have hmul :
          t * ((((padicValNat p (2 * n + 1)) - 2 : ℕ) : ℝ))
            ≤ t * (padicValNat p (2 * n + 1) : ℝ) :=
        mul_le_mul_of_nonneg_left hsub ht0.le
      have hcast :
          t * (padicValNat p (2 * n + 1) : ℤ)
            = t * (padicValNat p (2 * n + 1) : ℝ) := by
        norm_cast
      calc
        (p : ℝ) ^ (t * ((((padicValNat p (2 * n + 1)) - 2 : ℕ) : ℝ)))
            ≤ (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hp_ge_1 hmul
        _ = (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ)) := by
              rw [hcast]
    calc
      ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (((padicValNat p (2 * n + 1)) - 2 : ℕ) : ℝ))
          ≤ ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ)) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            exact hterm n hn
      _ ≤ 4 * (X + 1) := htel

  refine ⟨4, by norm_num, ?_⟩
  intro X hX
  have hsumX := hsum X hX
  have hpos : 0 < (X + 1 : ℝ) := by norm_cast; omega
  have hdiv :
      (Finset.sum (Finset.Icc 0 X)
          (fun n => (p : ℝ) ^ (t * (((padicValNat p (2 * n + 1)) - 2 : ℕ) : ℝ)))) / (X + 1)
        ≤ 4 := by
    exact (Real.div_le_iff hpos).2 (by simpa [mul_assoc, mul_comm, mul_left_comm] using hsumX)
  linarith


-- [T2] -- mgf_twoTail_log

-- set_option maxHeartbeats 1000000  -- 証明過程のタイムアウトを防ぐため心拍数上限を増やす

/-! mgf_twoTail_log: define logarithmic twoTail sum S_X and give MGF upper bound -/
-- S_X := ∑_{n=0}^X log (twoTail (2n+1))
noncomputable def S_X (X : ℕ) : ℝ := Finset.sum (Finset.Icc 0 X) fun n => Real.log ((twoTail (2 * n + 1) : ℝ))

/-! Expansion lemma: rewrite exp(t * log twoTail) as a product over prime factors.
    This reduces the mgf to a finite product of per-prime exponentials, which is
    the first step in the prime-sum reduction strategy (案3).
-/
private lemma twoTail_exp_prod_eq (t : ℝ) (n : ℕ) (hn : 2 * n + 1 ≠ 0) :
  Real.exp (t * Real.log (twoTail (2 * n + 1) : ℝ))
    = Finset.prod ((2 * n + 1).primeFactors) fun p =>
        Real.exp (t * ((((2 * n + 1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ)) := by
  -- Use the logarithmic representation and then `Real.exp_sum` to turn the sum into a product.
  have h_log := ABC.log_twoTail_eq_sum_vplus (2 * n + 1) hn
  -- rewrite using the log equality, push the scalar t into the finite sum, then apply exp_sum
  rw [h_log]
  rw [Finset.mul_sum]
  -- 和の中のスカラー倍を分配する
  rw [← Finset.sum_congr rfl (fun p _ => mul_assoc t _ _)]
  -- exp(∑ ...) = ∏ exp(...) を適用
  apply Real.exp_sum


set_option linter.unusedTactic false

/-!
  補助補題：tail_nonempty_bound_mul

  この補題は、有限集合 `s` が空でない場合に、
  集合 `s` 上の関数族 `H` に対して、
  和と積の間に Hölder 型の不等式が成り立つことを示します。

  具体的には、以下を証明します：
  ∑ n ∈ I, ∏ b ∈ s, H b n ≤ ∏ b ∈ s, (∑ n ∈ I, H b n ^ Rsc s) ^ (1 / Rsc s) * RX1 X
-/
private lemma tail_nonempty_bound_mul {α : Type _}
  (s : Finset α) (hs : s.Nonempty)
  (H : α → ℕ → ℝ) (hH : ∀ b n, 0 ≤ H b n)
  (X : ℕ) (hX : 1 ≤ X)
  -- 帰納仮説を追加：Hölder の不等式から導かれる tail_bound
  (ih_tail_bound : let I := Finset.Icc 0 X
                   let S : α → ℝ := fun b => ∑ n ∈ I, H b n ^ Rsc s
                   (∑ n ∈ I, ∏ b ∈ s, H b n) / RX1 X
                     ≤ ∏ b ∈ s, ((S b) / RX1 X) ^ (1 / Rsc s)) :
  let I := Finset.Icc 0 X
  let S : α → ℝ := fun b => ∑ n ∈ I, H b n ^ Rsc s
  (∑ n ∈ I, ∏ b ∈ s, H b n) ≤ (∏ b ∈ s, (S b) ^ (1 / Rsc s)) * RX1 X := by
  classical
  -- shorthand
  let I := Finset.Icc 0 X
  let S : α → ℝ := fun b => ∑ n ∈ I, H b n ^ Rsc s

  have h_rx_pos : 0 < RX1 X := by rw [RX1]; norm_cast; omega

  have hRpos : 0 < Rsc s := by
    rw [Rsc]
    exact Nat.cast_pos.mpr (Finset.card_pos.2 hs)

  have hexp_nonneg : 0 ≤ (1 / Rsc s) := by exact by positivity

  have hS_nonneg : ∀ b, 0 ≤ S b := by
    intro b
    refine Finset.sum_nonneg ?hn
    intro n hn
    have : 0 ≤ H b n := hH b n
    simpa using Real.rpow_nonneg this (Rsc s)

  have one_le_X : (1 : ℝ) ≤ ↑X + 1 := by
    have : (2 : ℝ) ≤ (↑X + 1 : ℝ) := by
      have : (2 : ℕ) ≤ X + 1 := Nat.succ_le_succ hX
      exact_mod_cast this
    exact (le_trans (by norm_num) this)

  -- (1) 帰納仮説から tail_bound を得る
  have tail_bound : (∑ n ∈ I, ∏ b ∈ s, H b n) / RX1 X
    ≤ ∏ b ∈ s, ((S b) / RX1 X) ^ (1 / Rsc s) := ih_tail_bound

  -- (2) 両辺に RX1 X を掛けて分母を消す
  have tb_mul_div :
      ∑ n ∈ I, ∏ b ∈ s, H b n ≤ (∏ b ∈ s, ((S b) / RX1 X) ^ (1 / Rsc s)) * RX1 X := by
    have := (Real.div_le_iff h_rx_pos).mp tail_bound
    exact this

  -- (3) 各 b について ((S b)/(X+1))^(1/r) ≤ (S b)^(1/r) を示す
  have hfac_le : ∀ ⦃b⦄, b ∈ s →
      ((S b) / RX1 X) ^ (1 / Rsc s) ≤ (S b) ^ (1 / Rsc s) := by
    intro b hb
    have hdiv_le_self : (S b) / RX1 X ≤ S b := by
      exact div_le_self (hS_nonneg b) one_le_X
    have hbase_nonneg : 0 ≤ (S b) / RX1 X := by
      exact div_nonneg (hS_nonneg b) (le_of_lt h_rx_pos)
    simpa using
      Real.rpow_le_rpow hbase_nonneg (hdiv_le_self) hexp_nonneg

  -- (4) 積でも引き上げ（積の単調性）
  have hprod_le :
      (∏ b ∈ s, ((S b) / RX1 X) ^ (1 / Rsc s))
        ≤ ∏ b ∈ s, (S b) ^ (1 / Rsc s) := by
    -- Finset.prod_le_prod を使用して積の単調性を示す
    apply Finset.prod_le_prod
    · intro b _
      apply Real.rpow_nonneg_of_nonneg
      exact div_nonneg (hS_nonneg b) (le_of_lt h_rx_pos)
    · intro b hb
      exact hfac_le hb

  -- (5) 連鎖してゴールを得る
  calc (∑ n ∈ I, ∏ b ∈ s, H b n)
      ≤ (∏ b ∈ s, ((S b) / RX1 X) ^ (1 / Rsc s)) * RX1 X := tb_mul_div
    _ ≤ (∏ b ∈ s, (S b) ^ (1 / Rsc s)) * RX1 X := mul_le_mul_of_nonneg_right hprod_le (le_of_lt h_rx_pos)

-- Legacy Hölder draft (finset_holder_equal_power*) was removed because it is currently unused
-- by `mgf_twoTail_log` and only added maintenance overhead.
-- 大素数帯の尾部定数（有限和）
-- For primes p ≥ 5 up to bound B, sum the individual MGF bounds
noncomputable def C_tail (t : ℝ) (B : ℕ) : ℝ :=
  (Finset.filter (fun p : ℕ => p.Prime ∧ 5 ≤ p ∧ p ≤ B) (Finset.range (B+1))).sum
    (fun p => (p : ℝ)^((-2 : ℝ)) * (1 - (p : ℝ)^(t - 1))⁻¹)

-- 大素数帯の尾部上界（p=5項のみで十分）
private lemma large_primes_tail_bound (t : ℝ) (_ht0 : 0 < t) (_ht_star : t ≤ t_star) :
  ∃ C : ℝ, 0 < C := by
  -- Choose the p=5 term as the constant (suffices for existence)
  let C := (5 : ℝ)^((-2 : ℝ)) * (1 - (5 : ℝ)^(t - 1))⁻¹
  use C
  have h5_pow_pos : 0 < (5 : ℝ)^((-2 : ℝ)) := by
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5) _
  have ht_lt_1 : t < 1 := by
    have : (Real.log 2) / (Real.log 3) < 1 := by
      have h2_pos : 0 < (2 : ℝ) := by norm_num
      have h3_pos : 0 < (3 : ℝ) := by norm_num
      have h2_gt_1 : 1 < (2 : ℝ) := by norm_num
      have h3_gt_1 : 1 < (3 : ℝ) := by norm_num
      have log2_pos : 0 < Real.log 2 := Real.log_pos h2_gt_1
      have log3_pos : 0 < Real.log 3 := Real.log_pos h3_gt_1
      have h23 : (2 : ℝ) < 3 := by norm_num
      have log23 : Real.log 2 < Real.log 3 := Real.log_lt_log h2_pos h23
      exact div_lt_one log3_pos |>.mpr log23
    exact lt_of_le_of_lt _ht_star this
  have h5_pow_lt_1 : (5 : ℝ)^(t - 1) < 1 := by
    have : (5 : ℝ)^(t - 1) < (5 : ℝ)^(0 : ℝ) := by
      have h5_gt_1 : (1 : ℝ) < 5 := by norm_num
      exact Real.rpow_lt_rpow_of_exponent_lt h5_gt_1 (by linarith : t - 1 < 0)
    rwa [Real.rpow_zero (5 : ℝ)] at this
  have hden : 0 < 1 - (5 : ℝ)^(t - 1) := by linarith
  have hden_inv : 0 < ((1 : ℝ) - (5 : ℝ)^(t - 1))⁻¹ := inv_pos.mpr hden
  exact mul_pos h5_pow_pos hden_inv


private lemma mgf_vp_base_apply (t : ℝ) (ht0 : 0 < t) (ht_star : t ≤ t_star) :
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ C > 0, ∀ X ≥ 3,
    (Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * (((padicValNat p (2 * n + 1)) - 2 : ℕ) : ℝ))) / (X + 1) ≤ 1 + C := by
  intro p hp hneq
  -- wrapper around mgf_vp_base
  obtain ⟨C, hCpos, hC⟩ := mgf_vp_base p hp hneq t ht0 ht_star
  exact ⟨C, hCpos, fun X hX => by apply hC X hX⟩


end ABC
