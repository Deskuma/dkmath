/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC

#print "file: DkMath.ABC.ABCMGFTwoTailLog"

set_option linter.style.emptyLine false
set_option linter.style.longLine false

/-!
Auxiliary lemmas used in the mgf_twoTail_log argument.
These are small, reusable statements around:
 - separated-set counting on intervals,
 - layer-cake counting for `padicValNat p (2*n+1)`,
 - geometric-series style bounds used in the MGF argument.
 -/


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


/-! Note: mathlib provides `Real.exp_sum` which we prefer to use; we avoid reimplementing
the finite induction here to reduce duplication. -/

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

-- [T1] layer-cake counting helpers

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
lemma card_separated_by_gap_le_div_add_one
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

-- 一般版: p^m ∣ (2n+1) を満たす n ∈ [0..X] の個数上界（+1 付き安全版）
lemma count_vp_ge (p m X : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) :
    ((Finset.Icc 0 X).filter (fun n => p^m ∣ (2*n+1))).card
      ≤ (X + 1) / p^m + 1 := by
  classical
  let q := p^m
  have hqpos : 0 < q := by
    have hppos : 0 < (p:ℕ) := hp.pos
    have : 0 < p ^ m := Nat.pow_pos hppos
    exact this
  have hcop : Nat.Coprime 2 q := coprime_two_pow_of_odd_prime p m hp hpodd
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

-- layer-cake 用の薄い wrapper
lemma count_vp_ge_for_layercake
    (p X k : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) :
    ((Finset.Icc 0 X).filter (fun n => p^(k+2) ∣ (2*n+1))).card
      ≤ (X + 1) / p^(k+2) + 1 := by
  simpa using count_vp_ge p (k + 2) X hp hpodd

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
              ring_nf
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

end ABC
