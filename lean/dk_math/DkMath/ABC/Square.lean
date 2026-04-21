/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Core

#print "file: DkMath.ABC.Square"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.ABC

-- Squarefree / Squarefull の基本性質

-------------------------------------------------------------------------------
-- 目標 1：squarefree / squarefull の残余補題
-------------------------------------------------------------------------------

/-- squarefree ならば、rad n は n のすべての素因子を含む -/
@[simp]
lemma rad_dvd {n : ℕ} (h : squarefree n) (p : ℕ) (hp : p.Prime) (hpd : p ∣ n) : p ∣ rad n := by
  -- squarefree ならば、rad n は n のすべての素因子を含む
  -- よって、p ∣ n ならば p ∣ rad n も成り立つ
  unfold rad
  let s := n.factorization.support
  have hsup : p ∈ s := by
    rw [mem_support_factorization_iff]
    -- n ≠ 0 は squarefree から導く：もし n = 0 なら p^2 ∣ n となり squarefree から p が可逆元になって矛盾
    have hn0 : n ≠ 0 := by
      by_contra hn
      have hpp : p * p ∣ n := by simp [hn]
      have hu := h p hpp
      -- IsUnit p を p = 1 に変換するには isUnit_iff_eq_one を使う（型を明示する）
      have hp1 : p = 1 := (isUnit_iff_eq_one : IsUnit p ↔ p = 1).mp hu
      exact (Nat.Prime.ne_one hp) hp1
    exact ⟨hn0, hp, hpd⟩
  -- support の積に p が含まれるので、rad n は p を割る
  exact Finset.dvd_prod_of_mem (fun q => q) hsup

/-- 指数が 2 以上であれば p^2 ∣ n となる補題 -/
@[simp]
lemma pow_dvd_of_factorization_ge_two {n p : ℕ} (hn0 : n ≠ 0)
  (h : 2 ≤ n.factorization p) : p ^ 2 ∣ n := by
  -- 素因数分解の積表示に書き換える
  have hfac : n = n.factorization.support.prod (fun q => q ^ n.factorization q) := Eq.symm (Nat.prod_factorization_pow_eq_self hn0)
  rw [hfac]
  -- 指数が 2 以上なら support に入る（指数 ≠ 0）
  have hmem : p ∈ n.factorization.support := by
    have hne : n.factorization p ≠ 0 := by
      intro hp0
      -- h を直接書き換えると後続で h が必要になるため、hp0 を使って 2 ≤ 0 を得て矛盾を導く
      have h2 : 2 ≤ 0 := by
        simp [hp0] at h
      exact (Nat.not_succ_le_zero 1) h2
    exact Finsupp.mem_support_iff.mpr hne
  -- support 上の積に関して p ^ (n.factorization p) が割る
  have hpn_dvd : p ^ n.factorization p ∣ n.factorization.support.prod (fun q => q ^ n.factorization q) :=
    Finset.dvd_prod_of_mem (fun q => q ^ n.factorization q) hmem
  -- 2 ≤ n.factorization p から p^2 ∣ p^(n.factorization p)
  rcases Nat.exists_eq_add_of_le h with ⟨k, hk⟩
  have h2 : p ^ 2 ∣ p ^ n.factorization p := by
    rw [hk]
    use p ^ k
    simp [pow_add]
  -- 合成して p^2 ∣ (全積) を得る
  exact dvd_trans h2 hpn_dvd

/-- サポート上で指数が 2 以上である素因子の積は元 n を割る -/
lemma square_factor_support_prod_dvd {n : ℕ} (hn0 : n ≠ 0) :
  (n.factorization.support.filter fun p => 2 ≤ n.factorization p).prod (fun p => p) ∣ n := by
  let s := n.factorization.support.filter fun p => 2 ≤ n.factorization p
  -- 展開: n = ∏_{q ∈ support} q ^ (f q)
  have hfac : n = n.factorization.support.prod fun q => q ^ n.factorization q := Eq.symm (Nat.prod_factorization_pow_eq_self hn0)
  -- 各 p ∈ s に対して p ∣ p^(n.factorization p)
  have hpoint : ∀ p ∈ s, p ∣ p ^ n.factorization p := by
    intro p hp
    -- s の定義から指数は 2 以上かつ support に含まれる
    have ⟨hmem', hge⟩ := Finset.mem_filter.1 hp
    -- p ∣ p ^ (n.factorization p)
    have hf : n.factorization p ≠ 0 := (Finsupp.mem_support_iff.mp hmem')
    have : p ∣ p ^ n.factorization p := dvd_pow_self p hf
    exact this
  -- s.prod p ∣ s.prod (fun p => p ^ n.factorization p)
  have hdiv := Finset.prod_dvd_prod_of_dvd (fun p => p) (fun p => p ^ n.factorization p) fun p hp => hpoint p hp
  -- s.prod (fun p => p ^ n.factorization p) divides n: show each p^f p divides n, then use prod_dvd_prod_of_dvd
  have hsub : s.prod (fun p => p ^ n.factorization p) ∣ n := by
    -- show s ⊆ support
    have hsubset : s ⊆ n.factorization.support := by intro x hx; exact (Finset.mem_filter.1 hx).1
    -- s.prod f divides support.prod f
    let hsub1 := Finset.prod_dvd_prod_of_subset s n.factorization.support (fun p => p ^ n.factorization p) hsubset
    -- support.prod f = n (use symmetry of hfac), so that product divides n by dvd_refl
    have hprod_eq : n.factorization.support.prod (fun q => q ^ n.factorization q) = n := Eq.symm hfac
    have hright : n.factorization.support.prod (fun q => q ^ n.factorization q) ∣ n := by
      rw [hprod_eq]
    exact dvd_trans hsub1 hright
  -- 合成して目的を得る
  exact dvd_trans hdiv hsub

/-- 数値としての上界：上の積は n を割るので n ≠ 0 のとき積 ≤ n となる -/
@[simp]
lemma square_factor_support_prod_le {n : ℕ} (hn0 : n ≠ 0) :
  (n.factorization.support.filter fun p => 2 ≤ n.factorization p).prod (fun p => p) ≤ n := by
  have hdvd := square_factor_support_prod_dvd hn0
  -- 部分積は正なので Nat.le_of_dvd を使う（0 < n）
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  exact Nat.le_of_dvd hn_pos hdvd


-------------------------------------------------------------------------------
-- 目標 2：squarefull ⇒ rad n < n（n>1）
-------------------------------------------------------------------------------
/--
n が squarefull かつ 1 < n のとき、rad n < n を示す。

ここで rad n は n の異なる素因数の積（素因数の冪を 1 にしたもの）を表し、
squarefull n は任意の素因数 p に対して p^2 が n を割り切ることを意味する。
n を素因数分解して n = ∏ p_i^{k_i} (各 k_i ≥ 2) と書くと、
rad n = ∏ p_i であり、したがって
n = rad n * ∏ p_i^{k_i - 1} ≥ rad n * ∏ p_i ≥ 2 * rad n
となる（n > 1 により少なくとも 1 個の素因数が存在し、その積は ≥ 2）。
よって rad n ≤ n/2 < n となり、要求される不等式が得られる。
-/
@[simp]
lemma rad_lt_of_squarefull {n : ℕ} (hfull : squarefull n) (h1 : 1 < n) :
  rad n < n := by
  -- Use a short contradiction: if rad n = n then n is squarefree, which contradicts squarefull
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans h1)
  have hn1 : n ≠ 1 := by linarith [h1]
  -- show rad n ≠ n
  have hne : rad n ≠ n := by
    intro heq
    -- rad n = n implies squarefree n
    have hsf := squarefree_of_rad_eq_self hn0 heq
    -- n > 1 so there is a prime p dividing n
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hn1
    -- squarefull gives p^2 ∣ n
    have hp2 := hfull p hp_prime hp_dvd
    -- squarefree expects p * p ∣ n (notation); convert and apply
    have hu := hsf p (by simpa [pow_two] using hp2)
    have hp1 := (isUnit_iff_eq_one : IsUnit p ↔ p = 1).mp hu
    exact (Nat.Prime.ne_one hp_prime) hp1
  -- rad ≤ n and rad ≠ n gives strict inequality
  exact lt_of_le_of_ne (rad_le hn0) hne

-------------------------------------------------------------------------------
-- 目標 5：隣接積と squarefree の相性（ABC 文脈で多用）
-------------------------------------------------------------------------------
/-- N と N+1 は互いに素 ⇒ 隣接積の rad は積に分解 -/
@[simp]
lemma rad_neighbors (N : ℕ) : rad (N*(N+1)) = rad N * rad (N+1) :=
  by simp only [Nat.coprime_self_add_right, Nat.coprime_one_right_eq_true, rad_mul_coprime']

/-- N が squarefree なら rad N = N -/
@[simp]
lemma rad_neighbors_simplify_left {N : ℕ} (hN0 : N ≠ 0) (hsf : squarefree N) :
  rad (N * (N+1)) = N * rad (N+1) := by simp [rad_eq_self_of_squarefree hN0 hsf]

/-- (応用例) どちらかが squarefree なら隣接積の rad に下界が立つ -/
@[simp]
lemma rad_neighbors_lower_bound {N : ℕ}
  (hN0 : N ≠ 0) (hsf : squarefree N) :
  (rad (N*(N+1))) ≥ N := by
  have h := rad_neighbors_simplify_left hN0 hsf
  have h_rad : 1 ≤ rad (N+1) := by
    -- rad は正であることが N+1 > 0 から従う（rad_pos を利用）
    have hpos : 0 < rad (N+1) := rad_pos (Nat.zero_lt_succ N)
    have hle : 1 ≤ rad (N+1) := Nat.zero_lt_one.trans_le hpos
    exact hle
  rw [h]
  -- N ≥ 0, rad(N+1) ≥ 1 より N ≤ N * rad(N+1) を直接示す
  have : N = N * 1 := by rw [mul_one]
  calc
    N = N * 1         := this
    _ ≤ N * rad (N+1) := Nat.mul_le_mul_left N h_rad

end DkMath.ABC
