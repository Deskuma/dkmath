/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Core

#print "file: DkMath.ABC.Square"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace ABC

-- Squarefree / Squarefull の基本性質

-------------------------------------------------------------------------------
-- 目標 1：squarefree ⇒ rad n = n
-------------------------------------------------------------------------------

/-- squarefree なら指数は 0/1 だけ → rad = 本体 -/
@[simp]
lemma rad_eq_self_of_squarefree {n : ℕ} (hn0 : n ≠ 0) (hsf : squarefree n) :
  rad n = n := by
  classical
  -- n ≠ 0 なので factorization の積表示が使える
  have hfac : ∀ p ∈ n.factorization.support, n.factorization p = 1 := by
    intro p hp
    -- squarefree の iff 版で指数 ≤ 1 を得る
    have hle := (Nat.squarefree_iff_factorization_le_one hn0).mp hsf p
    have hpos : n.factorization p ≠ 0 := (Finsupp.mem_support_iff).mp hp
    have hpos' : 0 < n.factorization p := Nat.pos_of_ne_zero hpos
    have h1le : 1 ≤ n.factorization p := Nat.succ_le_of_lt hpos'
    exact Nat.le_antisymm hle h1le
  calc
    rad n = n.factorization.support.prod (fun p => p) := rfl
    _ = n.factorization.support.prod (fun p => p ^ n.factorization p) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [hfac p hp]
      simp
    _ = n := Nat.factorization_prod_pow_eq_self hn0

/-- squarefree なら指数は 0/1 だけ → rad = 本体 -/
lemma rad_eq_self_of_squarefree' {n : ℕ} (hn0 : n ≠ 0) (hsf : squarefree n) :
  rad n = n := by
  classical
  -- n = ∏ p∈supp p^(factorization n p)
  -- squarefree ⇒ ∀p∈supp, factorization n p = 1
  have hfac : ∀ p ∈ n.factorization.support, n.factorization p = 1 := by
    intro p hp
    have hle := (Nat.squarefree_iff_factorization_le_one hn0).mp hsf p
    have hpos : n.factorization p ≠ 0 := (Finsupp.mem_support_iff).mp hp
    have hpos' : 0 < n.factorization p := Nat.pos_of_ne_zero hpos
    have h1le : 1 ≤ n.factorization p := Nat.succ_le_of_lt hpos'
    exact Nat.le_antisymm hle h1le
  calc
    rad n = n.factorization.support.prod (fun p => p) := rfl
    _ = n.factorization.support.prod (fun p => p ^ n.factorization p) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [hfac p hp]
      simp
    _ = n := by
      exact Nat.factorization_prod_pow_eq_self hn0

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
  have hfac : n = n.factorization.support.prod (fun q => q ^ n.factorization q) := Eq.symm (Nat.factorization_prod_pow_eq_self hn0)
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
  have hfac : n = n.factorization.support.prod fun q => q ^ n.factorization q := Eq.symm (Nat.factorization_prod_pow_eq_self hn0)
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

/-- 補題：有限集合 s の素数の積の factorization は，各素数について指数 1 を与える -/
@[simp]
lemma factorization_prod_primes (q : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
  (s.prod (fun p => p)).factorization q = if q ∈ s then 1 else 0 := by
  classical
  induction s using Finset.induction_on
  case empty => simp [Finset.prod_empty, Nat.factorization_one]
  case insert a t ha ih =>
    -- hs : ∀ p ∈ insert a t, Nat.Prime p
    have ha_prime := hs a (Finset.mem_insert_self a t)
    have ht_primes : ∀ p ∈ t, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    let m := t.prod fun p => p
    have a_ne : a ≠ 0 := Nat.Prime.ne_zero ha_prime
    have m_ne : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero (ht_primes p hp)
    have prod_eq : (insert a t).prod (fun p : ℕ => p) = a * m := by
      rw [Finset.prod_insert ha]
    have mul_fac : ((insert a t).prod (fun p : ℕ => p)).factorization = a.factorization + m.factorization := by
      rw [prod_eq]; exact Nat.factorization_mul a_ne m_ne
    have ha_fact : a.factorization q = if a = q then 1 else 0 := by
      simp [Nat.Prime.factorization ha_prime, Finsupp.single_apply]
    have ht_fact := ih ht_primes
    have hsum : ((insert a t).prod fun p => p).factorization q = a.factorization q + m.factorization q := by
      rw [mul_fac]; rfl
    by_cases hq_a : q = a
    · -- q = a の場合：a ∉ t なので q ∉ t、右辺は 1 となる
      subst hq_a
      have q_not_in_t : q ∉ t := by intro h; exact ha h
      -- q の成分をそれぞれ 1 と 0 に評価して和を計算する
      have q_fact_one : q.factorization q = 1 := by simp [ha_fact]
      have m_fact_zero : m.factorization q = 0 := by rw [ht_fact]; simp [q_not_in_t]
      simp [hsum, q_fact_one, m_fact_zero]
    · -- q ≠ a の場合
      by_cases hq_in_t : q ∈ t
      · -- q ∈ t のとき：a の成分は 0, m の成分は 1
        have a_fact_zero : a.factorization q = 0 := by
          have : a ≠ q := fun H => hq_a H.symm
          simp [ha_fact, this]
        have m_fact_one : m.factorization q = 1 := by
          rw [ht_fact]; simp [hq_in_t]
        simp [hsum, a_fact_zero, m_fact_one, Finset.mem_insert_of_mem hq_in_t]
      · -- q ∉ t かつ q ≠ a のとき：両方 0 で右辺は 0
        have a_fact_zero : a.factorization q = 0 := by
          have : a ≠ q := fun H => hq_a H.symm
          simp [ha_fact, this]
        have m_fact_zero : m.factorization q = 0 := by
          rw [ht_fact]; simp [hq_in_t]
        have q_not_in_insert : q ∉ insert a t := by
          simp [Finset.mem_insert, hq_a, hq_in_t]
        simp [hsum, a_fact_zero, m_fact_zero, q_not_in_insert]


/-- 逆向き（参考）：rad n = n なら「平方因子は現れない」 -/
@[simp]
lemma squarefree_of_rad_eq_self {n : ℕ} (hn0 : n ≠ 0) (h : rad n = n) :
  squarefree n := by
  -- 簡潔な証明：rad n = n と仮定すると、n の因数の指数は rad の指数に等しい。
  -- rad は素因子の積なので各素因子の指数は 1 である（補題を利用）。
  change Squarefree n
  apply (Nat.squarefree_iff_factorization_le_one hn0).mpr
  intro p
  -- use rad n = n to move to factorization of rad n
  have hfac := congrArg Nat.factorization h
  -- rewrite goal n.factorization p ≤ 1 into (rad n).factorization p ≤ 1
  rw [←hfac]
  let s := n.factorization.support
  -- 展開して rad n = s.prod id が現れるようにする
  dsimp [rad] at *
  have hs : ∀ r ∈ s, Nat.Prime r := by
    intro r hr
    exact (mem_support_factorization_iff.mp hr).2.1
  have hq := factorization_prod_primes p s hs
  -- (rad n) を展開すると primeFactors の積が現れるので、対応する factorization を結びつける
  have hrad_eq : (∏ p ∈ n.primeFactors, p).factorization p = (s.prod fun p => p).factorization p := by rfl
  have hval := Eq.trans hrad_eq hq
  rw [hval]
  by_cases hp : p ∈ s
  · simp [hp]
  · simp [hp]

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
-- 目標 3：冪乗の安定性 rad (n^k) = rad n（k>0）
-------------------------------------------------------------------------------

/--
`rad_pow_eq_rad` は，非負整数 `n` と正の整数 `k` に対して
`rad (n ^ k) = rad n` が成り立つことを表します。

ここで `rad m` は `m` の素因数の積（平方因数を取り除いたもの，squarefree kernel）
を表します．直感的には、正の冪乗は新たな素因数を導入しないため，
`n` と `n ^ k` は同じ素因数集合を持ち，従ってその radical も等しくなります。

引数:
- `n` : 基数となる自然数
- `k` : 指数（仮定 `hk : 0 < k` により正である）
- `hk` : `k > 0` の証明

この補題は，素因数集合が冪乗によって変わらないこと（および `rad` の定義）
を使って簡単に示せます．
-/
@[simp]
lemma rad_pow_eq_rad {n k : ℕ} (hk : 0 < k) :
  rad (n^k) = rad n := by
  classical
  -- 方針：
  --  factorization (n^k) = k • (factorization n) で support は同じ
  --  support の積は変わらないので rad も同じ
  unfold rad
  -- factorization_pow: (n^k).factorization = k • n.factorization
  have hfac : (n ^ k).factorization = k • n.factorization := by
    exact Nat.factorization_pow n k
  -- supports are equal because scalar multiplication by k>0 preserves zeros
  have hs : (n ^ k).factorization.support = n.factorization.support := by
    ext p
    -- mem_support_iff: f.support contains p ↔ f p ≠ 0
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    -- rewrite pointwise using hfac
    have hfac_p : (n ^ k).factorization p = (k • n.factorization) p := by
      exact congrArg (fun f => f p) hfac
    rw [hfac_p]
    -- for ℕ-valued finsupp, k • f p = k * f p
    have : (k • n.factorization) p = k * n.factorization p := by
      simp [Finsupp.smul_apply]
    rw [this]
    -- now k * a = 0 ↔ a = 0 because k > 0 (in ℕ)
    constructor
    · intro h
      by_contra hp0
      have : k * n.factorization p = 0 := by simp [hp0]
      -- then by mul_eq_zero, k = 0 or n.factorization p = 0; but k > 0, contradiction
      have := (Nat.mul_eq_zero.mp this).resolve_left (Nat.pos_iff_ne_zero.mp hk)
      contradiction
    · intro h
      by_contra hkp
      -- from h (n.factorization p ≠ 0) we get k * n.factorization p ≠ 0 because k ≠ 0
      have : k ≠ 0 := (Nat.pos_iff_ne_zero.mp hk)
      have := (Nat.mul_eq_zero.mp hkp).resolve_right (by exact h)
      contradiction
  -- with equal supports the prod over id is the same
  change (n ^ k).factorization.support.prod (fun p => p) = n.factorization.support.prod (fun p => p)
  rw [hs]

-------------------------------------------------------------------------------
-- 目標 4：一般積の公式（gcd を通す形）
-------------------------------------------------------------------------------

/--
rad_mul_general a b : rad (a * b) = rad a * rad b / rad (Nat.gcd a b)

Description:
The radical `rad n` is the product of the distinct prime factors of `n`. This lemma
expresses the radical of a product in terms of the radicals of the factors and the
radical of their gcd: a prime dividing both `a` and `b` would appear twice in
`rad a * rad b`, and division by `rad (gcd a b)` removes the duplicated primes.

Remarks:
- The division on the right-hand side is exact: `rad (Nat.gcd a b)` divides
  `rad a * rad b`.
- Useful for reducing statements about `rad (a * b)` to properties of `rad a`,
  `rad b`, and `rad (gcd a b)`.

日本語:
積の根(rad)は各素因子を重複なく掛け合わせたものであるため、
共通の素因子は `rad (gcd a b)` によって一度取り除かれる、という直観に基づいた等式です。

Example:
For a = 12, b = 18 one gets
`rad (12 * 18) = rad 12 * rad 18 / rad (gcd 12 18) = (2*3)*(2*3)/(2*3) = 2*3 = 6`.
-/
@[simp]
lemma rad_mul_general (a b : ℕ) :
  rad (a*b) = rad a * rad b / rad (Nat.gcd a b) := by
  classical
  -- trivial zero cases: handle a = 0 and b = 0 separately
  by_cases ha0 : a = 0
  · -- a = 0
    have rb_pos : 0 < rad b := by
      have : ∀ p ∈ b.factorization.support, 0 < p := fun p hp =>
        Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
      exact Finset.prod_pos this
    rw [ha0, zero_mul, rad_zero, Nat.gcd_zero_left, one_mul, Nat.div_self rb_pos]
  by_cases hb0 : b = 0
  · -- b = 0
    have ra_pos : 0 < rad a := by
      have : ∀ p ∈ a.factorization.support, 0 < p := fun p hp =>
        Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
      exact Finset.prod_pos this
    rw [hb0, mul_zero, rad_zero, Nat.gcd_zero_right, mul_one, Nat.div_self ra_pos]

  -- now both a and b are nonzero
  have ha_ne : a ≠ 0 := ha0
  have hb_ne : b ≠ 0 := hb0

  let sA := a.factorization.support
  let sB := b.factorization.support
  let sAB := (a*b).factorization.support
  let sG := (Nat.gcd a b).factorization.support

  -- prime-ness facts for supports
  have hsA : ∀ p ∈ sA, Nat.Prime p := by intro p hp; exact (mem_support_factorization_iff.mp hp).2.1
  have hsB : ∀ p ∈ sB, Nat.Prime p := by intro p hp; exact (mem_support_factorization_iff.mp hp).2.1
  have hsAB : ∀ p ∈ sAB, Nat.Prime p := by intro p hp; exact (mem_support_factorization_iff.mp hp).2.1
  have hsG : ∀ p ∈ sG, Nat.Prime p := by intro p hp; exact (mem_support_factorization_iff.mp hp).2.1

  -- pointwise description of factorization of each rad: indicator 1 on support, 0 otherwise
  have hA : ∀ p, (rad a).factorization p = if p ∈ sA then 1 else 0 := by
    intro p
    dsimp [rad]
    exact factorization_prod_primes p sA hsA
  have hB : ∀ p, (rad b).factorization p = if p ∈ sB then 1 else 0 := by
    intro p
    dsimp [rad]
    exact factorization_prod_primes p sB hsB
  have hAB : ∀ p, (rad (a*b)).factorization p = if p ∈ sAB then 1 else 0 := by
    intro p
    dsimp [rad]
    exact factorization_prod_primes p sAB hsAB
  have hG : ∀ p, (rad (Nat.gcd a b)).factorization p = if p ∈ sG then 1 else 0 := by
    intro p
    dsimp [rad]
    exact factorization_prod_primes p sG hsG

  -- compare finsupps pointwise
  -- show support of product is union of supports (for nonzero a,b)
  have hfac_mul : (a*b).factorization = a.factorization + b.factorization := Nat.factorization_mul ha_ne hb_ne
  have sAB_eq : sAB = sA ∪ sB := by
    ext p
    constructor
    · -- -> direction: p ∈ sAB → p ∈ sA ∪ sB
      intro hp
      rcases mem_support_factorization_iff.mp hp with ⟨_nz, pp, pd⟩
      have hdiv := (Nat.Prime.dvd_mul pp).mp pd
      rcases hdiv with pa | pb
      · exact Finset.mem_union.mpr (Or.inl (mem_support_factorization_iff.mpr ⟨ha_ne, pp, pa⟩))
      · exact Finset.mem_union.mpr (Or.inr (mem_support_factorization_iff.mpr ⟨hb_ne, pp, pb⟩))
    · -- <- direction: p ∈ sA ∪ sB → p ∈ sAB
      intro hp
      have h := Finset.mem_union.mp hp
      rcases h with hA | hB
      · rcases mem_support_factorization_iff.mp hA with ⟨_, ppA, pdiva⟩
        have pd : p ∣ a * b := dvd_mul_of_dvd_left pdiva b
        exact mem_support_factorization_iff.mpr ⟨mul_ne_zero ha_ne hb_ne, ppA, pd⟩
      · rcases mem_support_factorization_iff.mp hB with ⟨_, ppB, pdivb⟩
        have pd : p ∣ a * b := dvd_mul_of_dvd_right pdivb a
        exact mem_support_factorization_iff.mpr ⟨mul_ne_zero ha_ne hb_ne, ppB, pd⟩

  -- support of gcd is intersection of supports (gcd ≠ 0 since a,b ≠ 0)
  have gcd_ne0 : Nat.gcd a b ≠ 0 := by
    intro H
    -- Nat.gcd a b = 0 ならば a = 0 かつ b = 0 である
    have ha_zero : a = 0 := Nat.eq_zero_of_gcd_eq_zero_left H
    exact ha_ne ha_zero
  have sG_eq : sG = sA ∩ sB := by
    ext p
    constructor
    · intro hp
      rcases mem_support_factorization_iff.mp hp with ⟨_nz, pp, pd⟩
      -- p ∣ gcd a b implies p ∣ a and p ∣ b via transitivity with Nat.gcd_dvd_left/right
      have pdiva : p ∣ a := dvd_trans pd (Nat.gcd_dvd_left a b)
      have pdivb : p ∣ b := dvd_trans pd (Nat.gcd_dvd_right a b)
      exact Finset.mem_inter.mpr ⟨mem_support_factorization_iff.mpr ⟨ha_ne, pp, pdiva⟩, mem_support_factorization_iff.mpr ⟨hb_ne, pp, pdivb⟩⟩
    · intro h
      rcases Finset.mem_inter.mp h with ⟨ha, hb⟩
      rcases mem_support_factorization_iff.mp ha with ⟨_, ppA, pdiva⟩
      rcases mem_support_factorization_iff.mp hb with ⟨_, _ppB, pdivb⟩
      have pd : p ∣ Nat.gcd a b := Nat.dvd_gcd pdiva pdivb
      exact mem_support_factorization_iff.mpr ⟨gcd_ne0, ppA, pd⟩

  -- now prove the finsupp equality pointwise using divisibility indicators
  have hsum : (rad a).factorization + (rad b).factorization = (rad (a*b)).factorization + (rad (Nat.gcd a b)).factorization := by
    ext p
    have A := hA p
    have B := hB p
    have AB := hAB p
    have G := hG p
    by_cases pprime : Nat.Prime p
    · -- if p is prime, membership in supports is equivalent to divisibility
      have memA_iff : p ∈ sA ↔ p ∣ a := by
        constructor
        · intro h; rcases mem_support_factorization_iff.mp h with ⟨_, _, pd⟩; exact pd
        · intro pd; exact mem_support_factorization_iff.mpr ⟨ha_ne, pprime, pd⟩
      have memB_iff : p ∈ sB ↔ p ∣ b := by
        constructor
        · intro h; rcases mem_support_factorization_iff.mp h with ⟨_, _, pd⟩; exact pd
        · intro pd; exact mem_support_factorization_iff.mpr ⟨hb_ne, pprime, pd⟩
      have memAB_iff : p ∈ sAB ↔ p ∣ a * b := by
        constructor
        · intro h; rcases mem_support_factorization_iff.mp h with ⟨_, _, pd⟩; exact pd
        · intro pd; exact mem_support_factorization_iff.mpr ⟨mul_ne_zero ha_ne hb_ne, pprime, pd⟩
      have memG_iff : p ∈ sG ↔ p ∣ Nat.gcd a b := by
        constructor
        · intro h; rcases mem_support_factorization_iff.mp h with ⟨_, _, pd⟩; exact pd
        · intro pd; exact mem_support_factorization_iff.mpr ⟨gcd_ne0, pprime, pd⟩
      -- rewrite the indicator ifs to divisibility and finish by case analysis on divisibility
      rw [Finsupp.add_apply, Finsupp.add_apply, A, B, AB, G]
      simp only [memA_iff, memB_iff, memAB_iff, memG_iff]
      by_cases pa : p ∣ a
      · by_cases pb : p ∣ b
        · -- pa, pb true
          have pab := dvd_mul_of_dvd_left pa b
          have pg := Nat.dvd_gcd pa pb
          simp [pa, pb, pab, pg]
        · -- pa true, pb false
          have pab := dvd_mul_of_dvd_left pa b
          have pg : ¬ p ∣ Nat.gcd a b := by
            rw [Nat.dvd_gcd_iff]
            intro h
            exact pb h.right
          simp [pa, pb, pab, pg]
      · by_cases pb : p ∣ b
        · -- pa false, pb true
          have pab := dvd_mul_of_dvd_right pb a
          have pg : ¬ p ∣ Nat.gcd a b := by
            rw [Nat.dvd_gcd_iff]
            intro h
            exact pa h.left
          simp [pa, pb, pab, pg]
        · -- pa false, pb false
          have pab : ¬ p ∣ a * b := by
            intro h
            rw [Nat.Prime.dvd_mul pprime] at h
            cases h
            case inl ha =>
              exact pa ha
            case inr hb =>
              exact pb hb
          have pg : ¬ p ∣ Nat.gcd a b := by
            rw [Nat.dvd_gcd_iff]
            intro h
            exact pa h.left
          simp [pa, pb, pab, pg]
    · -- if p is not prime then it cannot be in any support (supports contain only primes)
      have nA : ¬ p ∈ sA := by intro h; rcases mem_support_factorization_iff.mp h with ⟨_, pp, _⟩; exact pprime pp
      have nB : ¬ p ∈ sB := by intro h; rcases mem_support_factorization_iff.mp h with ⟨_, pp, _⟩; exact pprime pp
      have nAB : ¬ p ∈ sAB := by intro h; rcases mem_support_factorization_iff.mp h with ⟨_, pp, _⟩; exact pprime pp
      have nG : ¬ p ∈ sG := by intro h; rcases mem_support_factorization_iff.mp h with ⟨_, pp, _⟩; exact pprime pp
      simp [A, B, AB, G, nA, nB, nAB, nG]

  -- use factorization_mul to move from finsupp equality to numeric equality
  have rad_a_pos : 0 < rad a := by
    have : ∀ p ∈ sA, 0 < p := fun p hp => Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
    exact Finset.prod_pos this
  have rad_b_pos : 0 < rad b := by
    have : ∀ p ∈ sB, 0 < p := fun p hp => Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
    exact Finset.prod_pos this
  have rad_ab_pos : 0 < rad (a*b) := by
    have : ∀ p ∈ sAB, 0 < p := fun p hp => Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
    exact Finset.prod_pos this
  have rad_g_pos : 0 < rad (Nat.gcd a b) := by
    have : ∀ p ∈ sG, 0 < p := fun p hp => Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
    exact Finset.prod_pos this

  have Lfac := Nat.factorization_mul (Nat.pos_iff_ne_zero.mp rad_a_pos) (Nat.pos_iff_ne_zero.mp rad_b_pos)
  have Rfac := Nat.factorization_mul (Nat.pos_iff_ne_zero.mp rad_ab_pos) (Nat.pos_iff_ne_zero.mp rad_g_pos)

  have fac_eq : (rad a * rad b).factorization = (rad (a*b) * rad (Nat.gcd a b)).factorization := by
    calc
      (rad a * rad b).factorization = (rad a).factorization + (rad b).factorization := Lfac
      _ = (rad (a*b)).factorization + (rad (Nat.gcd a b)).factorization := by simpa using hsum
      _ = (rad (a*b) * rad (Nat.gcd a b)).factorization := (Rfac).symm

  -- reconstruct numbers from factorization equality
  have lhs_prod := Nat.factorization_prod_pow_eq_self (Nat.pos_iff_ne_zero.mp (Nat.mul_pos rad_a_pos rad_b_pos))
  have rhs_prod := Nat.factorization_prod_pow_eq_self (Nat.pos_iff_ne_zero.mp (Nat.mul_pos rad_ab_pos rad_g_pos))
  have final_eq : rad a * rad b = rad (a*b) * rad (Nat.gcd a b) := by
    calc
      rad a * rad b = (rad a * rad b).factorization.support.prod fun p => p ^ ( (rad a * rad b).factorization p) := lhs_prod.symm
      _ = (rad (a*b) * rad (Nat.gcd a b)).factorization.support.prod fun p => p ^ ((rad (a*b) * rad (Nat.gcd a b)).factorization p) := by
        rw [fac_eq]
      _ = rad (a*b) * rad (Nat.gcd a b) := rhs_prod

  -- divide both sides by rad (gcd a b) (>0)
  -- final_eq : rad a * rad b = rad (a * b) * rad (Nat.gcd a b)
  -- 目的は rad (a * b) = rad a * rad b / rad (Nat.gcd a b) じゃ
  have : rad (a * b) = rad a * rad b / rad (Nat.gcd a b) :=
    (Nat.div_eq_of_eq_mul_left rad_g_pos (by simpa [mul_comm] using final_eq)).symm
  exact this

/-- 互いに素なら即ち gcd=1 なので一般公式→完全乗法性 -/
@[simp]
lemma rad_mul_coprime' {a b : ℕ} (h : Nat.Coprime a b) :
  rad (a * b) = rad a * rad b := by
  classical
  -- extract gcd = 1 from coprimality and rewrite the general formula,
  -- then simplify rad 1 and division by 1.
  have hg := Nat.coprime_iff_gcd_eq_one.mp h
  rw [rad_mul_general a b, hg, rad_one, Nat.div_one]

-------------------------------------------------------------------------------
-- 目標 5：隣接積と squarefree の相性（ABC 文脈で多用）
-------------------------------------------------------------------------------
/--
For a nonzero natural number `n` we have `1 ≤ rad n`.

Here `rad n` denotes the radical of `n`, i.e. the product of the distinct prime
factors of `n`. In particular `rad 1 = 1`, and for `n > 1` the radical is at
least `2`, so in every case with `n ≠ 0` we obtain the uniform lower bound
`1 ≤ rad n`.

This simple bound is convenient as a base case when comparing `rad n` with
other nonnegative quantities.
-/
@[simp]
lemma abc_one_le_rad {n : ℕ} (hn : n ≠ 0) : 1 ≤ rad n := by
  -- For n = 1 the result is trivial. Otherwise take a prime p dividing n and note p ∣ rad n.
  by_cases h1 : n = 1
  · -- n = 1
    subst h1
    simp only [ne_eq, one_ne_zero, not_false_eq_true, isUnit_iff_eq_one, IsUnit.squarefree,
      rad_eq_self_of_squarefree, le_refl]
  · -- n ≠ 1, so obtain a prime divisor p of n
    have hne1 : n ≠ 1 := h1
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne1
    -- p > 0 and p divides rad n because p ∈ n.factorization.support
    have hp_pos : 0 < p := Nat.pos_of_ne_zero (Nat.Prime.ne_zero hp_prime)
    have hmem : p ∈ n.factorization.support := by
      rw [ABC.mem_support_factorization_iff]
      exact ⟨hn, hp_prime, hp_dvd⟩
    have hpd : p ∣ rad n := Finset.dvd_prod_of_mem (fun q => q) hmem
    -- show rad n > 0 to use Nat.le_of_dvd
    have rad_pos_n : 0 < rad n := by
      apply Finset.prod_pos
      intro q hq
      rcases ABC.mem_support_factorization_iff.mp hq with ⟨_, hq_prime, _⟩
      exact Nat.pos_of_ne_zero (Nat.Prime.ne_zero hq_prime)
    -- now 1 ≤ p ≤ rad n, so 1 ≤ rad n
    have h1p : 1 ≤ p := Nat.Prime.one_le hp_prime
    exact Nat.le_trans h1p (Nat.le_of_dvd rad_pos_n hpd)

/-- rad は正であることが n > 0 から従う -/
@[simp]
lemma rad_pos {n : ℕ} (hn : 0 < n) : 0 < rad n := by
  -- rad が 1 以上であることを示す補題を利用する（Mathlib に one_le_rad がある想定）
  have : 1 ≤ rad n := abc_one_le_rad (Nat.ne_of_gt hn)
  exact Nat.zero_lt_one.trans_le this

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

end ABC
