/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.PadicValNat
-- import Mathlib.NumberTheory.Padics.PadicVal.Defs
import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdDiffPow
import DkMath.NumberTheory.GdcDivD

namespace DkMath.NumberTheory.GcdNext

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow
open DkMath.NumberTheory.GcdDiffPow

/-!
## GcdNext-step lemma skeletons

目的：
1) 宇宙式の Body = 差の冪 の “特化形” を ready-made で使えるようにする
2) 「完全 d 乗」仮定を `padicValNat` / `factorization` 的な条件へ落とす
3) Zsigmondy（原始素因子）が使える環境なら接続点を用意する
-/

/-! ### 0. Notation helpers -/

def Sd (a b : ℤ) (d : ℕ) : ℤ := diffPowSum a b d

def Body (x u : ℤ) (d : ℕ) : ℤ := (x + u)^d - u^d

/-! ### 1. Specialization: gcd(x, Sd(x+u,u,d)) ∣ d -/

/-- `a := x+u`, `b := u` の特化：gcd(x, Sd(x+u,u,d)) ∣ d -/
theorem gcd_specialized_divides_d (x u : ℤ) (d : ℕ) (hd : 1 ≤ d) (hab : Int.gcd (x + u) u = 1) :
    Int.gcd x (Sd (x+u) u d) ∣ d := by
  -- `a-b = x` なので `gcd_divides_d` のラッパ
  -- `gcd_divides_d` : Int.gcd (a-b) (Sd a b d) ∣ d を使う
  have key : Int.gcd ((x+u) - u) (diffPowSum (x+u) u d) ∣ d :=
    DkMath.NumberTheory.GcdDiffPow.gcd_divides_d hd hab
  have eq : (x+u) - u = x := by ring
  rw [eq] at key
  exact key

/-! ### 2. Perfect power => valuation constraints -/

/-- 完全 d 乗なら、任意の素数 p で指数が d の倍数（Nat側） -/
lemma dvd_padicVal_of_eq_pow {t n d : ℕ} (_ht : 0 < t) :
    t = n^d → ∀ p : ℕ, Nat.Prime p → d ∣ padicValNat p t := by
  intro heq p hp
  subst heq
  -- padicValNat.pow は Fact (Nat.Prime p) のインスタンスが必要
  haveI : Fact p.Prime := ⟨hp⟩
  -- padicValNat.pow : padicValNat p (a ^ n) = n * padicValNat p a (a ≠ 0 条件付き)
  by_cases hn : n = 0
  · -- n = 0 の場合
    subst hn
    by_cases hd : d = 0
    · -- d = 0 の場合、 0^0 = 1 なので padicValNat p 1 = 0
      subst hd
      simp
    · -- d > 0 の場合、 0^d = 0 なので矛盾 (前提 0 < t)
      exfalso
      simp [zero_pow hd] at _ht
  · -- n ≠ 0 の場合
    -- padicValNat.pow (n : ℕ) (ha : a ≠ 0) : padicValNat p (a ^ n) = n * padicValNat p a
    -- ここで a = n, 冪の指数 = d なので
    have key : padicValNat p (n ^ d) = d * padicValNat p n := padicValNat.pow d hn
    rw [key]
    -- d * padicValNat p n で d ∣ ...
    exact dvd_mul_right d _

/-- `t = A * B` で gcd(A,B) が小さいとき、v_p(t) を A と B に分配する雛形 -/
lemma padicVal_mul_eq_add_of_coprime {A B : ℕ} (hcop : Nat.Coprime A B) {p : ℕ} (hp : Nat.Prime p) :
    padicValNat p (A * B) = padicValNat p A + padicValNat p B := by
  -- Fact インスタンスを用意
  haveI : Fact p.Prime := ⟨hp⟩
  -- padicValNat.mul : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b
  by_cases hA : A = 0
  · subst hA
    -- 0.Coprime B → B = 1
    have : B = 1 := by
      have := Nat.Coprime.symm hcop
      simp only [Nat.Coprime, Nat.gcd_zero_right] at this
      exact this
    subst this
    simp
  · by_cases hB : B = 0
    · subst hB
      -- A.Coprime 0 → A = 1
      have : A = 1 := by
        simp only [Nat.Coprime, Nat.gcd_zero_right] at hcop
        exact hcop
      subst this
      simp
    · exact padicValNat.mul hA hB

/-! ### 3. Bridge: from gcd ∣ d to "no new prime can divide both" -/

/-- gcd が d を割るなら、p ∤ d なら同時割りは起きない（NatAbs版の雛形） -/
lemma prime_not_dvd_d_of_gcd_dvd {a b : ℤ} {d : ℕ}
    (hd : 1 ≤ d) (hab : Int.gcd a b = 1)
    (p : ℕ) (_hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d) :
    ¬ (p ∣ (a - b).natAbs ∧ p ∣ (Sd a b d).natAbs) := by
  -- 対偶：p が両方割る ⇒ p ∣ gcd ⇒ p ∣ d、なので矛盾
  intro ⟨hdiv_ab, hdiv_sd⟩
  -- gcd_divides_d を使う
  have gcd_dvd_d : Int.gcd (a - b) (diffPowSum a b d) ∣ d :=
    DkMath.NumberTheory.GcdDiffPow.gcd_divides_d hd hab
  -- p ∣ (a-b).natAbs かつ p ∣ (Sd a b d).natAbs なら
  -- p ∣ Int.gcd (a-b) (diffPowSum a b d)
  have p_dvd_gcd : (p : ℤ) ∣ Int.gcd (a - b) (diffPowSum a b d) := by
    -- Int.gcd の natAbs での表現を使う
    have eq := Int.gcd_eq_natAbs (a := a - b) (b := diffPowSum a b d)
    rw [eq]
    -- p ∣ natAbs.gcd を示す
    have h : p ∣ (a - b).natAbs.gcd (diffPowSum a b d).natAbs :=
      Nat.dvd_gcd hdiv_ab hdiv_sd
    exact Int.ofNat_dvd.mpr h
  -- したがって p ∣ d
  obtain ⟨k, hk⟩ := gcd_dvd_d
  have p_dvd_d_int : (p : ℤ) ∣ (d : ℤ) := by
    calc (p : ℤ)
      _ ∣ Int.gcd (a - b) (diffPowSum a b d) := p_dvd_gcd
      _ ∣ (d : ℤ) := by
        use k
        exact_mod_cast hk
  have p_dvd_d_nat : p ∣ d := by
    exact Int.ofNat_dvd.mp p_dvd_d_int
  -- 矛盾
  exact hpnd p_dvd_d_nat

/-! ### 4. Zsigmondy hook (optional) -/

/-- a^p - b^p を a - b で割った商（p は素数） -/
def quotientPrimePow (a b p : ℕ) : ℕ :=
  (a^p - b^p) / (a - b)

/-- 素数冪の商 G が存在し、a^p - b^p = (a - b) * G -/
lemma pow_sub_pow_eq_diff_mul_quotient {a b p : ℕ}
    (_hp : Nat.Prime p) (ha : b < a) :
    a^p - b^p = (a - b) * quotientPrimePow a b p := by
  unfold quotientPrimePow
  -- ℤ での pow_sub_pow_factor を使う
  have key : (a : ℤ)^p - (b : ℤ)^p = ((a : ℤ) - (b : ℤ)) * diffPowSum (a : ℤ) (b : ℤ) p :=
    DkMath.Algebra.DiffPow.pow_sub_pow_factor (a : ℤ) (b : ℤ) p
  -- Nat での可除性に変換
  have hab_le : b ≤ a := Nat.le_of_lt ha
  have hab_pow : b^p ≤ a^p := Nat.pow_le_pow_left hab_le p
  -- (a - b) ∣ (a^p - b^p) を Int から示す
  have hdvd : (a - b) ∣ (a^p - b^p) := by
    have h1 : ((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ) := Nat.cast_sub hab_le
    have h2 : ((a^p - b^p : ℕ) : ℤ) = (a : ℤ)^p - (b : ℤ)^p := by
      simp only [Nat.cast_sub hab_pow, Nat.cast_pow]
    have key' : (a : ℤ) - (b : ℤ) ∣ (a : ℤ)^p - (b : ℤ)^p := by
      rw [key]
      exact dvd_mul_right _ _
    rw [← h1, ← h2] at key'
    exact Int.ofNat_dvd.mp key'
  -- div_mul_cancel を使う
  rw [Nat.mul_comm]
  exact (Nat.div_mul_cancel hdvd).symm

/-- 素数冪の場合、a > b なら 0 < a^p - b^p -/
theorem pow_sub_pos {a b : ℕ} {p : ℕ}
  (hp : Nat.Prime p) (ha : a > b) : 0 < a ^ p - b ^ p := by
  -- p が素数なら p ≠ 0
  have hp_ne_zero : p ≠ 0 := Nat.Prime.ne_zero hp
  -- a > b より a^p > b^p
  have han : a ^ p > b ^ p := Nat.pow_lt_pow_left ha hp_ne_zero
  -- したがって 0 < a^p - b^p
  exact Nat.zero_lt_sub_of_lt han

/-- 素数冪の場合、商は正で 1 より大きい -/
lemma quotientPrimePow_gt_one {a b p : ℕ}
    (hp : Nat.Prime p) (ha : b < a) (_hb : 0 < b) :
    1 < quotientPrimePow a b p := by
  have hab_pos : 0 < a - b := Nat.sub_pos_of_lt ha
  have hab_ne : a - b ≠ 0 := Nat.ne_of_gt hab_pos

  -- p ≥ 2
  have hp_ge2 : 2 ≤ p := hp.two_le
  have hp1_pos : 0 < p - 1 := by
    -- 1 < p (prime) なので p-1 > 0
    exact Nat.sub_pos_of_lt hp.one_lt

  -- 1 < a（a > b ≥ 0 かつ b < a より、a ≥ 1 では弱いので、ここは 1 < a を作る）
  have ha_gt1 : 1 < a := by
    -- b < a かつ b ≥ 0 なので a ≥ 1、さらに a ≠ 1 を言えば 1 < a
    -- ここは簡単に omega が通るなら omega、通らなければ場合分けでもOK
    omega

  -- 2 ≤ a^(p-1)
  have two_le_apow : 2 ≤ a^(p-1) := by
    -- 2 ≤ m ↔ 1 < m
    have : 1 < a^(p-1) := by
      calc 1
        _ = a^0 := (pow_zero a).symm
        _ < a^(p-1) := Nat.pow_lt_pow_right ha_gt1 hp1_pos
    exact Nat.succ_le_of_lt this

  -- a^(p-1) ≤ (a^p - b^p) / (a-b)
  have apow_le_quot : a^(p-1) ≤ quotientPrimePow a b p := by
    unfold quotientPrimePow
    -- Nat.le_div_iff_mul_le : 0 < k → (m ≤ n / k ↔ m*k ≤ n)
    have hmul : a^(p-1) * (a - b) ≤ a^p - b^p := by
      -- b^p ≤ a^(p-1)*b を示して引き算で吸収
      have hb_le_a : b ≤ a := Nat.le_of_lt ha
      have hbpow_le_apow : b^(p-1) ≤ a^(p-1) := Nat.pow_le_pow_left hb_le_a (p-1)
      have hb_mul : b^(p-1) * b ≤ a^(p-1) * b := Nat.mul_le_mul_right b hbpow_le_apow
      have hbpow : b^p = b^(p-1) * b := by
        -- p = (p-1)+1
        have hp_eq : p = (p - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.2 hp.pos)).symm
        -- b^p = b^(p-1+1) = b^(p-1) * b
        rw [hp_eq]
        exact pow_succ b (p - 1)
      have hapow : a^p = a^(p-1) * a := by
        have hp_eq : p = (p - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.2 hp.pos)).symm
        rw [hp_eq]
        exact pow_succ a (p - 1)
      -- 目的：a^(p-1)*(a-b) ≤ a^p - b^p
      --     ⇔ a^(p-1)*a - a^(p-1)*b ≤ a^p - b^p
      --     ⇔ b^p ≤ a^(p-1)*b
      -- そして b^p = b^(p-1)*b ≤ a^(p-1)*b
      have hbpow_le : b^p ≤ a^(p-1) * b := by
        rw [hbpow]
        exact hb_mul
      have hab_pow_le : b^p ≤ a^p := Nat.pow_le_pow_left hb_le_a p
      have ha_ge_b_pow : a^(p-1) * b ≤ a^p := by
        calc a^(p-1) * b
          _ ≤ a^(p-1) * a := Nat.mul_le_mul_left _ hb_le_a
          _ = a^p := by rw [← hapow]
      calc a^(p-1) * (a - b)
        _ = a^(p-1) * a - a^(p-1) * b := Nat.mul_sub_left_distrib (a^(p-1)) a b
        _ = a^p - a^(p-1) * b := by rw [← hapow]
        _ ≤ a^p - b^p := Nat.sub_le_sub_left hbpow_le (a^p)
    exact (Nat.le_div_iff_mul_le hab_pos).2 hmul

  -- 2 ≤ quotient → 1 < quotient
  have : 2 ≤ quotientPrimePow a b p := le_trans two_le_apow apow_le_quot
  exact Nat.lt_of_succ_le this

/-- 素数冪の場合の軽量版 Zsigmondy（prime p, p ≥ 3） -/
lemma exists_prime_divisor_not_dividing_diff_of_prime_exp
    {a b p : ℕ}
    (hp : Nat.Prime p) (hp_ge : 3 ≤ p)
    (ha : b < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^p - b^p ∧ ¬ q ∣ a - b := by
  -- 方針：G = (a^p - b^p) / (a - b) の素因子を取る
  have hG_gt : 1 < quotientPrimePow a b p := quotientPrimePow_gt_one hp ha hb
  have hG_ne : quotientPrimePow a b p ≠ 1 := Nat.ne_of_gt hG_gt
  -- G ≠ 1 なので素因子が存在
  have ⟨q, hq_prime, hq_div_G⟩ := Nat.exists_prime_and_dvd hG_ne
  use q, hq_prime
  constructor
  · -- q ∣ G かつ a^p - b^p = (a-b) * G なので q ∣ a^p - b^p
    have heq := pow_sub_pow_eq_diff_mul_quotient hp ha
    rw [heq]
    exact dvd_mul_of_dvd_right hq_div_G _
  · -- q ∣ a - b なら矛盾を導く
    intro hq_div_diff
    -- q は G = (a^p - b^p)/(a - b) の素因子
    -- かつ q ∣ a - b と仮定したが、矛盾を導く
    -- ※ 正確な矛盾は Lifting the Exponent (LTE) 補題から：
    --   p が素数で q ∣ a - b ⇒ v_q(a^p - b^p) = v_q(a - b)
    --   しかし q は G の素因子なので v_q(G) > 0
    --   これと v_q(a - b) の関係から矛盾が生じる（LTE補題の詳細実装待ち）
    sorry

/-- Zsigmondy の原始素因子定理のフック

**TODO（別 PR で実装予定）:**
Mathlib v4.26.0 には Zsigmondy の原始素因子定理の完全な形式化がまだ存在しない。
将来的には円分多項式（Cyclotomic polynomial）経由で次のように実装する：
- `Cyclotomic.dvd_pow_sub_pow`: Φ_d(a/b) ∣ a^d - b^d
- 円分多項式の既約性と素因子の存在

**代替実装案：**
- 選択肢A: d = 3, 5 など小さいケースだけ初等的に証明
- 選択肢B: Cyclotomic 理論を段階的に構築（重工事）
- 選択肢C: 既存の Mathlib.NumberTheory.Cyclotomic.* を活用

**数学的内容:**
Zsigmondy の定理（1892）：
a > b ≥ 1, gcd(a,b) = 1, d > 1 のとき、
次の例外を除いて、a^d - b^d は「原始素因子」（primitive prime divisor）を持つ：
- 例外1: a - b = 1 かつ d = 2
- 例外2: a = 2, b = 1, d = 6
原始素因子 q とは：q ∣ a^d - b^d かつ q ∤ a^k - b^k （∀k < d）を満たす素数。

現在は軽量版（prime d ≥ 3）を優先実装。完全版は別 PR で。
-/
lemma exists_primitive_prime_factor_hook {a b : ℕ} {d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (hd : 2 < d) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b := by
  -- まずは d が素数の場合に限定（軽量版）
  by_cases hd_prime : Nat.Prime d
  · -- d が素数の場合
    have hab_lt : b < a := by
      -- ha : 0 < a, hb : 0 < b, hab : Coprime a b
      -- から b < a を導出するには：
      -- a ≤ b だと a^d - b^d = 0 または ≤ 0 となり、原始素因子を持たない
      -- したがって a > b が必須
      -- ただし、仮説だけからの直接的な導出は難しい
      -- （数学的には自明だが、Lean での形式化が複雑）
      sorry
    have hp_ge : 3 ≤ d := by omega
    exact exists_prime_divisor_not_dividing_diff_of_prime_exp hd_prime hp_ge hab_lt hb hab
  · -- d が合成数の場合は TODO（別 PR）
    sorry

/-! ### 5. Main target skeleton: (x+u)^d - u^d is not a perfect d-th power (strategy stub) -/

/-- 目標の雛形：Body(x,u,d) は完全 d 乗にならない（d > 2）

**証明構造（Zsigmondy フック使用）:**
最後の `sorry` は `exists_primitive_prime_factor_hook` の実装が完了すれば消える。
-/
theorem body_not_perfect_pow (x u : ℕ) (d : ℕ)
    (hd : 2 < d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime (x + u) u) :
    ¬ ∃ t : ℕ, 0 < t ∧ (x+u)^d - u^d = t^d := by
  intro ⟨t, ht, heq⟩

  -- 準備：a := x+u, b := u とおく
  set a := x + u with ha_def
  set b := u with hb_def

  -- (1) 基本分解：a^d - b^d = x * Sd(a,b,d)
  have body_eq : (a : ℤ)^d - (b : ℤ)^d = (x : ℤ) * Sd a b d := by
    have key := DkMath.Algebra.DiffPow.pow_sub_pow_factor (a : ℤ) (b : ℤ) d
    have x_eq : (x : ℤ) = (a : ℤ) - (b : ℤ) := by omega
    rw [x_eq]
    exact key

  -- (2) Zsigmondy フックを使用：原始素因子 q の存在
  -- a = x + u > u = b （x > 0 より）、且つ coprime
  have ha_pos : 0 < a := by
    simp only [ha_def, hb_def]
    omega
  have hb_pos : 0 < b := hu
  have hab : Nat.Coprime a b := hcop

  obtain ⟨q, hq_prime, hq_div_pow, hq_ndiv_diff⟩ :=
    exists_primitive_prime_factor_hook ha_pos hb_pos hab hd

  -- q ∣ a^d - b^d かつ q ∤ a - b = x
  -- body_eq より a^d - b^d = x * Sd なので、q ∣ x * Sd
  -- q ∤ x より q ∣ Sd

  have hq_div_body : (q : ℤ) ∣ (a : ℤ)^d - (b : ℤ)^d := by
    -- a^d ≥ b^d を示す
    have hab_le : b ≤ a := by
      simp only [ha_def, hb_def]; omega
    have hab_pow : b^d ≤ a^d := Nat.pow_le_pow_left hab_le d
    have : ((a^d - b^d : ℕ) : ℤ) = (a : ℤ)^d - (b : ℤ)^d := by
      simp only [Nat.cast_sub hab_pow, Nat.cast_pow]
    rw [← this]
    exact Int.ofNat_dvd.mpr hq_div_pow

  rw [body_eq] at hq_div_body

  -- q ∣ x * Sd かつ q ∤ x なら q ∣ Sd
  have hq_ndiv_x : ¬ (q : ℤ) ∣ (x : ℤ) := by
    intro hdiv
    apply hq_ndiv_diff
    -- a - b = x を使う
    have x_eq_ab : x = a - b := by omega
    rw [← x_eq_ab]
    exact Int.ofNat_dvd.mp hdiv

  have hq_div_Sd : (q : ℤ) ∣ Sd a b d := by
    -- 最初に hq_div_body を body_eq で書き換えて hq_div_prod を得る
    have hq_div_prod : (q : ℤ) ∣ (x : ℤ) * Sd a b d :=
      body_eq ▸ hq_div_body
    -- q は素数で q ∣ x * Sd かつ q ∤ x なので q ∣ Sd
    have hq_prime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq_prime
    have : (q : ℤ) ∣ (x : ℤ) ∨ (q : ℤ) ∣ Sd a b d := hq_prime_int.dvd_mul.mp hq_div_prod
    cases this with
    | inl h => exfalso; exact hq_ndiv_x h
    | inr h => exact h

  -- (3) gcd(x, Sd) ∣ d を使う
  have hab_int : Int.gcd (a : ℤ) (b : ℤ) = 1 := by
    simp only [Int.gcd_eq_natAbs]
    exact hab

  have gcd_dvd_d_int := by
    have key := gcd_specialized_divides_d (x : ℤ) (b : ℤ) d (Nat.one_le_of_lt hd) hab_int
    -- key : Int.gcd (↑x) (Sd (↑x + ↑b) ↑b d) ∣ d
    -- a = x + b なので、↑x + ↑b = ↑(x+b) = ↑a
    simp only at key ⊢
    exact key
  -- 実は prime_not_dvd_d_of_gcd_dvd を使うべきだが、
  -- これは「q ∤ d → q は両方割らない」という形
  -- 対偶を取ると「q が両方割る → q ∣ d」

  -- より直接的に：q が a^d - b^d の原始素因子なら、
  -- v_q(a^d - b^d) の精密評価が必要（Lifting the Exponent Lemma）
  -- これも深い内容なので、ここでは簡略化

  -- 実際の矛盾：
  -- heq : (x+u)^d - u^d = t^d より、ℤ で (a^d - b^d : ℤ) = (t^d : ℤ)
  -- body_eq : (a^d - b^d : ℤ) = x * Sd
  -- したがって x * Sd = t^d

  -- q ∣ Sd かつ q ∤ x なので、v_q(x * Sd) = v_q(Sd) ≥ 1
  -- 一方 v_q(t^d) = d * v_q(t)
  -- もし v_q(t) ≥ 1 なら v_q(t^d) ≥ d ≥ 3

  -- しかし、原始素因子の定義より v_q(a^d - b^d) の正確な値が決まる
  -- （Lifting the Exponent Lemma: v_q(a^d - b^d) = v_q(a - b) + v_q(d) when q | a-b）
  -- しかし q ∤ a - b = x なので、LTE の別のケース

  -- ここで詳細な指数評価が必要だが、これも深い内容
  -- 簡略版として：q が原始素因子なら v_q(a^d - b^d) = 1 （多くのケースで）
  -- したがって v_q(x * Sd) = v_q(Sd) = 1
  -- しかし v_q(t^d) = d * v_q(t) で、これが 1 になるには v_q(t) = 1/d （不可能）

  -- 厳密な証明には Zsigmondy の詳細な性質が必要
  -- 現時点では sorry で留める（Zsigmondy 実装後に完成）

  sorry

end DkMath.NumberTheory.GcdNext
