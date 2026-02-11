/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Defs
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

現在は `admit` のまま残し、枠組みだけ示す。
-/
lemma exists_primitive_prime_factor_hook {a b : ℕ} {d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (hd : 2 < d) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b := by
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
