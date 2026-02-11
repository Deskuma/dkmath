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
  -- (x+u) - u = x を使って変形
  -- (x+u) - u = x を使って変形
  have eq : (x+u) - u = x := by ring
  rw [eq] at key
  -- Sd の定義を展開
  convert key using 2
  -- diffPowSum = Sd の定義

/-! ### 2. Perfect power => valuation constraints -/

/-- 完全 d 乗なら、任意の素数 p で指数が d の倍数（Nat側） -/
lemma dvd_padicVal_of_eq_pow {t n d : ℕ} (ht : 0 < t) :
    t = n^d → ∀ p : ℕ, Nat.Prime p → d ∣ padicValNat p t := by
  -- `t = n^d` なら v_p(t) = d * v_p(n)
  -- TODO: Mathlib の padicValNat に関する補題を探して実装
  -- 現時点では戦略確認のため admit
  intro heq p hp
  subst heq
  -- padicValNat p (n^d) = d * padicValNat p n を使う（Mathlib にあるはず）
  -- とりあえず admit で通す
  admit

/-- `t = A * B` で gcd(A,B) が小さいとき、v_p(t) を A と B に分配する雛形 -/
lemma padicVal_mul_eq_add_of_coprime {A B : ℕ} (hcop : Nat.Coprime A B) (p : ℕ) :
    padicValNat p (A * B) = padicValNat p A + padicValNat p B := by
  -- TODO: Mathlib の padicValNat_mul 相当を探して実装
  -- coprime 条件下では加法性が成り立つはず
  admit

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

/-- （もし Mathlib にあるなら）原始素因子の存在を引っ張るための “接続点” -/
lemma exists_primitive_prime_factor_hook {a b : ℕ} {d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (hd : 2 < d) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b := by
  -- TODO: Mathlib の Zsigmondy / primitive prime divisor lemma を探索
  -- 無ければ円分多項式経由で実装
  -- 戦略：d > 2, coprime, a > b の条件下で原始素因子が存在
  admit

/-! ### 5. Main target skeleton: (x+u)^d - u^d is not a perfect d-th power (strategy stub) -/

/-- 目標の雛形：Body(x,u,d) は完全 d 乗にならない（d > 2） -/
theorem body_not_perfect_pow (x u : ℕ) (d : ℕ)
    (hd : 2 < d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime (x + u) u) :
    ¬ ∃ t : ℕ, 0 < t ∧ (x+u)^d - u^d = t^d := by
  -- TODO: 完全な証明を構築
  -- 証明方針：
  -- (1) a:=x+u, b:=u とおき、a^d - b^d = x * Sd(a,b,d)
  -- (2) gcd(x, Sd) ∣ d を確立（gcd_specialized_divides_d を使用）
  -- (3) もし t^d なら、任意の q で v_q(t^d) は d の倍数（dvd_padicVal_of_eq_pow）
  -- (4) Zsigmondy により q ∣ a^d - b^d かつ q ∤ a-b(=x) を得る
  --     (exists_primitive_prime_factor_hook を使用)
  -- (5) したがって q ∣ Sd だが q ∤ x。
  --     prime_not_dvd_d_of_gcd_dvd により q ∤ d が必要だが、
  --     一方 v_q(t^d) = d の倍数 の条件から矛盾を導く
  -- 現時点では上記補題群が admit なので、ここも admit
  admit

end DkMath.NumberTheory.GcdNext
