/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Defs
import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdDiffPow

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
  -- by simpa [Sd, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ...
  sorry

/-! ### 2. Perfect power => valuation constraints -/

/-- 完全 d 乗なら、任意の素数 p で指数が d の倍数（Nat側） -/
lemma dvd_padicVal_of_eq_pow {t n d : ℕ} (ht : 0 < t) :
    t = n^d → ∀ p : ℕ, Nat.Prime p → d ∣ padicValNat p t := by
  -- `t = n^d` なら v_p(t) = d * v_p(n)
  -- Mathlib: padicValNat_pow などを探して使う
  sorry

/-- `t = A * B` で gcd(A,B) が小さいとき、v_p(t) を A と B に分配する雛形 -/
lemma padicVal_mul_eq_add_of_coprime {A B : ℕ} (hcop : Nat.Coprime A B) (p : ℕ) :
    padicValNat p (A * B) = padicValNat p A + padicValNat p B := by
  -- Mathlib に `padicValNat.mul` 系があるはず
  sorry

/-! ### 3. Bridge: from gcd ∣ d to "no new prime can divide both" -/

/-- gcd が d を割るなら、p ∤ d なら同時割りは起きない（NatAbs版の雛形） -/
lemma prime_not_dvd_d_of_gcd_dvd {a b : ℤ} {d : ℕ}
    (hd : 1 ≤ d) (hab : Int.gcd a b = 1)
    (p : ℕ) (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d) :
    ¬ (p ∣ (a - b).natAbs ∧ p ∣ (Sd a b d).natAbs) := by
  -- `gcd_natAbs_divides_d` を使えば、
  -- p が両方割る ⇒ p ∣ gcd ⇒ p ∣ d、なので矛盾
  sorry

/-! ### 4. Zsigmondy hook (optional) -/

/-- （もし Mathlib にあるなら）原始素因子の存在を引っ張るための “接続点” -/
lemma exists_primitive_prime_factor_hook {a b : ℕ} {d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (hd : 2 < d) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b := by
  -- ここは Mathlib の Zsigmondy / primitive prime divisor lemma があれば `exact` 一発。
  -- 無ければ後で自前実装 or 既存文献補題を移植。
  sorry

/-! ### 5. Main target skeleton: (x+u)^d - u^d is not a perfect d-th power (strategy stub) -/

/-- 目標の雛形：Body(x,u,d) は完全 d 乗にならない（d > 2） -/
theorem body_not_perfect_pow (x u : ℕ) (d : ℕ)
    (hd : 2 < d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime (x + u) u) :
    ¬ ∃ t : ℕ, 0 < t ∧ (x+u)^d - u^d = t^d := by
  -- 証明方針：
  -- (1) a:=x+u, b:=u とおき、a^d - b^d = x * Sd(a,b,d)
  -- (2) gcd(x, Sd) ∣ d を確立（既存 lemma の特化）
  -- (3) もし t^d なら、任意の q で v_q(t^d) は d の倍数
  -- (4) Zsigmondy により q ∣ a^d - b^d かつ q ∤ a-b(=x) を得る
  -- (5) したがって q ∣ Sd だが q ∤ x。さらに q ∤ d を引き出して矛盾へ（条件調整）
  sorry

end DkMath.NumberTheory.GcdNext
