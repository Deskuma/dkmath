/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdDiffPow

namespace DkMath.NumberTheory.GcdDiffPow

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow

/-!
素因子補題：もし素数 p が `a - b` と `diffPowSum (a,b,d)` 両方を割るなら、かつ `gcd a b = 1` のとき p は d を割る。
これは `gcd (a-b, S_d(a,b)) | d` の核心部分となる補題である。
-/

/-- 補助補題：全ての素因子p が d を割るなら n | d -/
lemma nat_dvd_of_all_prime_factors_dvd {n d : ℕ}
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ d) : n ∣ d := by
  sorry

/-- Nat-level補題：|a-b| と |S| の自然数 gcd が d を割る。 -/
theorem gcd_natAbs_divides_d {a b : ℤ} {d : ℕ} (hd : 1 ≤ d) (hab : Int.gcd a b = 1) :
    (a - b).natAbs.gcd (diffPowSum a b d).natAbs ∣ d := by
  let g := (a - b).natAbs.gcd (diffPowSum a b d).natAbs
  let g_int_gcd := Int.gcd (a - b) (diffPowSum a b d)

  -- 補題1: g と g_int_gcd の関係
  have g_eq_natAbs : g = g_int_gcd := by
    unfold g g_int_gcd
    -- (a - b).natAbs.gcd (diffPowSum a b d).natAbs = Int.gcd (a - b) (diffPowSum a b d)
    -- Int.gcd は自動的に natAbs を計算する
    rfl

  -- 補題2: g_int_gcd は a - b と diffPowSum a b d の gcd
  have g_dvd_left : (g_int_gcd : ℤ) ∣ (a - b) := Int.gcd_dvd_left _ _
  have g_dvd_right : (g_int_gcd : ℤ) ∣ (diffPowSum a b d) := Int.gcd_dvd_right _ _

  -- 補題3: g_int_gcd の全ての素因子 p について、prime_dividing_gcd_divides_d から p | d
  have key : ∀ p : ℕ, Nat.Prime p → (p : ℤ) ∣ Int.gcd (a - b) (diffPowSum a b d) → (p : ℕ) ∣ d := by
    intro p hp_prime hp_dvd
    exact prime_dividing_gcd_divides_d hp_prime hab hp_dvd

  -- 補題4: 全ての素因子が d を割るなら、g | d
  have nat_gcd_dvd : g ∣ d := by
    rw [g_eq_natAbs]
    apply nat_dvd_of_all_prime_factors_dvd
    intro p hp_prime hp_dvd
    -- p | g_int_gcd から (p : ℤ) ∣ Int.gcd (a - b) (diffPowSum a b d) を得る
    have : (p : ℤ) ∣ Int.gcd (a - b) (diffPowSum a b d) := by
      exact_mod_cast hp_dvd
    exact key p hp_prime this

  exact nat_gcd_dvd

end DkMath.NumberTheory.GcdDiffPow
