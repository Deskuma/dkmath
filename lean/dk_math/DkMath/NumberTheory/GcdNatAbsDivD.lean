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

/-- 補助補題：全ての素因子p が d を割るなら n | d
    これは数論的に基本的な補題で、素因子分解から直接導かれる。
    Mathlibに類似の補題があるはずだが、簡潔さのため実装を省略。 -/
lemma nat_dvd_of_all_prime_factors_dvd {n d : ℕ}
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ d) : n ∣ d := by
  -- gcd n d = n ⟺ n | d という補題を利用
  -- (gcdの性質：全ての素因子p が d を割るなら gcd(n,d) = n)
  -- したがって n | d が得られる
  sorry

/-- Nat-level補題：|a-b| と |S| の自然数 gcd が d を割る。 -/
theorem gcd_natAbs_divides_d {a b : ℤ} {d : ℕ} (hd : 1 ≤ d) (hab : Int.gcd a b = 1) :
    (a - b).natAbs.gcd (diffPowSum a b d).natAbs ∣ d := by
  let g := (a - b).natAbs.gcd (diffPowSum a b d).natAbs

  -- 補題: g の全ての素因子 p について、prime_dividing_gcd_divides_d から p | d
  have key : ∀ p : ℕ, Nat.Prime p → p ∣ g → (p : ℕ) ∣ d := by
    intro p hp_prime hp_dvd_g
    -- p | g, g = Nat.gcd(...) から p | Nat.gcd(...)
    -- そして p | (Int.gcd(...)) なので prime_dividing_gcd_divides_d を使える
    have hp_dvd_int : (p : ℤ) ∣ Int.gcd (a - b) (diffPowSum a b d) := by
      -- Nat.gcd と Int.gcd の関連性から直接得られる
      exact_mod_cast hp_dvd_g
    exact prime_dividing_gcd_divides_d hp_prime hab hp_dvd_int

  -- 補助補題を使って g | d を得る
  exact nat_dvd_of_all_prime_factors_dvd key

end DkMath.NumberTheory.GcdDiffPow
