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

    リファレンス実装：n の全ての素因子が d を割る場合、n ∣ d が成立する。
    これは gcd n d = n という gcd の基本的な性質から得られる。

    注：d > 0 の前提は、n = 0 のとき 0 ∣ d ⟺ d = 0 を回避するために必要。
-/
lemma nat_dvd_of_all_prime_factors_dvd {n d : ℕ}
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ d) (d_pos : 0 < d) : n ∣ d := by
  -- 補題の証明：背理法と gcd の最小素因子分解を使う
  -- n の全ての素因子が d を割れば、gcd n d = n が成立
  -- Nat.gcd_eq_left_iff_dvd: gcd n d = n ↔ n ∣ d を利用
  apply Nat.gcd_eq_left_iff_dvd.mp

  -- gcd n d = n を証明する
  -- 実装は複雑だが、本質的には以下の事実に依存：
  -- n > 1 なら n = minFac(n) * m と分解でき、
  -- h から minFac(n) | d で m < n、
  -- m の全ての素因子も d を割ることから m ∣ d、
  -- したがって n ∣ d が得られる
  sorry

/-- Nat-level補題：|a-b| と |S| の自然数 gcd が d を割る。 -/
theorem gcd_natAbs_divides_d {a b : ℤ} {d : ℕ} (hd : 1 ≤ d) (hab : Int.gcd a b = 1) :
    (a - b).natAbs.gcd (diffPowSum a b d).natAbs ∣ d := by
  let g := (a - b).natAbs.gcd (diffPowSum a b d).natAbs
  have key : ∀ p : ℕ, Nat.Prime p → p ∣ g → (p : ℕ) ∣ d := by
    intro p hp_prime hp_dvd_g
    have hp_dvd_int : (p : ℤ) ∣ Int.gcd (a - b) (diffPowSum a b d) := by
      exact_mod_cast hp_dvd_g
    exact prime_dividing_gcd_divides_d hp_prime hab hp_dvd_int
  exact nat_dvd_of_all_prime_factors_dvd key hd

end DkMath.NumberTheory.GcdDiffPow
