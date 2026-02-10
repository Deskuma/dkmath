/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdLemmas
import DkMath.NumberTheory.GcdDiffPow

namespace DkMath.NumberTheory.GcdDiffPow

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow

/-!
素因子補題：もし素数 p が `a - b` と `diffPowSum (a,b,d)` 両方を割るなら、かつ `gcd a b = 1` のとき p は d を割る。
これは `gcd (a-b, S_d(a,b)) | d` の核心部分となる補題である。
-/

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
