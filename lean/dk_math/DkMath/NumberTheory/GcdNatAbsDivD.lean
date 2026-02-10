/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdLemmas

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

  -- gcd は常にpositive（ただし a=b=0の時の特例を除く、ここでは不要）
  have hg_pos : 0 < g := by
    sorry

  -- prime power版の key：p^k が g を割るなら p^k が d を割る
  have key_pow : ∀ p k : ℕ, Nat.Prime p → p^k ∣ g → p^k ∣ d := by
    intro p k hp_prime hpk_dvd_g
    -- p^k が g を割る → p^k が gcd(|a-b|, |S|) を割る
    -- gcd の性質から p^k が |a-b| と |S| 両方を割る（あるいはどちらか）
    -- ここから prime_dividing_gcd_divides_d の prime power 版を用いて p^k が d を割ることを示す
    sorry

  -- prime power 版の gcd_divides_d を使って g ∣ d を得る
  exact gcd_divides_d hg_pos key_pow

end DkMath.NumberTheory.GcdDiffPow
