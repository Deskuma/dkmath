/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdLemmas

namespace DkMath.NumberTheory.GcdDiffPow

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow

set_option linter.style.emptyLine false

/-!
素因子補題：もし素数 p が `a - b` と `diffPowSum (a,b,d)` 両方を割るなら、かつ `gcd a b = 1` のとき p は d を割る。
これは `gcd (a-b, S_d(a,b)) | d` の核心部分となる補題である。
-/

/-- Nat-level補題：|a-b| と |S| の自然数 gcd が d を割る。 -/
theorem gcd_natAbs_divides_d {a b : ℤ} {d : ℕ} (hab : Int.gcd a b = 1)
    (hab_ne : a ≠ b) :
    (a - b).natAbs.gcd (diffPowSum a b d).natAbs ∣ d := by
  set g := (a - b).natAbs.gcd (diffPowSum a b d).natAbs
  -- Strategy: Show that for all prime powers p^k, p^k ∣ g → p^k ∣ d
  -- Then use nat_dvd_of_all_prime_powers_dvd to conclude g ∣ d

  -- First, handle the trivial case g = 0 (impossible since a ≠ b)
  have hg_pos : 0 < g := by
    have hab_natAbs_pos : 0 < (a - b).natAbs := by
      simp [Int.natAbs_pos, sub_ne_zero, hab_ne]
    exact Nat.gcd_pos_of_pos_left _ hab_natAbs_pos

  -- Apply nat_dvd_of_all_prime_powers_dvd
  apply nat_dvd_of_all_prime_powers_dvd (hn := hg_pos)
  intro p k hp hpk

  -- Need to show: p^k ∣ d
  -- We have: p^k ∣ g = gcd(|a-b|, |S|)
  -- This means (p:ℤ)^k ∣ Int.gcd(a-b, S)
  -- Then by prime_pow_dividing_gcd_divides_d_pow, we get (p:ℤ)^k ∣ d

  -- Convert Nat.gcd to Int.gcd
  have : (p : ℤ) ^ k ∣ Int.gcd (a - b) (diffPowSum a b d) := by
    -- Use Int.gcd_eq_natAbs: Int.gcd a b = (a.natAbs.gcd b.natAbs : ℤ)
    rw [Int.gcd_eq_natAbs]
    -- Now (p:ℤ)^k ∣ (g:ℤ) because p^k ∣ g in Nat
    exact Int.natCast_dvd_natCast.mpr hpk

  -- Apply the prime power lemma
  have hpk_d_int : (p : ℤ) ^ k ∣ (d : ℤ) :=
    prime_pow_dividing_gcd_divides_d_pow hp hab this
  -- Convert back to Nat
  exact Int.natCast_dvd_natCast.mp hpk_d_int

end DkMath.NumberTheory.GcdDiffPow
