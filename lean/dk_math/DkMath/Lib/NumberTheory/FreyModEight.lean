/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Parity argument adapted from S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight.lean,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Modified: general integer inputs and odd exponents; no FreyPackage or FLT equation.
-/

import DkMath.Lib.NumberTheory.FreyGapCubic
import Mathlib.Data.ZMod.Basic

#print "file: DkMath.Lib.NumberTheory.FreyModEight"

/-!
# NOTE-032-003C: 指数を保ったmod8算術と整数モデルのa₂

[DkMath.Lib] a≡3 mod8、b偶数、奇数指数n≥3なら、bⁿ−aⁿ−1≡4 mod8となる。
従って整数モデルのa₂=(bⁿ−aⁿ−1)/4は奇数である。
冪和の方程式・原始性・素数性は要求しない。整数除算の余りを保持してから偶奇を導く。
-/
namespace DkMath.Lib.NumberTheory.FreyModEight

/-- [DkMath.Lib] 3の奇数乗と、偶数の3乗以上の冪をmod8で比較する。 -/
theorem power_difference_mod_eight {a b : ℤ} {n : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n) (ha : a % 8 = 3) (hb : Even b) :
    (b ^ n - a ^ n - 1) % 8 = 4 := by
  have ha8 : (a : ZMod 8) = 3 := by
    have hd : (8 : ℤ) ∣ a - 3 := by omega
    have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 3) 8).mpr hd
    have he : (a : ZMod 8) - 3 = 0 := by simpa using hzero
    exact sub_eq_zero.mp he
  have hb8 : (b : ZMod 8) ^ n = 0 := by
    obtain ⟨k, hk⟩ := hb
    have he : (b : ZMod 8) = 2 * (k : ZMod 8) := by rw [hk]; push_cast; ring
    obtain ⟨j, hj⟩ : ∃ j, n = 3 + j := ⟨n - 3, by omega⟩
    rw [he, hj, pow_add, mul_pow, show (2 : ZMod 8) ^ 3 = 0 from by decide, zero_mul, zero_mul]
  have ha8pow : (a : ZMod 8) ^ n = 3 := by
    obtain ⟨m, hm⟩ := hn
    rw [ha8, hm, pow_succ, pow_mul, show (3 : ZMod 8) ^ 2 = 1 from by decide, one_pow, one_mul]
  have hcast : ((b ^ n - a ^ n - 1 - 4 : ℤ) : ZMod 8) = 0 := by
    push_cast
    rw [hb8, ha8pow]
    decide
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hcast
  omega

/-- [DkMath.Lib] 正規化整数モデルのa₂の奇数性。指数は任意の奇数n≥3でよい。 -/
theorem integral_a2_odd {a b : ℤ} {n : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n) (ha : a % 8 = 3) (hb : Even b) :
    Odd (FreyGapCubic.integral (a ^ n) (b ^ n)).a₂ := by
  have hmod := power_difference_mod_eight hn hn3 ha hb
  change Odd ((b ^ n - a ^ n - 1) / 4)
  refine ⟨(b ^ n - a ^ n - 1) / 8, ?_⟩
  omega

end DkMath.Lib.NumberTheory.FreyModEight
