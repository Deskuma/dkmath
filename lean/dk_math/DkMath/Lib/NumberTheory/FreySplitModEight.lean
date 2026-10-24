/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyModEight

#print "file: DkMath.Lib.NumberTheory.FreySplitModEight"

/-!
# NOTE-032-005A: 7側の整数係数と分裂接錐

[DkMath.Lib] a≡7 mod8、b偶数、奇数n≥3ではbⁿ−aⁿ−1≡0 mod8である。
従って同じ整数モデルのa₂は偶数。3側のa₂奇数性と異なり、剰余接錐はz²+zとなる。
この段階は冪和方程式や素数性を使用しない一般の整数算術である。
-/
namespace DkMath.Lib.NumberTheory.FreySplitModEight

/-- [DkMath.Lib] 7≡−1 mod8の奇数乗と偶数の3乗以上の冪を比較する。 -/
theorem power_difference_mod_eight {a b : ℤ} {n : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n) (ha : a % 8 = 7) (hb : Even b) :
    (b ^ n - a ^ n - 1) % 8 = 0 := by
  have ha8 : (a : ZMod 8) = -1 := by
    have hd : (8 : ℤ) ∣ a + 1 := by omega
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a + 1) 8).mpr hd
    have he : (a : ZMod 8) + 1 = 0 := by simpa using hz
    exact eq_neg_of_add_eq_zero_left he
  have hb8 : (b : ZMod 8) ^ n = 0 := by
    obtain ⟨k, hk⟩ := hb
    have he : (b : ZMod 8) = 2 * (k : ZMod 8) := by rw [hk]; push_cast; ring
    obtain ⟨j, hj⟩ : ∃ j, n = 3 + j := ⟨n - 3, by omega⟩
    rw [he, hj, pow_add, mul_pow, show (2 : ZMod 8) ^ 3 = 0 from by decide, zero_mul, zero_mul]
  have hp : (a : ZMod 8) ^ n = -1 := by rw [ha8, hn.neg_one_pow]
  have hz : ((b ^ n - a ^ n - 1 : ℤ) : ZMod 8) = 0 := by
    push_cast
    rw [hb8, hp]
    ring
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz)

/-- [DkMath.Lib] 7側の整数a₂は偶数である。整数除算の剰余も保持して証明する。 -/
theorem integral_a2_even {a b : ℤ} {n : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n) (ha : a % 8 = 7) (hb : Even b) :
    Even (FreyGapCubic.integral (a ^ n) (b ^ n)).a₂ := by
  have hm := power_difference_mod_eight hn hn3 ha hb
  change Even ((b ^ n - a ^ n - 1) / 4)
  refine ⟨(b ^ n - a ^ n - 1) / 8, ?_⟩
  omega

end DkMath.Lib.NumberTheory.FreySplitModEight
