/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.Core

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance"

namespace DkMath.Collatz

/-!
# Exact Float width balance

The upper carry and lower 2-adic height are measured in the same integer unit:
binary width.  This module proves the exact one-step conservation law.
-/

/-- Multiplication by `2^h` adds exactly `h` binary positions. -/
theorem bitWidth_pow_two_mul
    {h q : ℕ} (hq : 0 < q) :
    bitWidth (2 ^ h * q) = h + bitWidth q := by
  have hbpos : 0 < bitWidth q := by
    rw [bitWidth_eq_log_two_add_one hq.ne']
    omega
  have hloq := pow_bitWidth_sub_one_le hq
  have hhiq := lt_pow_bitWidth hq
  have hexp : h + bitWidth q - 1 = h + (bitWidth q - 1) := by omega
  have hlo : 2 ^ (h + bitWidth q - 1) ≤ 2 ^ h * q := by
    rw [hexp, pow_add]
    exact Nat.mul_le_mul_left _ hloq
  have hhi : 2 ^ h * q < 2 ^ ((h + bitWidth q - 1) + 1) := by
    have hmul : 2 ^ h * q < 2 ^ h * 2 ^ bitWidth q :=
      (Nat.mul_lt_mul_left (pow_pos (by norm_num) h)).2 hhiq
    rw [← pow_add] at hmul
    have heq : (h + bitWidth q - 1) + 1 = h + bitWidth q := by omega
    simpa [heq] using hmul
  have hwidth := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
  omega

/-- The accelerated odd state is the exact residual after removing `2^s`. -/
theorem threeNPlusOne_eq_pow_height_mul_T (n : OddNat) :
    threeNPlusOne n.1 = 2 ^ s n * (T n).1 := by
  change threeNPlusOne n.1 =
    pow2 (v2 (threeNPlusOne n.1)) *
      (threeNPlusOne n.1 / pow2 (v2 (threeNPlusOne n.1)))
  exact (Nat.mul_div_cancel'
    (by
      simpa [v2, pow2] using
        (pow_padicValNat_dvd (p := 2) (n := threeNPlusOne n.1)))).symm

/-- Accelerated odd states are positive. -/
theorem T_val_pos (n : OddNat) : 0 < (T n).1 := by
  have hodd := (T n).2
  omega

/-- Removing the 2-adic height removes exactly that many binary positions. -/
theorem bitWidth_threeNPlusOne_eq_height_add_bitWidth_T (n : OddNat) :
    bitWidth (threeNPlusOne n.1) = s n + bitWidth (T n).1 := by
  rw [threeNPlusOne_eq_pow_height_mul_T]
  exact bitWidth_pow_two_mul (T_val_pos n)

/--
Exact one-step Float accounting:

`current width + upper carry = lower height + next width`.
-/
theorem bitWidth_T_add_height_eq_bitWidth_add_upperCarry (n : OddNat) :
    s n + bitWidth (T n).1 = bitWidth n.1 + stateUpperCarry n.1 := by
  have hn : 0 < n.1 := by
    have hodd := n.2
    omega
  rw [← bitWidth_threeNPlusOne_eq_height_add_bitWidth_T]
  simpa [threeNPlusOne] using
    bitWidth_threeNPlusOne_eq_bitWidth_add_upperCarry hn

/-- Symmetric display form of the exact one-step balance. -/
theorem bitWidth_add_upperCarry_eq_height_add_bitWidth_T (n : OddNat) :
    bitWidth n.1 + stateUpperCarry n.1 = s n + bitWidth (T n).1 :=
  (bitWidth_T_add_height_eq_bitWidth_add_upperCarry n).symm

/-- Every odd Collatz state pays at least one lower binary position. -/
theorem s_pos (n : OddNat) : 0 < s n := by
  unfold s threeNPlusOne
  exact v2_3n_plus_1_ge_1 n.1 n.2

/--
Binary width grows in one accelerated step exactly in the carry-two,
height-one state.
-/
theorem bitWidth_growth_iff_carryTwo_and_heightOne (n : OddNat) :
    bitWidth n.1 < bitWidth (T n).1 ↔
      stateUpperCarry n.1 = 2 ∧ s n = 1 := by
  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry n
  have hn : 0 < n.1 := by
    have hodd := n.2
    omega
  have hcarry := stateUpperCarry_one_or_two hn
  have hheight := s_pos n
  constructor
  · intro hgrowth
    rcases hcarry with hc | hc
    · omega
    · exact ⟨hc, by omega⟩
  · rintro ⟨hc, hs⟩
    omega

/-- Height at least two prevents binary-width growth. -/
theorem bitWidth_T_le_of_two_le_height
    (n : OddNat) (hheight : 2 ≤ s n) :
    bitWidth (T n).1 ≤ bitWidth n.1 := by
  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry n
  have hn : 0 < n.1 := by
    have hodd := n.2
    omega
  have hcarry : stateUpperCarry n.1 ≤ 2 :=
    upperCarry3n1_le_two_of_lt_pow (lt_pow_bitWidth hn)
  omega

end DkMath.Collatz
