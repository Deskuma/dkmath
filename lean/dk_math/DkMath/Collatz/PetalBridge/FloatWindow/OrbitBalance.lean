/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
import DkMath.Collatz.PetalBridge.TailGrammar

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance"

namespace DkMath.Collatz

/-- Accumulated own-width carry over the first `k` accelerated states. -/
noncomputable def sumUpperCarry : OddNat → ℕ → ℕ
  | _, 0 => 0
  | n, k + 1 => sumUpperCarry n k + stateUpperCarry (iterateT k n).1

/-- Number of carry-two states in the first `k` accelerated states. -/
noncomputable def orbitWindowUpperCarryCountEqTwo : OddNat → ℕ → ℕ
  | _, 0 => 0
  | n, k + 1 =>
      orbitWindowUpperCarryCountEqTwo n k +
        if stateUpperCarry (iterateT k n).1 = 2 then 1 else 0

/-- Each own-width carry contributes one, plus one more exactly at carry two. -/
theorem sumUpperCarry_eq_window_add_countCarryTwo
    (n : OddNat) (k : ℕ) :
    sumUpperCarry n k = k + orbitWindowUpperCarryCountEqTwo n k := by
  induction k with
  | zero => simp [sumUpperCarry, orbitWindowUpperCarryCountEqTwo]
  | succ k ih =>
      have hpos : 0 < (iterateT k n).1 := by
        have hodd := (iterateT k n).2
        omega
      rcases stateUpperCarry_one_or_two hpos with hc | hc
      · simp [sumUpperCarry, orbitWindowUpperCarryCountEqTwo, ih, hc]
        omega
      · simp [sumUpperCarry, orbitWindowUpperCarryCountEqTwo, ih, hc]
        omega

/--
Exact telescoping width ledger over a finite accelerated orbit window.
-/
theorem iterateT_bitWidth_add_sumS_eq_bitWidth_add_sumUpperCarry
    (n : OddNat) (k : ℕ) :
    sumS n k + bitWidth (iterateT k n).1 =
      bitWidth n.1 + sumUpperCarry n k := by
  induction k with
  | zero => simp [sumS, sumUpperCarry, iterateT]
  | succ k ih =>
      have hstep :=
        bitWidth_T_add_height_eq_bitWidth_add_upperCarry (iterateT k n)
      rw [sumS, sumUpperCarry, iterateT_succ_eq_T_iterateT]
      omega

/-- Expanded ledger with the carry-two count exposed. -/
theorem iterateT_bitWidth_add_sumS_eq_bitWidth_add_window_add_countCarryTwo
    (n : OddNat) (k : ℕ) :
    sumS n k + bitWidth (iterateT k n).1 =
      bitWidth n.1 + k + orbitWindowUpperCarryCountEqTwo n k := by
  rw [iterateT_bitWidth_add_sumS_eq_bitWidth_add_sumUpperCarry,
    sumUpperCarry_eq_window_add_countCarryTwo]
  omega

end DkMath.Collatz
