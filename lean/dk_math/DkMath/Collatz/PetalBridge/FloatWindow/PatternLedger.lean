/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
import DkMath.Collatz.PetalBridge.HeightBudget

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger"

namespace DkMath.Collatz

/-- A complete exact record of one accelerated binary-width transition. -/
structure FloatStepLedger where
  widthBefore : ℕ
  upperCarry : ℕ
  height : ℕ
  widthAfter : ℕ
  residue8 : Fin 8

/-- Construct the exact one-step ledger from an odd state. -/
noncomputable def floatStepLedger (n : OddNat) : FloatStepLedger where
  widthBefore := bitWidth n.1
  upperCarry := stateUpperCarry n.1
  height := s n
  widthAfter := bitWidth (T n).1
  residue8 := ⟨n.1 % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The ledger stores the exact one-step width conservation law. -/
theorem floatStepLedger_balance (n : OddNat) :
    (floatStepLedger n).widthBefore + (floatStepLedger n).upperCarry =
      (floatStepLedger n).height + (floatStepLedger n).widthAfter := by
  exact bitWidth_add_upperCarry_eq_height_add_bitWidth_T n

/-- Every upper-width growth step lies in the mod-eight `3` or `7` channel. -/
theorem upperGrowth_implies_mod8_three_or_seven
    (n : OddNat)
    (hgrowth : bitWidth n.1 < bitWidth (T n).1) :
    n.1 % 8 = 3 ∨ n.1 % 8 = 7 := by
  have hheight : s n = 1 :=
    (bitWidth_growth_iff_carryTwo_and_heightOne n).1 hgrowth |>.2
  have hwindow : orbitWindowHeight n 0 = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT, iterateT] using hheight
  simpa [oddOrbitLabel, iterateT] using
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).1 hwindow

/-- The mod-eight `1` channel cannot increase binary width. -/
theorem bitWidth_T_not_growth_of_mod8_eq_one
    (n : OddNat) (hmod : n.1 % 8 = 1) :
    ¬ bitWidth n.1 < bitWidth (T n).1 := by
  intro hgrowth
  rcases upperGrowth_implies_mod8_three_or_seven n hgrowth with h | h <;>
    omega

/-- The mod-eight `5` channel cannot increase binary width. -/
theorem bitWidth_T_not_growth_of_mod8_eq_five
    (n : OddNat) (hmod : n.1 % 8 = 5) :
    ¬ bitWidth n.1 < bitWidth (T n).1 := by
  intro hgrowth
  rcases upperGrowth_implies_mod8_three_or_seven n hgrowth with h | h <;>
    omega

end DkMath.Collatz
