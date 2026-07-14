/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
import DkMath.Collatz.PetalBridge.DriftBudget

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge"

namespace DkMath.Collatz

/-!
# Float debt and lower-height payment

This module is the first explicit bridge between upper binary-width debt and
the existing lower Petal delayed-payment grammar.  Endpoint shifts remain
visible; no payment slot is silently counted twice.
-/

/-- Accumulated height above the mandatory one-bit payment per step. -/
noncomputable def sumExtraHeight : OddNat → ℕ → ℕ
  | _, 0 => 0
  | n, k + 1 => sumExtraHeight n k + (s (iterateT k n) - 1)

/-- Total lower height is the base layer plus accumulated extra payment. -/
theorem sumS_eq_window_add_sumExtraHeight (n : OddNat) (k : ℕ) :
    sumS n k = k + sumExtraHeight n k := by
  induction k with
  | zero => simp [sumS, sumExtraHeight]
  | succ k ih =>
      have hs := s_pos (iterateT k n)
      rw [sumS, sumExtraHeight, ih]
      omega

/--
Exact debt/payment ledger:

`final width + extra lower payment = initial width + carry-two debt`.
-/
theorem bitWidth_iterateT_add_sumExtraHeight_eq_initial_add_countCarryTwo
    (n : OddNat) (k : ℕ) :
    bitWidth (iterateT k n).1 + sumExtraHeight n k =
      bitWidth n.1 + orbitWindowUpperCarryCountEqTwo n k := by
  have hledger :=
    iterateT_bitWidth_add_sumS_eq_bitWidth_add_window_add_countCarryTwo n k
  rw [sumS_eq_window_add_sumExtraHeight] at hledger
  omega

/-- Number of strict binary-width growth events in the first `k` states. -/
noncomputable def orbitWindowWidthGrowthCount (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP fun i => decide
    (bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1)

/-- Width-growth events sourced from the `3 mod 8` channel. -/
noncomputable def orbitWindowWidthGrowthMod8EqThreeCount
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP fun i =>
    if bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1 then
      decide (oddOrbitLabel n i % 8 = 3)
    else false

/-- Width-growth events in the genuine continuing `7 mod 8` reservoir. -/
noncomputable def orbitWindowWidthGrowthMod8EqSevenCount
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP fun i =>
    if bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1 then
      decide (oddOrbitLabel n i % 8 = 7)
    else false

/-- Every growth event is exactly in the `3` or `7 mod 8` growth channel. -/
theorem orbitWindowWidthGrowthCount_eq_three_add_seven
    (n : OddNat) (k : ℕ) :
    orbitWindowWidthGrowthCount n k =
      orbitWindowWidthGrowthMod8EqThreeCount n k +
        orbitWindowWidthGrowthMod8EqSevenCount n k := by
  unfold orbitWindowWidthGrowthCount
  unfold orbitWindowWidthGrowthMod8EqThreeCount
  unfold orbitWindowWidthGrowthMod8EqSevenCount
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_append]
      have hnext : iterateT (k + 1) n = T (iterateT k n) :=
        iterateT_succ_eq_T_iterateT n k
      by_cases hgrowth :
          bitWidth (iterateT k n).1 < bitWidth (iterateT (k + 1) n).1
      · have hgrowth' :
            bitWidth (iterateT k n).1 < bitWidth (T (iterateT k n)).1 := by
          simpa [hnext] using hgrowth
        have hmod := upperGrowth_implies_mod8_three_or_seven
          (iterateT k n) hgrowth'
        change oddOrbitLabel n k % 8 = 3 ∨ oddOrbitLabel n k % 8 = 7 at hmod
        rcases hmod with hthree | hseven
        · simp [ih, hgrowth, hthree]
          omega
        · simp [ih, hgrowth, hseven]
          omega
      · simp [ih, hgrowth]

/-- A width-growth event is a carry-two, height-one event. -/
theorem orbitWidthGrowth_carryTwo_and_heightOne
    (n : OddNat) (i : ℕ)
    (hgrowth : bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1) :
    stateUpperCarry (iterateT i n).1 = 2 ∧ s (iterateT i n) = 1 := by
  rw [iterateT_succ_eq_T_iterateT] at hgrowth
  exact (bitWidth_growth_iff_carryTwo_and_heightOne (iterateT i n)).1 hgrowth

/-- Growth is either repaid at the next height or remains in the `7` channel. -/
theorem upperGrowth_delayedPayment_or_mod8Seven
    (n : OddNat)
    (hgrowth : bitWidth n.1 < bitWidth (T n).1) :
    2 ≤ s (T n) ∨ n.1 % 8 = 7 := by
  rcases upperGrowth_implies_mod8_three_or_seven n hgrowth with hthree | hseven
  · left
    have hnext := orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 0 (by
      simpa [oddOrbitLabel, iterateT] using hthree)
    simpa [orbitWindowHeight_eq_s_iterateT, iterateT_succ_eq_T_iterateT] using hnext
  · exact Or.inr hseven

/-- Growth from `3 mod 8` is bounded by existing delayed-payment receivers. -/
theorem orbitWindowWidthGrowthMod8EqThreeCount_le_tailHeightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowWidthGrowthMod8EqThreeCount n k ≤
      orbitWindowHeightCountGeTail n k 2 := by
  have hsource : orbitWindowWidthGrowthMod8EqThreeCount n k ≤
      orbitWindowResidueCountMod8EqThree n k := by
    unfold orbitWindowWidthGrowthMod8EqThreeCount
    unfold orbitWindowResidueCountMod8EqThree
    apply List.countP_mono_left
    intro i
    by_cases hgrowth :
        bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1
    <;> by_cases hthree : oddOrbitLabel n i % 8 = 3
    <;> simp [hgrowth, hthree]
  exact le_trans hsource
    (orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k)

/-- All growth is bounded by delayed receivers plus the unpaid seven reservoir. -/
theorem orbitWindowWidthGrowthCount_le_delayedReceivers_add_sevenGrowth
    (n : OddNat) (k : ℕ) :
    orbitWindowWidthGrowthCount n k ≤
      orbitWindowHeightCountGeTail n k 2 +
        orbitWindowWidthGrowthMod8EqSevenCount n k := by
  rw [orbitWindowWidthGrowthCount_eq_three_add_seven]
  exact Nat.add_le_add_right
    (orbitWindowWidthGrowthMod8EqThreeCount_le_tailHeightCountGe_two n k) _

/-- Explicit count of carry-two, height-one, `7 mod 8` unpaid events. -/
noncomputable def orbitWindowSevenCarryReservoirCount
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP fun i =>
    if stateUpperCarry (iterateT i n).1 = 2 then
      if s (iterateT i n) = 1 then
        decide (oddOrbitLabel n i % 8 = 7)
      else false
    else false

/-- The explicit Seven-Carry reservoir is exactly the seven-growth count. -/
theorem orbitWindowSevenCarryReservoirCount_eq_growthMod8SevenCount
    (n : OddNat) (k : ℕ) :
    orbitWindowSevenCarryReservoirCount n k =
      orbitWindowWidthGrowthMod8EqSevenCount n k := by
  unfold orbitWindowSevenCarryReservoirCount
  unfold orbitWindowWidthGrowthMod8EqSevenCount
  congr 1
  funext i
  have hiff := bitWidth_growth_iff_carryTwo_and_heightOne (iterateT i n)
  rw [← iterateT_succ_eq_T_iterateT n i] at hiff
  by_cases hgrowth :
      bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1
  · have hpair := hiff.1 hgrowth
    simp [hgrowth, hpair.1, hpair.2]
  · have hnotPair :
        ¬ (stateUpperCarry (iterateT i n).1 = 2 ∧
          s (iterateT i n) = 1) := by
      exact fun hp => hgrowth (hiff.2 hp)
    rcases not_and_or.mp hnotPair with hcarry | hheight
    · simp [hgrowth, hcarry]
    · simp [hgrowth, hheight]

/-!
## Pressure-bridge stopping point

The Float/Petal ledger is now exact at orbit indices: carry-two events are the
upper debt, and `s - 1` is the lower extra payment.  The existing pressure
margin, however, is indexed by a separate source-depth coordinate `r + j`.
There is currently no theorem identifying an orbit payment slot `i + 1` with
a pressure-depth slot `r + j`.  Consequently, a claim that two Float debts
collide in one `SourcePressureMarginInt` slot would silently invent an index
map and is not derivable from the current APIs.

The next bridge must explicitly provide a map from orbit indices to pressure
depths and prove that it preserves the relevant height contribution.  Only
then can payment collision be translated into margin nonpositivity or a local
pressure obstruction.  This is the genuine boundary of the present branch;
the finite debt/payment and continuing-reservoir results above require no such
unproved identification.
-/

end DkMath.Collatz
